{-# OPTIONS --safe #-}
-- Remove an entire completed result if it covers the forgotten family.
module Muninn.SharedResultRemoval where

import Muninn.OwnedState as O
import Muninn.PrivateReceipt as Private
import Muninn.RemovalStore as Store
import Muninn.ReceiptTypes as Receipt
import Muninn.ReceiptLedger as Ledger
import Muninn.RequestIdentity as Identity
import Muninn.RequestState as RequestState
import Muninn.RequestCodecs as Codecs
import Muninn.Canonical as Canonical
import Muninn.CatalogInputs as Input
import Muninn.Worktree as Worktree
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (tt)
open import Data.List using (List; []; _∷_)
import Data.List.Relation.Unary.All as All
open All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (_×_; proj₂; _,_)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans)

module DB = O.DB

sameFamily = Canonical.compare Codecs.familyId

member : Worktree.FamilyId → List Worktree.FamilyId → Bool
member family [] = false
member family (first ∷ rest) with sameFamily family first
... | yes _ = true
... | no _ = member family rest

belongs : Worktree.FamilyId → Input.Owner → Bool
belongs family Input.installationOwner = false
belongs family (Input.repositoryOwner target) with sameFamily family target
... | yes _ = true
... | no _ = false
belongs family (Input.repositoriesOwner targets) = member family targets

requestOwner : Identity.Meaning → Maybe Input.Owner
requestOwner (Identity.mutation kind input) = RequestState.requestOwner (RequestState.userMeaning (Identity.intent kind) input)
requestOwner (Identity.durableJob job input) = RequestState.requestOwner (RequestState.jobMeaning job input)

data Decision : Set where
  keep : Decision
  compact : Input.OperationId → Decision

decide : Worktree.FamilyId → O.Record → Decision
decide family (O.recordOf owner (O.receipt (Receipt.entry id (Receipt.finished meaning names result)))) with requestOwner meaning
... | nothing = keep
... | just target with belongs family target
...   | true = compact id
...   | false = keep
decide family _ = keep

mark : Worktree.FamilyId → ℕ → DB.Transaction Bool
mark family slot = DB.scan λ world → choose (DB.lookup slot world)
  where
  choose : Maybe O.Record → DB.Transaction Bool
  choose nothing = DB.commit false
  choose (just value) with decide family value
  ... | keep = DB.commit false
  ... | compact id = DB.put slot (Ledger.markerAt id) (DB.commit true)

activeReceiptUnchanged : ∀ family slot world owner id meaning names work →
  DB.lookup slot world ≡ just (O.recordOf owner (O.receipt (Receipt.entry id (Receipt.active meaning names work)))) →
  DB.execute (mark family slot) world ≡ (false , world)
activeReceiptUnchanged family slot world owner id meaning names work found rewrite found = refl

markedReceiptIsCompact : ∀ family slot world value id → DB.lookup slot world ≡ just value →
  decide family value ≡ compact id →
  DB.execute (mark family slot) world ≡ (true , DB.write slot (Ledger.markerAt id) world)
markedReceiptIsCompact family slot world value id found selected rewrite found | selected = refl

otherSlotPreserved : ∀ family slot other world → ¬ (slot ≡ other) →
  DB.lookup other (proj₂ (DB.execute (mark family slot) world)) ≡ DB.lookup other world
otherSlotPreserved family slot other world different with DB.lookup slot world
... | nothing = refl
... | just value with decide family value
...   | keep = refl
...   | compact id = DB.writePreservesOther slot other (Ledger.markerAt id) world different

retryMarker : ∀ family slot world id →
  DB.execute (mark family slot) (DB.write slot (Ledger.markerAt id) world) ≡
    (false , DB.write slot (Ledger.markerAt id) world)
retryMarker family slot world id rewrite DB.writeVisible slot (Ledger.markerAt id) world = refl

-- A multi-repository owner makes the complete saved result subject to removal
-- when any one of its recorded families is forgotten.
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥-elim)

memberIncluded : ∀ family targets → family ∈ targets → member family targets ≡ true
memberIncluded family (first ∷ rest) (here refl) with sameFamily family family
... | yes _ = refl
... | no different = ⊥-elim (different refl)
memberIncluded family (first ∷ rest) (there included) with sameFamily family first
... | yes _ = refl
... | no _ = memberIncluded family rest included

sharedResultSelected : ∀ family owner id meaning names result targets →
  requestOwner meaning ≡ just (Input.repositoriesOwner targets) → family ∈ targets →
  decide family (O.recordOf owner (O.receipt (Receipt.entry id (Receipt.finished meaning names result)))) ≡ compact id
sharedResultSelected family owner id meaning names result targets saved included rewrite saved | memberIncluded family targets included = refl

-- Each lookup is made inside the same transaction as its replacement.
compile : ∀ {A : Set} → Worktree.FamilyId → O.World → DB.Transaction A → DB.Transaction A
compile family [] next = next
compile {A} family ((slot , value) ∷ rest) next = DB.read slot choose
  where
  choose : Maybe O.Record → DB.Transaction A
  choose nothing = compile family rest next
  choose (just current) with decide family current
  ... | keep = compile family rest next
  ... | compact id = DB.put slot (Ledger.markerAt id) (compile family rest next)

run : Worktree.FamilyId → O.World → O.World → O.World
run family [] world = world
run family ((slot , value) ∷ rest) world with DB.lookup slot world
... | nothing = run family rest world
... | just current with decide family current
...   | keep = run family rest world
...   | compact id = run family rest (DB.write slot (Ledger.markerAt id) world)

compiled : ∀ {A} family rows (next : DB.Transaction A) world →
  DB.evaluate (compile family rows next) world ≡ DB.evaluate next (run family rows world)
compiled family [] next world = refl
compiled family ((slot , value) ∷ rest) next world with DB.lookup slot world
... | nothing = compiled family rest next world
... | just current with decide family current
...   | keep = compiled family rest next world
...   | compact id = compiled family rest next (DB.write slot (Ledger.markerAt id) world)

selectedPrivate : ∀ family value id → decide family value ≡ compact id →
  O.privateTarget (O.kind (O.body value)) ≡ true
selectedPrivate family (O.recordOf owner (O.receipt (Receipt.entry stored (Receipt.finished meaning names result)))) id selected = refl
selectedPrivate family (O.recordOf owner (O.receipt (Receipt.entry stored (Receipt.active meaning names work)))) id ()
selectedPrivate family (O.recordOf owner (O.receipt (Receipt.entry stored Receipt.used))) id ()
selectedPrivate family (O.recordOf owner (O.registration _)) id ()
selectedPrivate family (O.recordOf owner (O.checkout _)) id ()
selectedPrivate family (O.recordOf owner (O.creationIntent _)) id ()
selectedPrivate family (O.recordOf owner (O.defaults _)) id ()
selectedPrivate family (O.recordOf owner (O.policyVersion _ _)) id ()
selectedPrivate family (O.recordOf owner (O.currentPolicy _)) id ()
selectedPrivate family (O.recordOf owner (O.note _)) id ()
selectedPrivate family (O.recordOf owner (O.notePosting _ _)) id ()
selectedPrivate family (O.recordOf owner (O.noteVector _ _)) id ()
selectedPrivate family (O.recordOf owner (O.fileVersion _)) id ()
selectedPrivate family (O.recordOf owner (O.baseBinding _ _)) id ()
selectedPrivate family (O.recordOf owner (O.deltaBinding _ _ _)) id ()
selectedPrivate family (O.recordOf owner (O.basePointer _)) id ()
selectedPrivate family (O.recordOf owner (O.chunk _ _)) id ()
selectedPrivate family (O.recordOf owner (O.posting _ _)) id ()
selectedPrivate family (O.recordOf owner (O.vector _ _)) id ()
selectedPrivate family (O.recordOf owner (O.symbol _ _ _)) id ()
selectedPrivate family (O.recordOf owner (O.edge _ _ _)) id ()
selectedPrivate family (O.recordOf owner (O.publishedView _ _)) id ()
selectedPrivate family (O.recordOf owner (O.structuralSnapshot _ _ _ _)) id ()
selectedPrivate family (O.recordOf owner (O.legacy _ _)) id ()
selectedPrivate family (O.recordOf owner (O.staging _ _)) id ()
selectedPrivate family (O.recordOf owner (O.acceptedWork _ _)) id ()
selectedPrivate family (O.recordOf owner (O.cleanupWork _ _ _)) id ()
selectedPrivate family (O.recordOf owner (O.activeReader _ _)) id ()
selectedPrivate family (O.recordOf owner (O.continuation _ _)) id ()
selectedPrivate family (O.recordOf owner (O.migration _)) id ()
selectedPrivate family (O.recordOf owner (O.usage _)) id ()
selectedPrivate family (O.recordOf owner (O.bootstrap _)) id ()
selectedPrivate family (O.recordOf owner (O.modelCache _)) id ()
selectedPrivate family (O.recordOf owner (O.coordination _)) id ()
selectedPrivate family (O.recordOf owner (O.schemaResource _)) id ()
selectedPrivate family (O.recordOf owner (O.graphResource _ _ _)) id ()
selectedPrivate family (O.recordOf owner (O.logFile _)) id ()
selectedPrivate family (O.recordOf owner (O.bootstrapStage _)) id ()

runAdmissible : ∀ family rows world → O.Admissible world → O.Admissible (run family rows world)
runAdmissible family [] world valid = valid
runAdmissible family ((slot , value) ∷ rows) world valid with DB.lookup slot world in found
... | nothing = runAdmissible family rows world valid
... | just current with decide family current in selected
...   | keep = runAdmissible family rows world valid
...   | compact id = runAdmissible family rows (DB.write slot (Ledger.markerAt id) world)
    (Private.replacePrivate world slot current (Ledger.markerAt id) valid found
      (selectedPrivate family current id selected) (Ledger.markerPlaced id) refl)

-- Compaction changes a selected receipt only into a permanent marker.
runClosed : ∀ (P : ℕ × O.Record → Set) family rows world → All P world →
  (∀ slot id → P (slot , Ledger.markerAt id)) → All P (run family rows world)
runClosed P family [] world holds markerAllowed = holds
runClosed P family ((slot , value) ∷ rows) world holds markerAllowed with DB.lookup slot world
... | nothing = runClosed P family rows world holds markerAllowed
... | just current with decide family current
...   | keep = runClosed P family rows world holds markerAllowed
...   | compact id = runClosed P family rows (DB.write slot (Ledger.markerAt id) world)
    (markerAllowed slot id ∷ O.deleteAll slot world holds) markerAllowed

runKeeps : ∀ family rows world slot value → DB.lookup slot world ≡ just value →
  decide family value ≡ keep → DB.lookup slot (run family rows world) ≡ just value
runKeeps family [] world slot value found kept = found
runKeeps family ((key , original) ∷ rows) world slot value found kept with key ≟ slot
... | yes refl rewrite found | kept = runKeeps family rows world slot value found kept
... | no different with DB.lookup key world
...   | nothing = runKeeps family rows world slot value found kept
...   | just current with decide family current
...     | keep = runKeeps family rows world slot value found kept
...     | compact id = runKeeps family rows (DB.write key (Ledger.markerAt id) world) slot value
        (trans (DB.writePreservesOther key slot (Ledger.markerAt id) world different) found) kept

-- Every selected saved result in the captured store is compacted as a whole.
runMarks : ∀ family rows world slot value id → (slot , value) ∈ rows →
  DB.lookup slot world ≡ just value → decide family value ≡ compact id →
  DB.lookup slot (run family rows world) ≡ just (Ledger.markerAt id)
runMarks family ((.slot , .value) ∷ rows) world slot value id (here refl) found selected
  rewrite found | selected = runKeeps family rows (DB.write slot (Ledger.markerAt id) world) slot
    (Ledger.markerAt id) (DB.writeVisible slot (Ledger.markerAt id) world) refl
runMarks family ((key , original) ∷ rows) world slot value id (there later) found selected with key ≟ slot
... | yes refl rewrite found | selected = runKeeps family rows (DB.write slot (Ledger.markerAt id) world) slot
    (Ledger.markerAt id) (DB.writeVisible slot (Ledger.markerAt id) world) refl
... | no different with DB.lookup key world
...   | nothing = runMarks family rows world slot value id later found selected
...   | just current with decide family current
...     | keep = runMarks family rows world slot value id later found selected
...     | compact other = runMarks family rows (DB.write key (Ledger.markerAt other) world) slot value id later
        (trans (DB.writePreservesOther key slot (Ledger.markerAt other) world different) found) selected

lookupMember : ∀ world slot value → DB.lookup slot world ≡ just value → (slot , value) ∈ world
lookupMember [] slot value ()
lookupMember ((key , stored) ∷ rows) slot value found with slot ≟ key
... | yes refl with just-injective found
...   | refl = here refl
lookupMember ((key , stored) ∷ rows) slot value found | no different = there (lookupMember rows slot value found)

metadataUnselected : ∀ family value → Store.settingsOrNotes (O.kind (O.body value)) ≡ true → decide family value ≡ keep
metadataUnselected family (O.recordOf owner (O.registration _)) ()
metadataUnselected family (O.recordOf owner (O.checkout _)) ()
metadataUnselected family (O.recordOf owner (O.creationIntent _)) valid = refl
metadataUnselected family (O.recordOf owner (O.defaults _)) valid = refl
metadataUnselected family (O.recordOf owner (O.policyVersion _ _)) valid = refl
metadataUnselected family (O.recordOf owner (O.currentPolicy _)) valid = refl
metadataUnselected family (O.recordOf owner (O.note _)) valid = refl
metadataUnselected family (O.recordOf owner (O.notePosting _ _)) valid = refl
metadataUnselected family (O.recordOf owner (O.noteVector _ _)) valid = refl
metadataUnselected family (O.recordOf owner (O.fileVersion _)) ()
metadataUnselected family (O.recordOf owner (O.baseBinding _ _)) ()
metadataUnselected family (O.recordOf owner (O.deltaBinding _ _ _)) ()
metadataUnselected family (O.recordOf owner (O.basePointer _)) ()
metadataUnselected family (O.recordOf owner (O.chunk _ _)) ()
metadataUnselected family (O.recordOf owner (O.posting _ _)) ()
metadataUnselected family (O.recordOf owner (O.vector _ _)) ()
metadataUnselected family (O.recordOf owner (O.symbol _ _ _)) ()
metadataUnselected family (O.recordOf owner (O.edge _ _ _)) ()
metadataUnselected family (O.recordOf owner (O.publishedView _ _)) ()
metadataUnselected family (O.recordOf owner (O.structuralSnapshot _ _ _ _)) ()
metadataUnselected family (O.recordOf owner (O.legacy _ _)) ()
metadataUnselected family (O.recordOf owner (O.staging _ _)) ()
metadataUnselected family (O.recordOf owner (O.acceptedWork _ _)) ()
metadataUnselected family (O.recordOf owner (O.cleanupWork _ _ _)) ()
metadataUnselected family (O.recordOf owner (O.activeReader _ _)) ()
metadataUnselected family (O.recordOf owner (O.continuation _ _)) ()
metadataUnselected family (O.recordOf owner (O.receipt _)) ()
metadataUnselected family (O.recordOf owner (O.migration _)) ()
metadataUnselected family (O.recordOf owner (O.usage _)) valid = refl
metadataUnselected family (O.recordOf owner (O.bootstrap _)) ()
metadataUnselected family (O.recordOf owner (O.modelCache _)) ()
metadataUnselected family (O.recordOf owner (O.coordination _)) ()
metadataUnselected family (O.recordOf owner (O.schemaResource _)) ()
metadataUnselected family (O.recordOf owner (O.graphResource _ _ _)) ()
metadataUnselected family (O.recordOf owner (O.logFile _)) valid = refl
metadataUnselected family (O.recordOf owner (O.bootstrapStage _)) ()

-- A compacted marker has no request or saved result and cannot be selected.
markerNotSelected : ∀ family marker id → decide family (Ledger.markerAt marker) ≢ compact id
markerNotSelected family marker id ()

selectedSource : ∀ family rows world slot value id →
  DB.lookup slot (run family rows world) ≡ just value → decide family value ≡ compact id →
  DB.lookup slot world ≡ just value
selectedSource family [] world slot value id found selected = found
selectedSource family ((key , original) ∷ rows) world slot value id found selected with DB.lookup key world
... | nothing = selectedSource family rows world slot value id found selected
... | just current with decide family current
...   | keep = selectedSource family rows world slot value id found selected
...   | compact marker with key ≟ slot
...     | no different = trans (sym (DB.writePreservesOther key slot (Ledger.markerAt marker) world different))
        (selectedSource family rows (DB.write key (Ledger.markerAt marker) world) slot value id found selected)
...     | yes refl with just-injective (trans (sym (DB.writeVisible slot (Ledger.markerAt marker) world))
        (selectedSource family rows (DB.write slot (Ledger.markerAt marker) world) slot value id found selected))
...       | refl = ⊥-elim (markerNotSelected family marker id selected)

runCleared : ∀ family world slot value → DB.lookup slot (run family world world) ≡ just value → decide family value ≡ keep
runCleared family world slot value found with decide family value in selected
... | keep = refl
... | compact id with just-injective (trans (sym (runMarks family world world slot value id
    (lookupMember world slot value (selectedSource family world world slot value id found selected))
    (selectedSource family world world slot value id found selected) selected)) found)
...   | refl = ⊥-elim (markerNotSelected family id id selected)
