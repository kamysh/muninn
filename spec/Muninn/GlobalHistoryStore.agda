{-# OPTIONS --safe #-}
-- Remove repository-owned usage and log records from the modeled store.
module Muninn.GlobalHistoryStore where

import Muninn.OwnedState as O
import Muninn.RepositoryHistory as History
import Muninn.HistoryOwnership as Ownership
open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe.Properties
open import Data.Product using (_×_; _,_; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
module DB = O.DB

selected : ℕ → O.Record → Bool
selected = Ownership.owns

selectedPrivate : ∀ family value → selected family value ≡ true → O.privateTarget (O.kind (O.body value)) ≡ true
selectedPrivate family (O.recordOf owner (O.usage item)) present = refl
selectedPrivate family (O.recordOf owner (O.logFile item)) present = refl
selectedPrivate family (O.recordOf owner (O.registration _)) ()
selectedPrivate family (O.recordOf owner (O.checkout _)) ()
selectedPrivate family (O.recordOf owner (O.creationIntent _)) ()
selectedPrivate family (O.recordOf owner (O.defaults _)) ()
selectedPrivate family (O.recordOf owner (O.policyVersion _ _)) ()
selectedPrivate family (O.recordOf owner (O.currentPolicy _)) ()
selectedPrivate family (O.recordOf owner (O.note _)) ()
selectedPrivate family (O.recordOf owner (O.notePosting _ _)) ()
selectedPrivate family (O.recordOf owner (O.noteVector _ _)) ()
selectedPrivate family (O.recordOf owner (O.fileVersion _)) ()
selectedPrivate family (O.recordOf owner (O.baseBinding _ _)) ()
selectedPrivate family (O.recordOf owner (O.deltaBinding _ _ _)) ()
selectedPrivate family (O.recordOf owner (O.basePointer _)) ()
selectedPrivate family (O.recordOf owner (O.chunk _ _)) ()
selectedPrivate family (O.recordOf owner (O.posting _ _)) ()
selectedPrivate family (O.recordOf owner (O.vector _ _)) ()
selectedPrivate family (O.recordOf owner (O.symbol _ _ _)) ()
selectedPrivate family (O.recordOf owner (O.edge _ _ _)) ()
selectedPrivate family (O.recordOf owner (O.publishedView _ _)) ()
selectedPrivate family (O.recordOf owner (O.structuralSnapshot _ _ _ _)) ()
selectedPrivate family (O.recordOf owner (O.legacy _ _)) ()
selectedPrivate family (O.recordOf owner (O.staging _ _)) ()
selectedPrivate family (O.recordOf owner (O.acceptedWork _ _)) ()
selectedPrivate family (O.recordOf owner (O.cleanupWork _ _ _)) ()
selectedPrivate family (O.recordOf owner (O.activeReader _ _)) ()
selectedPrivate family (O.recordOf owner (O.continuation _ _)) ()
selectedPrivate family (O.recordOf owner (O.receipt _)) ()
selectedPrivate family (O.recordOf owner (O.migration _)) ()
selectedPrivate family (O.recordOf owner (O.bootstrap _)) ()
selectedPrivate family (O.recordOf owner (O.modelCache _)) ()
selectedPrivate family (O.recordOf owner (O.coordination _)) ()
selectedPrivate family (O.recordOf owner (O.schemaResource _)) ()
selectedPrivate family (O.recordOf owner (O.graphResource _ _ _)) ()
selectedPrivate family (O.recordOf owner (O.bootstrapStage _)) ()

compile : ∀ {A : Set} → ℕ → O.World → DB.Transaction A → DB.Transaction A
compile family [] next = next
compile {A} family ((slot , value) ∷ rows) next = DB.read slot choose
  where
  choose : Maybe O.Record → DB.Transaction A
  choose nothing = compile family rows next
  choose (just value) with selected family value
  ... | false = compile family rows next
  ... | true = DB.remove slot (compile family rows next)

run : ℕ → O.World → O.World → O.World
run family [] world = world
run family ((slot , value) ∷ rows) world with DB.lookup slot world
... | nothing = run family rows world
... | just current with selected family current
...   | false = run family rows world
...   | true = run family rows (DB.delete slot world)

compiled : ∀ {A} family rows (next : DB.Transaction A) world →
  DB.evaluate (compile family rows next) world ≡ DB.evaluate next (run family rows world)
compiled family [] next world = refl
compiled family ((slot , value) ∷ rows) next world with DB.lookup slot world
... | nothing = compiled family rows next world
... | just current with selected family current
...   | false = compiled family rows next world
...   | true = compiled family rows next (DB.delete slot world)

runAdmissible : ∀ family rows world → O.Admissible world → O.Admissible (run family rows world)
runAdmissible family [] world valid = valid
runAdmissible family ((slot , value) ∷ rows) world valid with DB.lookup slot world in found
... | nothing = runAdmissible family rows world valid
... | just current with selected family current in selection
...   | false = runAdmissible family rows world valid
...   | true = runAdmissible family rows (DB.delete slot world)
    (O.deleteUnreferencedPreservesAdmissibility slot world valid
      (O.privateUnreferenced slot world current valid found (selectedPrivate family current selection)))

runClosed : ∀ (P : ℕ × O.Record → Set) family rows world → All P world → All P (run family rows world)
runClosed P family [] world holds = holds
runClosed P family ((slot , value) ∷ rows) world holds with DB.lookup slot world
... | nothing = runClosed P family rows world holds
... | just current with selected family current
...   | false = runClosed P family rows world holds
...   | true = runClosed P family rows (DB.delete slot world) (O.deleteAll slot world holds)

runKeeps : ∀ family rows world slot value → DB.lookup slot world ≡ just value →
  selected family value ≡ false → DB.lookup slot (run family rows world) ≡ just value
runKeeps family [] world slot value found kept = found
runKeeps family ((key , original) ∷ rows) world slot value found kept with key ≟ slot
... | yes refl rewrite found | kept = runKeeps family rows world slot value found kept
... | no different with DB.lookup key world
...   | nothing = runKeeps family rows world slot value found kept
...   | just current with selected family current
...     | false = runKeeps family rows world slot value found kept
...     | true = runKeeps family rows (DB.delete key world) slot value
      (trans (DB.deletePreservesOther key slot world different) found) kept

runKeepsAbsent : ∀ family rows world slot → DB.lookup slot world ≡ nothing → DB.lookup slot (run family rows world) ≡ nothing
runKeepsAbsent family [] world slot absent = absent
runKeepsAbsent family ((key , value) ∷ rows) world slot absent with DB.lookup key world
... | nothing = runKeepsAbsent family rows world slot absent
... | just current with selected family current
...   | false = runKeepsAbsent family rows world slot absent
...   | true = runKeepsAbsent family rows (DB.delete key world) slot (O.deleteKeepsAbsent key slot world absent)

runRemoves : ∀ family rows world slot value → (slot , value) ∈ rows → DB.lookup slot world ≡ just value →
  selected family value ≡ true → DB.lookup slot (run family rows world) ≡ nothing
runRemoves family ((.slot , .value) ∷ rows) world slot value (here refl) found remove
  rewrite found | remove = runKeepsAbsent family rows (DB.delete slot world) slot (DB.deleteAbsent slot world)
runRemoves family ((key , original) ∷ rows) world slot value (there later) found remove with key ≟ slot
... | yes refl rewrite found | remove = runKeepsAbsent family rows (DB.delete slot world) slot (DB.deleteAbsent slot world)
... | no different with DB.lookup key world
...   | nothing = runRemoves family rows world slot value later found remove
...   | just current with selected family current
...     | false = runRemoves family rows world slot value later found remove
...     | true = runRemoves family rows (DB.delete key world) slot value later
      (trans (DB.deletePreservesOther key slot world different) found) remove

-- Deletion cannot manufacture a record, and a complete pass leaves no
-- repository-attributed usage or log record in the store.
deleteSource : ∀ key world slot value → DB.lookup slot (DB.delete key world) ≡ just value → DB.lookup slot world ≡ just value
deleteSource key world slot value found with key ≟ slot
... | yes refl with trans (sym (DB.deleteAbsent slot world)) found
...   | ()
deleteSource key world slot value found | no different = trans (sym (DB.deletePreservesOther key slot world different)) found

runSource : ∀ family rows world slot value → DB.lookup slot (run family rows world) ≡ just value → DB.lookup slot world ≡ just value
runSource family [] world slot value found = found
runSource family ((key , original) ∷ rows) world slot value found with DB.lookup key world
... | nothing = runSource family rows world slot value found
... | just current with selected family current
...   | false = runSource family rows world slot value found
...   | true = deleteSource key world slot value (runSource family rows (DB.delete key world) slot value found)

lookupMember : ∀ rows slot value → DB.lookup slot rows ≡ just value → (slot , value) ∈ rows
lookupMember [] slot value ()
lookupMember ((key , current) ∷ rows) slot value present with slot ≟ key
... | yes refl with Data.Maybe.Properties.just-injective present
...   | refl = here refl
lookupMember ((key , current) ∷ rows) slot value present | no different = there (lookupMember rows slot value present)

runCleared : ∀ family world slot value → DB.lookup slot (run family world world) ≡ just value → selected family value ≡ false
runCleared family world slot value found with selected family value in selection
... | false = refl
... | true with trans (sym (runRemoves family world world slot value
    (lookupMember world slot value (runSource family world world slot value found))
    (runSource family world world slot value found) selection)) found
...   | ()
