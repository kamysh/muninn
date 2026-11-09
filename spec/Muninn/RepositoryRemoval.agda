{-# OPTIONS --safe #-}
-- Existing remove/unregister and approved forget-all, with receipt-first replay.
module Muninn.RepositoryRemoval where
import Muninn.OwnedState as O
import Muninn.RemovalStore as Store
import Muninn.RetirementCleanup as Serving
import Muninn.CurrentReader as Readers
import Muninn.RequestAdmission as Admission
import Muninn.ContentPublication as Publication
import Muninn.ExclusionOutcomes as E
import Muninn.ArtifactIdentity as Equal
import Muninn.CatalogInputs as I
import Muninn.RequestIdentity as N
import Muninn.ReceiptTypes as R
import Muninn.ReceiptLedger as Ledger
import Muninn.CleanupStorage as Storage
import Muninn.Dialogue as D
import Muninn.RecordAllocation as Allocation
import Muninn.CleanupAdmissionStorage as Insert
import Muninn.Config as Config
open import Data.Nat using (ℕ; suc; _≟_; _<_; s≤s)
open import Data.Nat.Properties using (≤-refl)
import Data.Nat as Nat
open import Data.Bool using (Bool; true; false; not; _∧_)
open import Data.List using (List; []; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Data.String using (String)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
module DB = O.DB
module Exec = O.Execution

meaning : Store.Scope → I.Mutation I.FamilyTarget → N.Meaning
meaning Store.unregister request = N.mutation N.kUnregister request
meaning Store.forget request = N.mutation N.kForget request

names : ∀ scope request → R.Names (I.Mutation.operationId request) (meaning scope request)
names Store.unregister request = refl
names Store.forget request = refl

isRemoval : ∀ scope request → E.removalInput (meaning scope request) ≡ true
isRemoval Store.unregister request = refl
isRemoval Store.forget request = refl

result : Store.Scope → String
result Store.unregister = "Unregistered. The code index is removed; saved notes and settings are preserved."
result Store.forget = "Forgotten. All data owned by this repository has been removed."

waiting : D.Prompt
waiting = D.prompt
  (D.text 'A' " search that started earlier is still using this repository. Removal is accepted and remains active; new searches cannot extend the wait.")
  (D.text 'C' "ontinue this request after the running search finishes. Removal is not complete yet.") []

contextNeeded : D.Prompt
contextNeeded = D.prompt (D.text 'I' " cannot match this request to the saved repository identity.")
  (D.text 'S' "end the repository ID and location again so I can resolve the target before changing anything.") []

otherRequest : D.Prompt
otherRequest = D.prompt (D.text 'A' "nother removal request for this repository is already active.")
  (D.text 'C' "ontinue that request first, then send this request again if it is still needed.") []

lookupMember : ∀ world key value → DB.lookup key world ≡ just value → (key , value) ∈ world
lookupMember ((first , stored) ∷ rows) key value found with key ≟ first
... | yes refl with found
...   | refl = here refl
lookupMember ((first , stored) ∷ rows) key value found | no other = there (lookupMember rows key value found)

anyHit : ∀ test world key value → (key , value) ∈ world → test key value ≡ true → E.anyRow test world ≡ true
anyHit test ((key , value) ∷ rows) .key .value (here refl) hit rewrite hit = refl
anyHit test ((first , stored) ∷ rows) key value (there member) hit with test first stored
... | true = refl
... | false = anyHit test rows key value member hit

module Family (family : ℕ) (scope : Store.Scope) (requestInput : I.Mutation I.FamilyTarget) where
  module Rows = Store.Family family scope
  owner = O.family family
  id = I.Mutation.operationId requestInput
  input = meaning scope requestInput
  named = names scope requestInput
  target = I.Mutation.input requestInput

  matches : O.Record → Bool
  matches (O.recordOf actualOwner (O.registration info)) = E.sameOwner actualOwner owner ∧ does (Equal.FamilyId? (O.RegistrationInfo.id info) (I.FamilyTarget.expectedFamily target))
  matches (O.recordOf actualOwner (O.creationIntent policy)) = E.sameOwner actualOwner owner ∧ does (Equal.FamilyId? (Config.FamilyPolicy.family policy) (I.FamilyTarget.expectedFamily target))
  matches (O.recordOf actualOwner (O.policyVersion initial info)) = E.sameOwner actualOwner owner ∧ does (Equal.FamilyId? (O.PolicyVersionInfo.familyId info) (I.FamilyTarget.expectedFamily target))
  matches value = false
  targetPresent : O.World → Bool
  targetPresent world = E.anyRow (λ key value → matches value) world

  reader : O.Record → Bool
  reader (O.recordOf actualOwner (O.activeReader held payload)) = E.sameOwner actualOwner owner
  reader value = false
  hasReaders : O.World → Bool
  hasReaders world = E.anyRow (λ key value → reader value) world

  anotherRemoval : O.Record → Bool
  anotherRemoval (O.recordOf actualOwner (O.receipt (R.entry other (R.active original names work)))) =
    E.sameOwner actualOwner owner ∧ (E.removalInput original ∧ not (does (Ledger.sameId id other)))
  anotherRemoval value = false
  conflicting : O.World → Bool
  conflicting world = E.anyRow (λ key value → anotherRemoval value) world

  -- Begin checks the target and the removal admission fence in the SAME
  -- transaction that accepts the durable original request. Replay comes first.
  beginSnapshot : ℕ → R.Work → O.World → DB.Transaction Ledger.Reply
  beginSnapshot slot progress world with Ledger.find id world
  ... | just stored = DB.commit (Ledger.existing input stored)
  ... | nothing with E.pendingRemovalFor owner world | targetPresent world
  ...   | true | _ = DB.commit (Ledger.ask otherRequest)
  ...   | false | false = DB.commit (Ledger.ask contextNeeded)
  ...   | false | true = Ledger.accept id input named slot owner progress

  begin : ℕ → R.Work → DB.Transaction Ledger.Reply
  begin slot progress = DB.scan (beginSnapshot slot progress)

  initial = R.progressOf 0 [] "Removal accepted; waiting for earlier searches before final cleanup."
  start : DB.Transaction Ledger.Reply
  start = DB.scan (λ world → beginSnapshot (Allocation.freshId world) initial world)

  acceptsExplicit : ∀ before → Ledger.find id before ≡ nothing → E.pendingRemovalFor owner before ≡ false → targetPresent before ≡ true →
    DB.execute start before ≡ (Ledger.accepted (Allocation.freshId before) , DB.write (Allocation.freshId before) (Ledger.recordAt {id = id} owner (R.active input named initial)) before)
  acceptsExplicit before noId notRemoving located rewrite noId | notRemoving | located | noId | Insert.freshAbsent before (Allocation.freshId before) (Allocation.fresh before) = refl

  rejectsSecondRemoval : ∀ before → Ledger.find id before ≡ nothing → E.pendingRemovalFor owner before ≡ true →
    DB.execute start before ≡ (Ledger.ask otherRequest , before)
  rejectsSecondRemoval before noId pending rewrite noId | pending with targetPresent before
  ... | true = refl
  ... | false = refl

  -- No loop or second confirmation is added. An unambiguous typed request
  -- enters the existing admission check immediately. An ambiguous request is
  -- handled by the generic dialogue before it becomes this typed request.
  beginReplay : ∀ slot progress world stored → Ledger.find id world ≡ just stored → DB.execute (begin slot progress) world ≡ (Ledger.existing input stored , world)
  beginReplay slot progress world stored located rewrite located = refl

  complete : ℕ → O.World → DB.Transaction Ledger.Reply
  complete slot world = Ledger.seal slot (λ answer → Ledger.markerAt id) (λ answer → Ledger.saved (result scope))
    (λ reason → Ledger.explain Ledger.historyReclaimed) (Rows.compile world (result scope))

  active : ℕ → ℕ → N.Meaning → R.Work → O.World → DB.Transaction Ledger.Reply
  active expected slot original progress world with N.sameRequest input original
  ... | no different = DB.commit (Ledger.explain Ledger.differentRequest)
  ... | yes same with R.generation progress Nat.≟ expected
  ...   | no stale = DB.commit (Ledger.resume slot progress)
  ...   | yes current with conflicting world | hasReaders world
  ...     | true | _ = DB.commit (Ledger.continueDialogue slot progress otherRequest)
  ...     | false | true = DB.commit (Ledger.continueDialogue slot progress waiting)
  ...     | false | false = complete slot world

  found : ℕ → O.World → Ledger.Found id → DB.Transaction Ledger.Reply
  found expected world (Ledger.found slot actualOwner state) with E.ownerEqual actualOwner owner
  ... | no wrongOwner = DB.commit (Ledger.explain Ledger.differentRequest)
  ... | yes same with state
  ...   | R.active original names progress = active expected slot original progress world
  ...   | R.finished original names answer = DB.commit (Ledger.existing input (Ledger.found slot actualOwner state))
  ...   | R.used = DB.commit (Ledger.explain Ledger.historyReclaimed)

  -- A used-ID marker is installation-owned; inspect it BEFORE owner checks.
  snapshot : ℕ → O.World → DB.Transaction Ledger.Reply
  snapshot expected world with Ledger.find id world
  ... | nothing = DB.commit (Ledger.explain Ledger.unknownId)
  ... | just (Ledger.found slot actualOwner R.used) = DB.commit (Ledger.explain Ledger.historyReclaimed)
  ... | just stored = found expected world stored
  transaction : ℕ → DB.Transaction Ledger.Reply
  transaction expected = DB.scan (snapshot expected)

  pending : ∀ before slot names progress → DB.lookup slot before ≡ just (Ledger.recordAt {id = id} owner (R.active input names progress)) → E.pendingRemovalFor owner before ≡ true
  pending before slot names progress located = anyHit _ before slot _ (lookupMember before slot _ located) self
    where
    self : E.pendingRemovalValue owner (Ledger.recordAt {id = id} owner (R.active input names progress)) ≡ true
    self with E.ownerEqual owner owner
    ... | yes same rewrite isRemoval scope requestInput = refl
    ... | no different = ⊥-elim (different refl)

  blocksAdmission : ∀ selection before slot names progress checkout → E.targetOwner selection ≡ owner →
    DB.lookup slot before ≡ just (Ledger.recordAt {id = id} owner (R.active input names progress)) → Serving.available selection before checkout ≡ false
  blocksAdmission selection before slot names progress checkout owns located rewrite owns | pending before slot names progress located
    with E.Model.familyRegistered selection before ∧ E.Model.checkoutLive selection before checkout
  ... | true = refl
  ... | false = refl

  blocksReader : ∀ selection pointer checkout before slot names progress → E.targetOwner selection ≡ owner →
    DB.lookup slot before ≡ just (Ledger.recordAt {id = id} owner (R.active input names progress)) →
    Readers.Model.Family.currentRoot selection pointer checkout before ≡ nothing
  blocksReader selection pointer checkout before slot names progress owns located =
    Readers.Model.Family.removalBlocksCurrent selection pointer checkout before
      (trans (cong (λ targetOwner → E.pendingRemovalFor targetOwner before) owns) (pending before slot names progress located))

  blocksPublication : ∀ {A : Set} pointer version before slot names progress (next : DB.Transaction A) wait →
    DB.lookup slot before ≡ just (Ledger.recordAt {id = id} owner (R.active input names progress)) →
    DB.evaluate (Publication.PolicyGuard.transaction owner pointer version next wait) before ≡ DB.aborted wait
  blocksPublication pointer version before slot names progress next wait located =
    Publication.PolicyGuard.removalBlocksPublication owner pointer version next wait before (pending before slot names progress located)

  waitsForReaders : ∀ before slot names progress →
    Ledger.find id before ≡ just (Ledger.found slot owner (R.active input names progress)) →
    conflicting before ≡ false → hasReaders before ≡ true →
    DB.execute (transaction (R.generation progress)) before ≡ (Ledger.continueDialogue slot progress waiting , before)
  waitsForReaders before slot names progress located alone readers rewrite located with E.ownerEqual owner owner
  ... | no different = ⊥-elim (different refl)
  ... | yes same with N.sameRequest input input
  ...   | no different = ⊥-elim (different refl)
  ...   | yes sameInput with R.generation progress Nat.≟ R.generation progress
  ...     | no different = ⊥-elim (different refl)
  ...     | yes sameGeneration rewrite alone | readers = refl

  module Ready (before : O.World) (valid : O.Admissible before) (slot : ℕ) (names : R.Names id input) (progress : R.Work)
    (located : DB.lookup slot before ≡ just (Ledger.recordAt {id = id} owner (R.active input names progress)))
    (locatedId : Ledger.find id before ≡ just (Ledger.found slot owner (R.active input names progress)))
    (alone : conflicting before ≡ false) (readersFinished : hasReaders before ≡ false) where
    module V = Rows.Valid before valid
    changed = Rows.final before
    after = DB.write slot (Ledger.markerAt id) changed

    compacts : DB.lookup slot changed ≡ just (Ledger.markerAt id)
    compacts = Rows.receiptCompacted before slot id (R.active input names progress) (O.Admissible.unique valid) located
    afterValid : O.Admissible after
    afterValid = Storage.writeAdmissible changed slot (Ledger.markerAt id) (Ledger.markerAt id) V.admissible compacts refl refl (Ledger.markerPlaced id) (λ ref ())

    performs : DB.execute (transaction (R.generation progress)) before ≡ (Ledger.saved (result scope) , after)
    performs rewrite locatedId with E.ownerEqual owner owner
    ... | no different = ⊥-elim (different refl)
    ... | yes same with N.sameRequest input input
    ...   | no different = ⊥-elim (different refl)
    ...   | yes sameInput with R.generation progress Nat.≟ R.generation progress
    ...     | no different = ⊥-elim (different refl)
    ...     | yes sameGeneration rewrite alone | readersFinished |
      Ledger.sealCommitted slot (λ answer → Ledger.markerAt id) (λ answer → Ledger.saved (result scope)) (λ reason → Ledger.explain Ledger.historyReclaimed)
        (Rows.compile before (result scope)) before (result scope) changed (Rows.performs before before (result scope)) = refl

    finishesThenReclaims : R.Transition (R.active input names progress) (R.finished input names (result scope)) ×
      R.Transition (R.finished input names (result scope)) R.used
    finishesThenReclaims = R.finish input names progress (result scope) , R.reclaim input names (result scope)

    written : Ledger.find id after ≡ just (Ledger.found slot O.installation R.used)
    written = Ledger.writtenReceiptVisible id slot O.installation R.used changed
    protocolCompletion : Admission.Completed id input after
    protocolCompletion = record
      { slot = slot; owner = owner; names = names; result = result scope
      ; terminal = inj₂ (record { before = before; progress = progress; transaction = transaction (R.generation progress)
          ; removal = isRemoval scope requestInput; accepted = locatedId; committed = performs; marker = written }) }

    retry : DB.execute (transaction (R.generation progress)) after ≡ (Ledger.explain Ledger.historyReclaimed , after)
    retry rewrite written = refl

    exact : ∀ key → DB.lookup key after ≡ Rows.intendedAt (DB.lookup key before)
    exact key with slot Nat.≟ key
    ... | yes refl = trans (DB.writeVisible slot (Ledger.markerAt id) changed) (sym (trans (cong Rows.intendedAt located) (Rows.localReceipt id (R.active input names progress))))
    ... | no different = trans (DB.writePreservesOther slot key (Ledger.markerAt id) changed different) (Rows.exact before key (O.Admissible.unique valid))

    otherFamilies : ∀ key value → O.owner value ≢ owner → DB.lookup key before ≡ just value → DB.lookup key after ≡ just value
    otherFamilies key value foreign found = trans (exact key) (trans (cong Rows.intendedAt found) (Rows.foreignUnchanged value foreign))

    boundary : ∀ observed → Exec.Interrupted (Exec.atomic (transaction (R.generation progress)) Exec.done) before observed → (observed ≡ before) ⊎ (observed ≡ after)
    boundary observed interrupted with Ledger.atomicBoundary (transaction (R.generation progress)) before observed interrupted
    ... | inj₁ same = inj₁ same
    ... | inj₂ same = inj₂ (trans same (cong proj₂ performs))
    completedAtomic : ∀ observed reply final → Exec.Completed (Exec.atomic (transaction (R.generation progress)) Exec.done) observed reply final → DB.execute (transaction (R.generation progress)) observed ≡ (reply , final)
    completedAtomic observed reply final (Exec.committed Exec.stop) = refl
    converges : ∀ observed reply final → Exec.Interrupted (Exec.atomic (transaction (R.generation progress)) Exec.done) before observed →
      Exec.Completed (Exec.atomic (transaction (R.generation progress)) Exec.done) observed reply final → final ≡ after
    converges observed reply final interrupted completed with boundary observed interrupted
    ... | inj₁ same = trans (sym (cong proj₂ (completedAtomic observed reply final completed)))
      (trans (cong (λ world → proj₂ (DB.execute (transaction (R.generation progress)) world)) same) (cong proj₂ performs))
    ... | inj₂ same = trans (sym (cong proj₂ (completedAtomic observed reply final completed)))
      (trans (cong (λ world → proj₂ (DB.execute (transaction (R.generation progress)) world)) same) (cong proj₂ retry))

    scopeComplete : All.All (λ row → Rows.Allowed (proj₂ row)) after
    scopeComplete = Rows.allowedForeign (Ledger.markerAt id) (λ ()) All.∷ O.deleteAll slot changed V.completeScope

    notesAndSettings : ∀ key value → scope ≡ Store.unregister → Store.settingsOrNotes (O.kind (O.body value)) ≡ true →
      DB.lookup key before ≡ just value → DB.lookup key after ≡ just value
    notesAndSettings key value mode metadata found = trans (exact key) (trans (cong Rows.intendedAt found) (Rows.metadataUnchanged value mode metadata))

    everyOwnedReceipt : ∀ key other state → DB.lookup key before ≡ just (O.recordOf owner (O.receipt (R.entry other state))) → DB.lookup key after ≡ just (Ledger.markerAt other)
    everyOwnedReceipt key other state found = trans (exact key) (trans (cong Rows.intendedAt found) (Rows.localReceipt other state))

    noNewFamilyRecords : ∀ key value other → O.owner value ≡ O.family other → DB.lookup key after ≡ just value → DB.lookup key before ≡ just value
    noNewFamilyRecords key value other owned located with DB.lookup key before in prior
    ... | nothing = ⊥-elim (impossible (trans (sym (trans (exact key) (cong Rows.intendedAt prior))) located))
      where impossible : nothing ≢ just value
            impossible ()
    ... | just old = cong just (Rows.projectFamilySame old value other owned
        (trans (sym (trans (exact key) (cong Rows.intendedAt prior))) located))

    record Outcome (world : O.World) : Set where
      field clean : All.All (λ row → Rows.Allowed (proj₂ row)) world
            validStore : O.Admissible world
            noNewFamilyData : ∀ key value other → O.owner value ≡ O.family other → DB.lookup key world ≡ just value → DB.lookup key before ≡ just value
            preserveOthers : ∀ key value → O.owner value ≢ owner → DB.lookup key before ≡ just value → DB.lookup key world ≡ just value
            preserveCurated : ∀ key value → scope ≡ Store.unregister → Store.settingsOrNotes (O.kind (O.body value)) ≡ true → DB.lookup key before ≡ just value → DB.lookup key world ≡ just value
            receiptMarkers : ∀ key other state → DB.lookup key before ≡ just (O.recordOf owner (O.receipt (R.entry other state))) → DB.lookup key world ≡ just (Ledger.markerAt other)
            originalFinished : Ledger.find id world ≡ just (Ledger.found slot O.installation R.used)

    goal : Outcome after
    goal = record { clean = scopeComplete; validStore = afterValid; noNewFamilyData = noNewFamilyRecords; preserveOthers = otherFamilies; preserveCurated = notesAndSettings; receiptMarkers = everyOwnedReceipt; originalFinished = written }

    convergesToGoal : ∀ observed reply final → Exec.Interrupted (Exec.atomic (transaction (R.generation progress)) Exec.done) before observed →
      Exec.Completed (Exec.atomic (transaction (R.generation progress)) Exec.done) observed reply final → Outcome final
    convergesToGoal observed reply final interrupted completed = subst Outcome (sym (converges observed reply final interrupted completed)) goal

  readerCount : O.World → ℕ
  readerCount [] = 0
  readerCount ((key , value) ∷ rows) with reader value
  ... | true = suc (readerCount rows)
  ... | false = readerCount rows

  absentReaderCount : ∀ world key → DB.lookup key world ≡ nothing → readerCount (DB.delete key world) ≡ readerCount world
  absentReaderCount [] key absent = refl
  absentReaderCount ((first , value) ∷ rows) key absent with key Nat.≟ first
  ... | yes same with absent
  ...   | ()
  absentReaderCount ((first , value) ∷ rows) key absent | no different with reader value
  ... | true = cong suc (absentReaderCount rows key absent)
  ... | false = absentReaderCount rows key absent

  releaseDecreases : ∀ world key value → O.Unique world → DB.lookup key world ≡ just value → reader value ≡ true →
    readerCount (DB.delete key world) < readerCount world
  releaseDecreases ((first , stored) ∷ rows) key value (absent , unique) located held with key Nat.≟ first
  ... | yes refl with located
  ...   | refl rewrite held | absentReaderCount rows key absent = ≤-refl
  releaseDecreases ((first , stored) ∷ rows) key value (absent , unique) located held | no different with reader stored
  ... | true = s≤s (releaseDecreases rows key value unique located held)
  ... | false = releaseDecreases rows key value unique located held
