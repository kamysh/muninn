{-# OPTIONS --safe #-}
-- Remove or forget an existing family using the shared transaction semantics.
module Muninn.RepositoryRemoval where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.RemovalStore as Store
import Muninn.CleanupStorage as Storage
import Muninn.SharedResultRemoval as Shared
import Muninn.RepositoryHistory as History
import Muninn.GlobalHistoryStore as Global
import Muninn.RemovalOutcome as Outcome
import Muninn.ReceiptTypes as Receipt
import Muninn.ReceiptLedger as Ledger
import Muninn.RequestIdentity as Identity
import Muninn.Worktree as Worktree
import Muninn.CatalogInputs as Input
open import Data.Bool using (Bool; true; false; _∨_; _∧_; not)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no; ¬_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; cong)

module DB = O.DB

module Family (family : ℕ) (familyId : Worktree.FamilyId) (scope : Store.Scope)
  (requestId : Input.OperationId) (requestMeaning : Identity.Meaning) where
  owner = O.family family
  module Rows = Store.Family family scope
  module Visibility = E.Model (λ _ _ → false)
  selection = E.rule family []

  -- Concurrent removal requests for this same family share one cleanup.
  matchesTarget : Input.FamilyTarget → Bool
  matchesTarget target with Shared.sameFamily (Input.FamilyTarget.expectedFamily target) familyId
  ... | yes _ = true
  ... | no _ = false

  removalMeaning : Identity.Meaning → Bool
  removalMeaning (Identity.mutation Identity.kUnregister input) = matchesTarget (Input.Mutation.input input)
  removalMeaning (Identity.mutation Identity.kForget input) = matchesTarget (Input.Mutation.input input)
  removalMeaning _ = false

  blocker : O.Record → Bool
  blocker (O.recordOf readerOwner (O.activeReader refs payload)) with E.ownerEqual readerOwner owner
  ... | yes _ = true
  ... | no _ = false
  blocker (O.recordOf receiptOwner (O.receipt (Receipt.entry id (Receipt.active meaning names work)))) with Ledger.sameId id requestId
  ... | yes _ = false
  ... | no _ with E.ownerEqual receiptOwner owner | Shared.requestOwner meaning
  ...   | yes _ | _ = not (removalMeaning meaning)
  ...   | no _ | nothing = false
  ...   | no _ | just target = Shared.belongs familyId target
  blocker _ = false

  cooperativeRemoval : ∀ id meaning names work → removalMeaning meaning ≡ true →
    blocker (O.recordOf owner (O.receipt (Receipt.entry id (Receipt.active meaning names work)))) ≡ false
  cooperativeRemoval id meaning names work removal with Ledger.sameId id requestId
  ... | yes same = refl
  ... | no different with E.ownerEqual owner owner | Shared.requestOwner meaning
  ...   | yes same | target rewrite removal = refl
  ...   | no impossible | target = ⊥-elim (impossible refl)

  blocked : O.World → Bool
  blocked = E.anyRow (λ key value → blocker value)

  -- Completion is admitted only for the saved request for this family.
  matchesScope : Store.Scope → Identity.Meaning → Bool
  matchesScope Store.unregister (Identity.mutation Identity.kUnregister input) = matchesTarget (Input.Mutation.input input)
  matchesScope Store.forget (Identity.mutation Identity.kForget input) = matchesTarget (Input.Mutation.input input)
  matchesScope _ _ = false

  sameMeaning : Identity.Meaning → Bool
  sameMeaning saved with Identity.sameRequest requestMeaning saved
  ... | yes _ = true
  ... | no _ = false

  accepted : O.World → Bool
  accepted world with Ledger.find requestId world
  ... | nothing = false
  ... | just (Ledger.found slot receiptOwner (Receipt.active meaning names work)) with E.ownerEqual receiptOwner owner
  ...   | yes _ = matchesScope scope meaning ∧ sameMeaning meaning
  ...   | no _ = false
  accepted world | just (Ledger.found slot receiptOwner (Receipt.finished meaning names result)) = false
  accepted world | just (Ledger.found slot receiptOwner Receipt.used) = false

  -- The database owner must be tied to the requested family identity. The
  -- preserved policy record provides the link after unregistration as well.
  targetEvidence : O.Record → Bool
  targetEvidence (O.recordOf recordOwner (O.registration info)) with E.ownerEqual recordOwner owner | O.RegistrationInfo.identity info
  ... | yes same | just stored with Shared.sameFamily stored familyId
  ...   | yes identity = true
  ...   | no different = false
  targetEvidence (O.recordOf recordOwner (O.registration info)) | _ | _ = false
  targetEvidence (O.recordOf recordOwner (O.policyVersion version info)) with E.ownerEqual recordOwner owner | Shared.sameFamily (O.PolicyVersionInfo.familyId info) familyId
  ... | yes same | yes identity = true
  ... | _ | _ = false
  targetEvidence _ = false

  targetKnown : O.World → Bool
  targetKnown = E.anyRow (λ key value → targetEvidence value)

  -- Conflicting saved identities must never authorize deleting this owner.
  targetContradiction : O.Record → Bool
  targetContradiction (O.recordOf recordOwner (O.registration info)) with E.ownerEqual recordOwner owner | O.RegistrationInfo.identity info
  ... | yes same | just stored with Shared.sameFamily stored familyId
  ...   | yes identity = false
  ...   | no different = true
  targetContradiction (O.recordOf recordOwner (O.registration info)) | _ | _ = false
  targetContradiction (O.recordOf recordOwner (O.policyVersion version info)) with E.ownerEqual recordOwner owner | Shared.sameFamily (O.PolicyVersionInfo.familyId info) familyId
  ... | yes same | no different = true
  ... | _ | _ = false
  targetContradiction _ = false

  consistentTarget : O.World → Bool
  consistentTarget world = targetKnown world ∧ not (E.anyRow (λ key value → targetContradiction value) world)

  ready : O.World → Bool
  ready world = accepted world ∧ (consistentTarget world ∧ (not (Visibility.familyRegistered selection world) ∧ not (blocked world)))

  data Reply : Set where
    waiting completed : Reply
    clarify usedId : Reply

  message : Reply → String
  message waiting = "Earlier work is still finishing. Removal will continue automatically."
  message completed = "Removal is complete."
  message clarify = "I cannot match this removal to an accepted request. Tell me the repository and what you want removed."
  message usedId = "This request ID was already used and its details were removed. Check the repository status before submitting a new request."

  -- Continue the accepted request only after the earlier holders have finished.
  localFor : Store.Scope → O.World → DB.Transaction Reply → DB.Transaction Reply
  localFor mode [] next = next
  localFor mode ((key , value) ∷ rest) next with Store.Family.action family mode value
  ... | Store.keep = localFor mode rest next
  ... | Store.erase = DB.remove key (localFor mode rest next)
  ... | Store.compact id = DB.put key (Ledger.markerAt id) (localFor mode rest next)

  localCompiledFor : ∀ mode rows next world → DB.evaluate (localFor mode rows next) world ≡
    DB.evaluate next (Store.Family.run family mode rows world)
  localCompiledFor mode [] next world = refl
  localCompiledFor mode ((key , value) ∷ rows) next world with Store.Family.action family mode value
  ... | Store.keep = localCompiledFor mode rows next world
  ... | Store.erase = localCompiledFor mode rows next (DB.delete key world)
  ... | Store.compact id = localCompiledFor mode rows next (DB.write key (Ledger.markerAt id) world)

  -- Mark the family unavailable before waiting for existing users. The saved
  -- request stays active; no failure checkpoint or extra confirmation is needed.
  fence : ℕ → O.World → DB.Transaction Reply
  fence slot world with DB.lookup slot world
  ... | just (O.recordOf recordOwner (O.registration info)) with E.ownerEqual recordOwner owner | O.RegistrationInfo.identity info
  ...   | no different | _ = DB.commit clarify
  ...   | yes same | nothing = DB.commit clarify
  ...   | yes same | just storedFamily with Shared.sameFamily storedFamily familyId
  ...     | yes identity = DB.put slot (O.recordOf recordOwner (O.registration (record info { retired = true }))) (DB.commit waiting)
  ...     | no different = DB.commit clarify
  fence slot world | _ = DB.commit clarify

  -- New family work must use this same saved registration view.
  mayStartNewWork : O.World → Bool
  mayStartNewWork = Visibility.familyRegistered selection

  finishGlobal : Store.Scope → O.World → DB.Transaction Reply
  finishGlobal Store.unregister world = DB.commit completed
  finishGlobal Store.forget world = Global.compile family world (DB.commit completed)

  finishScope : Store.Scope → O.World → DB.Transaction Reply
  finishScope mode world = localFor mode world
    (DB.scan λ after → Shared.compile familyId after (DB.scan (finishGlobal mode)))

  -- A concurrent forget is an explicit request for the wider scope.
  requestsForget : O.Record → Bool
  requestsForget (O.recordOf receiptOwner (O.receipt (Receipt.entry id (Receipt.active (Identity.mutation Identity.kForget input) names work)))) with E.ownerEqual receiptOwner owner
  ... | yes same = matchesTarget (Input.Mutation.input input)
  ... | no different = false
  requestsForget _ = false

  chooseScope : Store.Scope → Bool → Store.Scope
  chooseScope Store.forget _ = Store.forget
  chooseScope Store.unregister true = Store.forget
  chooseScope Store.unregister false = Store.unregister

  effectiveScope : O.World → Store.Scope
  effectiveScope world = chooseScope scope (E.anyRow (λ key value → requestsForget value) world)

  complete : O.World → DB.Transaction Reply
  complete world = finishScope (effectiveScope world) world

  localResult : Store.Scope → O.World → O.World
  localResult mode world = Store.Family.run family mode world world

  sharedResult : Store.Scope → O.World → O.World
  sharedResult mode world = Shared.run familyId localAfter localAfter
    where localAfter = localResult mode world

  resultWorld : Store.Scope → O.World → O.World
  resultWorld Store.unregister world = sharedResult Store.unregister world
  resultWorld Store.forget world = Global.run family afterShared afterShared
    where afterShared = sharedResult Store.forget world

  sharedAdmissible : ∀ mode world → O.Admissible world → O.Admissible (sharedResult mode world)
  sharedAdmissible mode world valid = Shared.runAdmissible familyId localAfter localAfter
    (Store.Family.Valid.admissible family mode world valid)
    where localAfter = localResult mode world

  resultAdmissible : ∀ mode world → O.Admissible world → O.Admissible (resultWorld mode world)
  resultAdmissible Store.unregister world valid = sharedAdmissible Store.unregister world valid
  resultAdmissible Store.forget world valid = Global.runAdmissible family afterShared afterShared
    (sharedAdmissible Store.forget world valid)
    where afterShared = sharedResult Store.forget world

  sharedScope : ∀ mode world → O.Admissible world →
    All (λ row → Store.AllowedFor mode owner (proj₂ row)) (sharedResult mode world)
  sharedScope mode world valid = Shared.runClosed (λ row → Store.AllowedFor mode owner (proj₂ row))
    familyId localAfter localAfter (Store.Family.Valid.completeScope family mode world valid)
    (λ slot id → Store.allowedOther mode owner (Ledger.markerAt id) (λ ()))
    where localAfter = localResult mode world

  resultScope : ∀ mode world → O.Admissible world →
    All (λ row → Store.AllowedFor mode owner (proj₂ row)) (resultWorld mode world)
  resultScope Store.unregister world valid = sharedScope Store.unregister world valid
  resultScope Store.forget world valid = Global.runClosed (λ row → Store.AllowedFor Store.forget owner (proj₂ row))
    family afterShared afterShared (sharedScope Store.forget world valid)
    where afterShared = sharedResult Store.forget world

  forgetRemovesOwned : ∀ world → O.Admissible world → ∀ slot value →
    DB.lookup slot (resultWorld Store.forget world) ≡ just value → O.owner value ≢ owner
  forgetRemovesOwned world valid slot value found = Storage.lookupAll (resultWorld Store.forget world) slot value
    (resultScope Store.forget world valid) found

  resultPreservesOther : ∀ mode world slot value → O.Unique world →
    DB.lookup slot world ≡ just value → O.owner value ≢ owner → Shared.decide familyId value ≡ Shared.keep →
    Global.selected family value ≡ false → DB.lookup slot (resultWorld mode world) ≡ just value
  resultPreservesOther Store.unregister world slot value unique found other kept historyKept =
    Shared.runKeeps familyId localAfter localAfter slot value
      (Store.Family.preservesOthers family Store.unregister world slot value unique found other) kept
    where localAfter = localResult Store.unregister world
  resultPreservesOther Store.forget world slot value unique found other kept historyKept =
    Global.runKeeps family afterShared afterShared slot value sharedFound historyKept
    where
    localAfter = localResult Store.forget world
    afterShared = sharedResult Store.forget world
    sharedFound = Shared.runKeeps familyId localAfter localAfter slot value
      (Store.Family.preservesOthers family Store.forget world slot value unique found other) kept

  resultPreservesMetadata : ∀ world slot value → O.Unique world →
    DB.lookup slot world ≡ just value → Store.settingsOrNotes (O.kind (O.body value)) ≡ true →
    DB.lookup slot (resultWorld Store.unregister world) ≡ just value
  resultPreservesMetadata world slot value unique found metadata =
    Shared.runKeeps familyId localAfter localAfter slot value localFound (Shared.metadataUnselected familyId value metadata)
    where
    module Unregistered = Store.Family family Store.unregister
    localAfter = Unregistered.run world world
    localFound : DB.lookup slot localAfter ≡ just value
    localFound = trans (Unregistered.exact world slot unique)
      (trans (cong Unregistered.intendedAt found) (Unregistered.metadataUnchanged value refl metadata))

  sharedRemoves : ∀ mode world slot value id → O.Unique world →
    DB.lookup slot world ≡ just value → O.owner value ≢ owner → Shared.decide familyId value ≡ Shared.compact id →
    DB.lookup slot (sharedResult mode world) ≡ just (Ledger.markerAt id)
  sharedRemoves mode world slot value id unique found other selected =
    Shared.runMarks familyId localAfter localAfter slot value id
      (Shared.lookupMember localAfter slot value preserved) preserved selected
    where
    localAfter = localResult mode world
    preserved = Store.Family.preservesOthers family mode world slot value unique found other

  resultRemovesShared : ∀ mode world slot value id → O.Unique world →
    DB.lookup slot world ≡ just value → O.owner value ≢ owner → Shared.decide familyId value ≡ Shared.compact id →
    DB.lookup slot (resultWorld mode world) ≡ just (Ledger.markerAt id)
  resultRemovesShared Store.unregister world slot value id unique found other selected =
    sharedRemoves Store.unregister world slot value id unique found other selected
  resultRemovesShared Store.forget world slot value id unique found other selected =
    Global.runKeeps family afterShared afterShared slot (Ledger.markerAt id)
      (sharedRemoves Store.forget world slot value id unique found other selected) refl
    where afterShared = sharedResult Store.forget world

  resultRemovesUsage : ∀ world slot item → O.Unique world →
    DB.lookup slot world ≡ just (O.recordOf O.installation (O.usage item)) →
    History.mentions family (History.owners item) ≡ true →
    DB.lookup slot (resultWorld Store.forget world) ≡ nothing
  resultRemovesUsage world slot item unique found selected =
    Global.runRemoves family afterShared afterShared slot value
      (Shared.lookupMember afterShared slot value sharedFound) sharedFound selected
    where
    value = O.recordOf O.installation (O.usage item)
    localAfter = localResult Store.forget world
    afterShared = sharedResult Store.forget world
    localFound = Store.Family.preservesOthers family Store.forget world slot value unique found (λ ())
    sharedFound = Shared.runKeeps familyId localAfter localAfter slot value localFound refl

  resultRemovesLog : ∀ world slot item → O.Unique world →
    DB.lookup slot world ≡ just (O.recordOf O.installation (O.logFile item)) →
    History.mentions family (History.owners item) ≡ true →
    DB.lookup slot (resultWorld Store.forget world) ≡ nothing
  resultRemovesLog world slot item unique found selected =
    Global.runRemoves family afterShared afterShared slot value
      (Shared.lookupMember afterShared slot value sharedFound) sharedFound selected
    where
    value = O.recordOf O.installation (O.logFile item)
    localAfter = localResult Store.forget world
    afterShared = sharedResult Store.forget world
    localFound = Store.Family.preservesOthers family Store.forget world slot value unique found (λ ())
    sharedFound = Shared.runKeeps familyId localAfter localAfter slot value localFound refl

  finishScopeCompiled : ∀ mode world →
    DB.evaluate (finishScope mode world) world ≡ DB.committed completed (resultWorld mode world)
  finishScopeCompiled Store.unregister world = trans
    (localCompiledFor Store.unregister world (DB.scan λ after → Shared.compile familyId after (DB.scan (finishGlobal Store.unregister))) world)
    (Shared.compiled familyId localAfter (DB.scan (finishGlobal Store.unregister)) localAfter)
    where localAfter = localResult Store.unregister world
  finishScopeCompiled Store.forget world = trans
    (localCompiledFor Store.forget world (DB.scan λ after → Shared.compile familyId after (DB.scan (finishGlobal Store.forget))) world)
    (trans (Shared.compiled familyId localAfter (DB.scan (finishGlobal Store.forget)) localAfter)
      (Global.compiled family afterShared (DB.commit completed) afterShared))
    where
    localAfter = localResult Store.forget world
    afterShared = sharedResult Store.forget world

  completeCommitted : ∀ world →
    DB.evaluate (complete world) world ≡ DB.committed completed (resultWorld (effectiveScope world) world)
  completeCommitted world = finishScopeCompiled (effectiveScope world) world

  previous : O.World → Reply
  previous world with Ledger.find requestId world
  ... | just (Ledger.found slot receiptOwner Receipt.used) = usedId
  ... | just (Ledger.found slot receiptOwner (Receipt.finished meaning names result)) with matchesScope scope meaning ∧ sameMeaning meaning
  ...   | true = completed
  ...   | false = clarify
  previous world | _ = clarify

  -- A normal retry advances automatically: first fence, then wait for earlier
  -- users, then complete in one transaction. No timeout abandons the request.
  step : ℕ → DB.Transaction Reply
  step registrationSlot = DB.scan λ world → choose (accepted world) (consistentTarget world) (mayStartNewWork world) (blocked world) world
    where
    choose : Bool → Bool → Bool → Bool → O.World → DB.Transaction Reply
    choose false known registered earlier world = DB.commit (previous world)
    choose true false registered earlier world = DB.commit clarify
    choose true true true earlier world = fence registrationSlot world
    choose true true false true world = DB.commit waiting
    choose true true false false world = complete world

  stepCompletes : ∀ slot world → ready world ≡ true →
    DB.evaluate (step slot) world ≡
      DB.committed completed (resultWorld (effectiveScope world) world)
  stepCompletes slot world isReady with accepted world | consistentTarget world | mayStartNewWork world | blocked world | isReady
  ... | true | true | false | false | refl = completeCommitted world


  stepPreservesStore : ∀ slot world → O.Admissible world → ready world ≡ true →
    O.Admissible (proj₂ (DB.execute (step slot) world)) ×
    All (λ row → Store.AllowedFor (effectiveScope world) owner (proj₂ row)) (proj₂ (DB.execute (step slot) world))
  stepPreservesStore slot world valid isReady rewrite stepCompletes slot world isReady =
    resultAdmissible (effectiveScope world) world valid , resultScope (effectiveScope world) world valid

  previousUsed : ∀ world receiptSlot receiptOwner →
    Ledger.find requestId world ≡ just (Ledger.found receiptSlot receiptOwner Receipt.used) → previous world ≡ usedId
  previousUsed world receiptSlot receiptOwner found rewrite found = refl

  acceptedUsed : ∀ world receiptSlot receiptOwner →
    Ledger.find requestId world ≡ just (Ledger.found receiptSlot receiptOwner Receipt.used) → accepted world ≡ false
  acceptedUsed world receiptSlot receiptOwner found rewrite found = refl

  retryReclaimed : ∀ slot world receiptSlot receiptOwner →
    Ledger.find requestId world ≡ just (Ledger.found receiptSlot receiptOwner Receipt.used) →
    DB.evaluate (step slot) world ≡ DB.committed usedId world
  retryReclaimed slot world receiptSlot receiptOwner found rewrite acceptedUsed world receiptSlot receiptOwner found | previousUsed world receiptSlot receiptOwner found = refl

  -- Interruption at the transaction boundary leaves either the prior world
  -- or the whole committed cleanup, never a partial family removal.
  interruptedAtomic : ∀ slot before after → ready before ≡ true →
    O.Execution.Interrupted (O.Execution.atomic (step slot) O.Execution.done) before after →
    (after ≡ before) ⊎
      (after ≡ resultWorld (effectiveScope before) before)
  interruptedAtomic slot before after readyBefore interrupted with Ledger.atomicBoundary (step slot) before after interrupted
  ... | inj₁ unchanged = inj₁ unchanged
  ... | inj₂ committed = inj₂ (trans committed (cong (λ evaluated → DB.publish before evaluated) (stepCompletes slot before readyBefore)))

  -- History is outside the database transaction. Clean it first; an
  -- interruption leaves the accepted database request unchanged, and retry
  -- repeats the same idempotent cleanup.
  FullWorld : Set
  FullWorld = O.World × History.History

  prepareHistory : FullWorld → FullWorld
  prepareHistory (world , records) with ready world | effectiveScope world
  ... | true | Store.forget = world , History.clean family records
  ... | _ | _ = world , records

  prepareKeepsRequest : ∀ world records → Data.Product.proj₁ (prepareHistory (world , records)) ≡ world
  prepareKeepsRequest world records with ready world | effectiveScope world
  ... | true | Store.forget = refl
  ... | true | Store.unregister = refl
  ... | false | Store.forget = refl
  ... | false | Store.unregister = refl

  prepareRetry : ∀ world records → prepareHistory (prepareHistory (world , records)) ≡ prepareHistory (world , records)
  prepareRetry world records with ready world in readyEq | effectiveScope world in scopeEq
  ... | true | Store.forget rewrite readyEq | scopeEq | History.cleanRetry family records = refl
  ... | true | Store.unregister rewrite readyEq | scopeEq = refl
  ... | false | Store.forget rewrite readyEq = refl
  ... | false | Store.unregister rewrite readyEq = refl

  commitFull : ℕ → FullWorld → Reply × FullWorld
  commitFull slot (world , records) with ready world | effectiveScope world | History.emptyOf family records
  ... | true | Store.forget | false = waiting , (world , records)
  ... | _ | _ | _ with DB.execute (step slot) world
  ...   | reply , after = reply , (after , records)

  runFull : ℕ → FullWorld → Reply × FullWorld
  runFull slot before = commitFull slot (prepareHistory before)

  retryAfterHistory : ∀ slot before → runFull slot (prepareHistory before) ≡ runFull slot before
  retryAfterHistory slot before = cong (commitFull slot) (prepareRetry (Data.Product.proj₁ before) (Data.Product.proj₂ before))

  fullForgetCompletes : ∀ slot world records → ready world ≡ true → effectiveScope world ≡ Store.forget →
    runFull slot (world , records) ≡ (completed , (resultWorld Store.forget world , History.clean family records))
  fullForgetCompletes slot world records isReady isForget with ready world in readyEq | effectiveScope world in scopeEq | isReady | isForget
  ... | true | Store.forget | refl | refl rewrite readyEq | scopeEq | History.cleanIsEmpty family records | stepCompletes slot world readyEq | scopeEq = refl

  fullForgetHistory : ∀ slot world records → ready world ≡ true → effectiveScope world ≡ Store.forget →
    All (λ item → History.mentions family (History.Entry.owners item) ≡ false)
      (History.usage (proj₂ (proj₂ (runFull slot (world , records))))) ×
    All (λ item → History.mentions family (History.Entry.owners item) ≡ false)
      (History.logs (proj₂ (proj₂ (runFull slot (world , records))))) ×
    All (λ item → History.mentions family (History.Entry.owners item) ≡ false)
      (History.buffered (proj₂ (proj₂ (runFull slot (world , records)))))
  fullForgetHistory slot world records isReady isForget rewrite fullForgetCompletes slot world records isReady isForget =
    History.cleanRowsNoFamily family (History.usage records) , History.cleanRowsNoFamily family (History.logs records) , History.cleanRowsNoFamily family (History.buffered records)

  fullForgetGlobalHistory : ∀ slot world records → ready world ≡ true → effectiveScope world ≡ Store.forget →
    ∀ key value → DB.lookup key (proj₁ (proj₂ (runFull slot (world , records)))) ≡ just value →
      Global.selected family value ≡ false
  fullForgetGlobalHistory slot world records isReady isForget key value found
    rewrite fullForgetCompletes slot world records isReady isForget =
      Global.runCleared family afterShared key value found
    where afterShared = sharedResult Store.forget world

  fullForgetGoal : ∀ slot world records → O.Admissible world → ready world ≡ true → effectiveScope world ≡ Store.forget →
    Outcome.ForgetGoal family (proj₁ (proj₂ (runFull slot (world , records)))) (proj₂ (proj₂ (runFull slot (world , records))))
  fullForgetGoal slot world records valid isReady isForget rewrite fullForgetCompletes slot world records isReady isForget =
    forgetRemovesOwned world valid ,
    Global.runCleared family (sharedResult Store.forget world) ,
    History.cleanRowsNoFamily family (History.usage records) ,
    History.cleanRowsNoFamily family (History.logs records) ,
    History.cleanRowsNoFamily family (History.buffered records)

  noSharedResult : ∀ world slot receiptOwner id meaning names result target →
    DB.lookup slot (resultWorld Store.forget world) ≡ just (O.recordOf receiptOwner (O.receipt (Receipt.entry id (Receipt.finished meaning names result)))) →
    Shared.requestOwner meaning ≡ just target → Shared.belongs familyId target ≡ false
  noSharedResult world slot receiptOwner id meaning names result target found owned
    with Shared.belongs familyId target in belongs
  ... | false = refl
  ... | true with Shared.runCleared familyId (localResult Store.forget world) slot
      (O.recordOf receiptOwner (O.receipt (Receipt.entry id (Receipt.finished meaning names result))))
      (Global.runSource family (sharedResult Store.forget world) (sharedResult Store.forget world) slot
        (O.recordOf receiptOwner (O.receipt (Receipt.entry id (Receipt.finished meaning names result)))) found)
  ...   | cleared rewrite owned | belongs with cleared
  ...     | ()

  fullForgetShared : ∀ slot world records → ready world ≡ true → effectiveScope world ≡ Store.forget →
    ∀ key receiptOwner id meaning names result target →
    DB.lookup key (proj₁ (proj₂ (runFull slot (world , records)))) ≡ just (O.recordOf receiptOwner (O.receipt (Receipt.entry id (Receipt.finished meaning names result)))) →
    Shared.requestOwner meaning ≡ just target → Shared.belongs familyId target ≡ false
  fullForgetShared slot world records isReady isForget key receiptOwner id meaning names result target found owned
    rewrite fullForgetCompletes slot world records isReady isForget =
      noSharedResult world key receiptOwner id meaning names result target found owned
