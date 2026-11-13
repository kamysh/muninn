{-# OPTIONS --safe #-}
-- Proofs about the actual policy-aware cleanup worker step.
module Muninn.PolicyCleanupWorkerProof where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.PolicyRuleAdmission as Admission
import Muninn.CleanupEffects as Effects
import Muninn.CleanupProgress as Progress
import Muninn.PolicyCleanupWorker as Worker
import Muninn.CleanupRequest as Request
import Muninn.PolicyCleanupBatch as Batch
import Muninn.StoredPolicy as Stored
import Muninn.CleanupDecision as Decision
import Muninn.CleanupFinalization as Finalization
import Muninn.ReceiptLedger as Ledger
import Muninn.ReceiptTypes as Receipt
import Muninn.CatalogInputs as Input
import Muninn.RequestIdentity as Identity
import Muninn.Dialogue as Dialogue
open import Data.Nat using (ℕ; _<_)
open import Data.Bool using (Bool)
open import Data.String using (String)
open import Data.List using (List)
open import Data.Maybe using (just)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans; subst)
module DB = O.DB

mapEvaluation : ∀ {A B : Set} → (A → B) → DB.Evaluation A → DB.Evaluation B
mapEvaluation f (DB.committed value world) = DB.committed (f value) world
mapEvaluation f (DB.aborted value) = DB.aborted (f value)

evaluationMapping : ∀ {A B : Set} (f : A → B) transaction world →
  DB.evaluate (Worker.mapTransaction f transaction) world ≡ mapEvaluation f (DB.evaluate transaction world)
evaluationMapping f (DB.commit value) world = refl
evaluationMapping f (DB.abort value) world = refl
evaluationMapping f (DB.scan next) world = evaluationMapping f (next world) world
evaluationMapping f (DB.read key next) world = evaluationMapping f (next (DB.lookup key world)) world
evaluationMapping f (DB.put key value next) world = evaluationMapping f next (DB.write key value world)
evaluationMapping f (DB.remove key next) world = evaluationMapping f next (DB.delete key world)
evaluationMapping f (DB.eraseRows count keep next) world = evaluationMapping f next (DB.erase count keep world)

executionMapping : ∀ {A B : Set} (f : A → B) transaction world →
  DB.execute (Worker.mapTransaction f transaction) world ≡
    (f (proj₁ (DB.execute transaction world)) , proj₂ (DB.execute transaction world))
executionMapping f transaction world rewrite evaluationMapping f transaction world with DB.evaluate transaction world
... | DB.committed value after = refl
... | DB.aborted value = refl

module Model where
  module M = E.Model

  module Family (family pointer : ℕ) (accepted : O.World) (rules : List String)
    (validRules : Admission.Entries (Data.List.map Data.String.toList rules))
    (intent : M.Intent (E.rule family rules validRules) accepted)
    (request : Input.Mutation (Input.PolicyTarget × Input.PolicyDraft)) (taskSlot : ℕ) where
    id = Input.Mutation.operationId request
    meaning = Identity.mutation Identity.kApplyPolicy request
    owner = O.family family
    module Policy = Stored.Family family pointer
    open Worker.Model.Family family pointer accepted rules validRules intent request taskSlot using (tick)
    open Batch.Model.Family family pointer accepted rules validRules intent id taskSlot using (batch)

    module At (world : O.World) (current : Policy.Saved world) where
      module Step = Batch.Model.Family.Selected family pointer accepted rules validRules intent id taskSlot current
      module Task = Finalization.Model.Task Step.selection accepted Step.intent id taskSlot
      module Decisions = Decision.Model.Family.Current family pointer accepted rules validRules intent id taskSlot current
      open Worker.Model.Family.Current family pointer accepted rules validRules intent request taskSlot current using (perform)

      -- If any captured edit is eligible, the worker selects an actual batch
      -- rather than waiting for a different protected record.
      performsEdit : ∀ receiptSlot progress guidance → Task.TaskAt world → Step.Pass.Available world →
        Σ ℕ (λ key → Step.Pass.Ready key world ×
          (DB.execute (perform receiptSlot progress guidance) world ≡
            (Worker.advanced , proj₂ (DB.execute (batch key Effects.unchanged) world))))
      performsEdit receiptSlot progress guidance actual available with Decisions.nextForAvailable actual available
      ... | key , selected , ready rewrite selected = key , ready , executionMapping (λ _ → Worker.advanced) (batch key Effects.unchanged) world

      tickUsesCurrent : ∀ receiptSlot names progress guidance →
        Ledger.find id world ≡ just (Ledger.found receiptSlot owner (Receipt.active meaning names progress)) →
        Policy.observe world ≡ just current →
        DB.execute (tick guidance) world ≡ DB.execute (perform receiptSlot progress guidance) world
      tickUsesCurrent receiptSlot names progress guidance found seen
        rewrite Request.activeObserved id meaning owner world receiptSlot names progress found | seen = refl

      -- Under the saved-policy and task guards, an eligible tick strictly
      -- decreases the existing finite cleanup measure.
      tickProgresses : ∀ receiptSlot names progress guidance →
        Ledger.find id world ≡ just (Ledger.found receiptSlot owner (Receipt.active meaning names progress)) →
        Policy.observe world ≡ just current → Task.TaskAt world → Step.Pass.Available world →
        Progress.mass (proj₂ (DB.execute (tick guidance) world)) < Progress.mass world
      tickProgresses receiptSlot names progress guidance found seen actual available
        with performsEdit receiptSlot progress guidance actual available
      ... | key , ready , performed = subst (λ after → Progress.mass after < Progress.mass world)
        (sym (cong proj₂ (trans (tickUsesCurrent receiptSlot names progress guidance found seen) performed)))
        (Batch.Model.Family.Current.productive family pointer accepted rules validRules intent id taskSlot
          world current seen actual key Effects.unchanged ready)
