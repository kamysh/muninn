{-# OPTIONS --safe #-}
-- A newer blocker triggers a bounded task under the same active request.
module Muninn.PolicyCleanupWorkerFollowup where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.PolicyCleanupBatch as Batch
import Muninn.PolicyCleanupWorker as Worker
import Muninn.PolicyCleanupWorkerProof as Proof
import Muninn.CleanupDecision as Decision
import Muninn.CleanupFinalization as Finalization
import Muninn.RecordAllocation as Allocation
import Muninn.StoredPolicy as Stored
import Muninn.ReceiptLedger as Ledger
import Muninn.ReceiptTypes as Receipt
import Muninn.CatalogInputs as Input
import Muninn.Dialogue as Dialogue
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool)
open import Data.String using (String)
open import Data.List using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (just)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
module DB = O.DB

module Model (excluded : List String → String → Bool) where
  module Outcome = E.Model excluded
  module Family (family pointer : ℕ) (accepted : O.World) (rules : List String)
    (intent : Outcome.Intent (E.rule family rules) accepted)
    (request : Input.Mutation (Input.PolicyTarget × Input.PolicyDraft)) (taskSlot : ℕ) where
    module Policy = Stored.Family family pointer
    open Proof.Model.Family excluded family pointer accepted rules intent request taskSlot
      using (id; meaning; owner)
    open Worker.Model.Family excluded family pointer accepted rules intent request taskSlot using (tick)

    module At (world : O.World) (current : Policy.Saved world)
      (seen : Policy.observe world ≡ just current) (valid : O.Admissible world)
      (receiptSlot : ℕ) (names : Receipt.Names id meaning) (progress : Receipt.Work)
      (guidance : String → Dialogue.Prompt)
      (located : DB.lookup receiptSlot world ≡ just (Ledger.recordAt {id = id} owner (Receipt.active meaning names progress)))
      (found : Ledger.find id world ≡ just (Ledger.found receiptSlot owner (Receipt.active meaning names progress))) where
      module Step = Batch.Model.Family.Selected excluded family pointer accepted rules intent id taskSlot current
      module Task = Finalization.Model.Task excluded Step.selection accepted Step.intent id taskSlot
      module Decisions = Decision.Model.Family.Current excluded family pointer accepted rules intent id taskSlot current
      open Worker.Model.Family.Current excluded family pointer accepted rules intent request taskSlot current
        using (perform; followupStepDefinition)
      open Proof.Model.Family.At excluded family pointer accepted rules intent request taskSlot world current
        using (tickUsesCurrent)
      open Allocation.Model.Family.Current excluded Step.selection world valid "Follow-up cleanup" "Cleanup is progressing."
        guidance id meaning names receiptSlot progress located found
        using (after; next; commits; ownedCapture)

      module Blocked (actual : Task.TaskAt world) (quiet : Step.Pass.NoEdit world)
        (pending : Σ ℕ (λ key → Task.Final.Pending key world))
        (blocker : Σ (ℕ × O.Record) (λ row → row ∈ world × Decisions.Followup.Unscheduled row)) where
        selected : Decisions.next ≡ Decision.doFollowup
        selected = Decisions.nextForFollowup actual quiet pending blocker

        performsFollowup : DB.execute (perform receiptSlot progress guidance) world ≡
          (Worker.response (Ledger.resume receiptSlot next) , after)
        performsFollowup rewrite selected = trans
          (cong (λ transaction → DB.execute transaction world) (followupStepDefinition progress guidance))
          (trans (Proof.executionMapping Worker.response
            (Ledger.update id meaning (Receipt.generation progress) (Ledger.checkpoint (Receipt.versions progress))
              (Allocation.Model.Family.effect excluded Step.selection id "Follow-up cleanup" "Cleanup is progressing." guidance)) world)
            (cong (λ outcome → Worker.response (proj₁ outcome) , proj₂ outcome) commits))

        tickSchedules : DB.execute (tick guidance) world ≡ (Worker.response (Ledger.resume receiptSlot next) , after)
        tickSchedules = trans (tickUsesCurrent receiptSlot names progress guidance found seen) performsFollowup

        originalRequestStillActive : Ledger.find id after ≡
          just (Ledger.found receiptSlot owner (Receipt.active meaning names next))
        originalRequestStillActive = proj₂ ownedCapture
