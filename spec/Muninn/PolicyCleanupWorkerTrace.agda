{-# OPTIONS --safe #-}
-- Each productive worker tick is an actual edge of the cleanup trace.
module Muninn.PolicyCleanupWorkerTrace where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.PolicyRuleAdmission as Admission
import Muninn.CleanupEffects as Effects
import Muninn.PolicyCleanupBatch as Batch
import Muninn.PolicyCleanupWorkerProof as Proof
import Muninn.PolicyCleanupWorker as Worker
import Muninn.StoredPolicy as Stored
import Muninn.CleanupFinalization as Finalization
import Muninn.ReceiptLedger as Ledger
import Muninn.ReceiptTypes as Receipt
import Muninn.CatalogInputs as Input
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool)
open import Data.String using (String)
open import Data.List using (List)
open import Data.Maybe using (just)
open import Data.Product using (Σ; _×_; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; cong; trans; subst)
module DB = O.DB

module Model where
  module Outcome = E.Model
  module Family (family pointer : ℕ) (accepted : O.World) (rules : List String)
    (validRules : Admission.Entries (Data.List.map Data.String.toList rules))
    (intent : Outcome.Intent (E.rule family rules validRules) accepted)
    (request : Input.Mutation (Input.PolicyTarget × Input.PolicyDraft)) (taskSlot : ℕ) where
    module Policy = Stored.Family family pointer
    open Proof.Model.Family family pointer accepted rules validRules intent request taskSlot
      using (id; meaning; owner)
    open Worker.Model.Family family pointer accepted rules validRules intent request taskSlot using (tick)
    module At (world : O.World) (current : Policy.Saved world) where
      module Step = Batch.Model.Family.Selected family pointer accepted rules validRules intent id taskSlot current
      module Task = Finalization.Model.Task Step.selection accepted Step.intent id taskSlot
      open Proof.Model.Family.At family pointer accepted rules validRules intent request taskSlot world current
        using (performsEdit; tickUsesCurrent)

      tickTrace : ∀ receiptSlot names progress guidance →
        Ledger.find id world ≡ just (Ledger.found receiptSlot owner (Receipt.active meaning names progress)) →
        Policy.observe world ≡ just current → Task.TaskAt world → Step.Pass.Available world →
        Σ ℕ (λ count → Step.Pass.Trace count world (proj₂ (DB.execute (tick guidance) world)))
      tickTrace receiptSlot names progress guidance found seen actual available
        with performsEdit receiptSlot progress guidance actual available
      ... | key , ready , performed
        with Batch.Model.Family.Current.trail family pointer accepted rules validRules intent id taskSlot
          world current seen actual key Effects.unchanged
      ... | count , trail = count , subst (Step.Pass.Trace count world)
        (sym (trans (cong proj₂ (trans (tickUsesCurrent receiptSlot names progress guidance found seen) performed))
          (Batch.Model.Family.Current.sameEffect family pointer accepted rules validRules intent id taskSlot
            world current seen actual key Effects.unchanged))) trail
