{-# OPTIONS --safe #-}
-- Safety of an actual productive worker transaction under its current policy.
module Muninn.PolicyCleanupWorkerSafety where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.PolicyRuleAdmission as Admission
import Muninn.CleanupEffects as Effects
import Muninn.CleanupReceiptPreservation as Continuity
import Muninn.PolicyCleanupBatch as Batch
import Muninn.StoredPolicy as Stored
import Muninn.CleanupFinalization as Finalization
import Muninn.PolicyCleanupWorkerProof as Proof
import Muninn.PolicyCleanupWorker as Worker
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

      tickSafety : ∀ receiptSlot names progress guidance →
        Ledger.find id world ≡ just (Ledger.found receiptSlot owner (Receipt.active meaning names progress)) →
        Policy.observe world ≡ just current → Task.TaskAt world → Step.Pass.Available world →
        Outcome.Safety Step.selection world (proj₂ (DB.execute (tick guidance) world))
      tickSafety receiptSlot names progress guidance found seen actual available
        with performsEdit receiptSlot progress guidance actual available
      ... | key , ready , performed = subst (Outcome.Safety Step.selection world)
        (sym (cong proj₂ (trans (tickUsesCurrent receiptSlot names progress guidance found seen) performed)))
        (Batch.Model.Family.Current.safety family pointer accepted rules validRules intent id taskSlot
          world current seen actual key Effects.unchanged)

      tickKeepsReceipt : ∀ receiptSlot names progress guidance → O.Admissible world →
        Ledger.find id world ≡ just (Ledger.found receiptSlot owner (Receipt.active meaning names progress)) →
        Policy.observe world ≡ just current → Task.TaskAt world → Step.Pass.Available world →
        Ledger.find id (proj₂ (DB.execute (tick guidance) world)) ≡ Ledger.find id world
      tickKeepsReceipt receiptSlot names progress guidance valid found seen actual available
        with performsEdit receiptSlot progress guidance actual available
      ... | key , ready , performed = trans
        (cong (Ledger.find id) (trans
          (cong proj₂ (trans (tickUsesCurrent receiptSlot names progress guidance found seen) performed))
          (Batch.Model.Family.Current.sameEffect family pointer accepted rules validRules intent id taskSlot
            world current seen actual key Effects.unchanged)))
        (Continuity.Model.Core.preserves Step.selection accepted Step.intent id key world valid)

      tickBatch : ∀ receiptSlot names progress guidance →
        Ledger.find id world ≡ just (Ledger.found receiptSlot owner (Receipt.active meaning names progress)) →
        Policy.observe world ≡ just current → Task.TaskAt world → Step.Pass.Available world →
        Σ ℕ (λ key → Step.Pass.Ready key world ×
          (proj₂ (DB.execute (tick guidance) world) ≡
           proj₂ (DB.execute (Batch.Model.Family.batch family pointer accepted rules validRules intent id taskSlot key Effects.unchanged) world)))
      tickBatch receiptSlot names progress guidance found seen actual available
        with performsEdit receiptSlot progress guidance actual available
      ... | key , ready , performed = key , ready , cong proj₂
        (trans (tickUsesCurrent receiptSlot names progress guidance found seen) performed)
