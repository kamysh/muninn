{-# OPTIONS --safe #-}
-- Each productive step leaves the facts needed for the next worker step.
module Muninn.PolicyCleanupWorkerContinue where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.CleanupEffects as Effects
import Muninn.PolicyCleanupBatch as Batch
import Muninn.PolicyCleanupWorker as Worker
import Muninn.PolicyCleanupWorkerProof as Proof
import Muninn.PolicyCleanupWorkerSafety as Safety
import Muninn.CleanupFinalization as Finalization
import Muninn.StoredPolicy as Stored
import Muninn.ReceiptLedger as Ledger
import Muninn.ReceiptTypes as Receipt
import Muninn.CatalogInputs as Input
import Muninn.RequestIdentity as Identity
import Muninn.Dialogue as Dialogue
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool)
open import Data.String using (String)
open import Data.List using (List)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans; subst)
module DB = O.DB

module Model (excluded : List String → String → Bool) where
  module Outcome = E.Model excluded
  module Family (family pointer : ℕ) (accepted : O.World) (rules : List String)
    (intent : Outcome.Intent (E.rule family rules) accepted)
    (request : Input.Mutation (Input.PolicyTarget × Input.PolicyDraft)) (taskSlot : ℕ)
    (receiptSlot : ℕ) (names : Receipt.Names (Input.Mutation.operationId request)
      (Identity.mutation Identity.kApplyPolicy request))
    (progress : Receipt.Work) (guidance : String → Dialogue.Prompt) where
    module Policy = Stored.Family family pointer
    open Proof.Model.Family excluded family pointer accepted rules intent request taskSlot using (id; meaning; owner)
    open Worker.Model.Family excluded family pointer accepted rules intent request taskSlot using (tick)
    module Task = Finalization.Model.Task excluded (E.rule family rules) accepted intent id taskSlot

    record Context (world : O.World) : Set where
      constructor context
      field current : Policy.Saved world
            seen : Policy.observe world ≡ just current
            valid : O.Admissible world
            task : Task.TaskAt world
            located : DB.lookup receiptSlot world ≡ just (Ledger.recordAt {id = id} owner (Receipt.active meaning names progress))
            receipt : Ledger.find id world ≡ just (Ledger.found receiptSlot owner (Receipt.active meaning names progress))
    open Context

    module At (world : O.World) (ctx : Context world) where
      module Step = Batch.Model.Family.Selected excluded family pointer accepted rules intent id taskSlot (current ctx)
      open Proof.Model.Family.At excluded family pointer accepted rules intent request taskSlot world (current ctx)
        using (performsEdit)
      open Safety.Model.Family.At excluded family pointer accepted rules intent request taskSlot world (current ctx)
        using (tickKeepsReceipt; tickBatch)
      after = proj₂ (DB.execute (tick guidance) world)

      next : Step.Pass.Available world → Context after
      next available with tickBatch receiptSlot names progress guidance (receipt ctx) (seen ctx) (task ctx) available
      ... | key , ready , equalWorld with Batch.Model.Family.Current.savedTask excluded family pointer accepted rules intent id taskSlot
        world (current ctx) (seen ctx) (task ctx) key Effects.unchanged
      ...   | payload , savedTask with Policy.observe after in observed
      ...     | nothing = ⊥-elim (impossible selected)
        where
        selected = trans (cong Policy.selectedPolicy equalWorld)
          (Batch.Model.Family.Current.selectedPolicyPreserved excluded family pointer accepted rules intent id taskSlot
            world (current ctx) (seen ctx) (task ctx) key Effects.unchanged)
        impossible : Policy.selectedPolicy after ≡ just (Policy.policy (current ctx)) → ⊥
        impossible proof rewrite observed = contradiction proof
          where
          contradiction : nothing ≡ just (Policy.policy (current ctx)) → ⊥
          contradiction ()
      ...     | just new = context new observed nextValid nextTask nextLocated nextReceipt
        where
        nextValid = subst O.Admissible (sym equalWorld)
          (Batch.Model.Family.Current.admissible excluded family pointer accepted rules intent id taskSlot
            world (current ctx) (seen ctx) (task ctx) key Effects.unchanged (valid ctx))
        nextTask : Task.TaskAt after
        nextTask = O.recordOf owner (O.cleanupWork id (Outcome.Intent.keys intent) payload) ,
          trans (cong (DB.lookup taskSlot) equalWorld) savedTask , refl , refl
        nextLocated = trans (cong (DB.lookup receiptSlot) equalWorld)
          (Batch.Model.Family.Current.activeReceipt excluded family pointer accepted rules intent id taskSlot
            world (current ctx) (seen ctx) (task ctx) key Effects.unchanged id meaning names progress receiptSlot owner (located ctx))
        nextReceipt = trans (tickKeepsReceipt receiptSlot names progress guidance (valid ctx) (receipt ctx) (seen ctx) (task ctx) available) (receipt ctx)
