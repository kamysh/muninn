{-# OPTIONS --safe #-}
-- Productive worker runs are finite, including when policy changes between runs.
module Muninn.PolicyCleanupWorkerRun where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.CleanupProgress as Progress
import Muninn.PolicyCleanupBatch as Batch
import Muninn.PolicyCleanupWorker as Worker
import Muninn.PolicyCleanupWorkerProof as Proof
import Muninn.CleanupFinalization as Finalization
import Muninn.StoredPolicy as Stored
import Muninn.ReceiptLedger as Ledger
import Muninn.ReceiptTypes as Receipt
import Muninn.CatalogInputs as Input
import Muninn.Dialogue as Dialogue
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Data.Bool using (Bool)
open import Data.String using (String)
open import Data.List using (List)
open import Data.Maybe using (just)
open import Data.Product using (_×_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
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

    module At (world : O.World) (current : Policy.Saved world) where
      module Step = Batch.Model.Family.Selected excluded family pointer accepted rules intent id taskSlot current
      module Task = Finalization.Model.Task excluded Step.selection accepted Step.intent id taskSlot
      open Proof.Model.Family.At excluded family pointer accepted rules intent request taskSlot world current
        using (tickProgresses)

    data One (before : O.World) : O.World → Set where
      edit : (current : Policy.Saved before) (receiptSlot : ℕ) (names : Receipt.Names id meaning)
        (progress : Receipt.Work) (guidance : String → Dialogue.Prompt) →
        Ledger.find id before ≡ just (Ledger.found receiptSlot owner (Receipt.active meaning names progress)) →
        Policy.observe before ≡ just current → At.Task.TaskAt before current before →
        At.Step.Pass.Available before current before →
        One before (proj₂ (DB.execute (tick guidance) before))

    decreases : ∀ {before after} → One before after → Progress.mass after < Progress.mass before
    decreases {before} (edit current receiptSlot names progress guidance found seen actual available) =
      Proof.Model.Family.At.tickProgresses excluded family pointer accepted rules intent request taskSlot
        before current receiptSlot names progress guidance found seen actual available

    data Run : ℕ → O.World → O.World → Set where
      stop : ∀ world → Run zero world world
      advance : ∀ {count before middle after} → One before middle → Run count middle after → Run (suc count) before after

    bounded : ∀ {count before after} → Run count before after → count + Progress.mass after ≤ Progress.mass before
    bounded (stop world) = ≤-refl
    bounded (advance first rest) = ≤-trans (s≤s (bounded rest)) (decreases first)
