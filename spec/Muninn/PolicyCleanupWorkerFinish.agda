{-# OPTIONS --safe #-}
-- The worker actually finalizes when the checked cleanup outcome is ready.
module Muninn.PolicyCleanupWorkerFinish where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.PolicyCleanupBatch as Batch
import Muninn.PolicyCleanupWorker as Worker
import Muninn.PolicyCleanupWorkerProof as Proof
import Muninn.PolicyCleanupCompletionProof as Completion
import Muninn.PolicyCleanupFinish as Finish
import Muninn.CleanupDecision as Decision
import Muninn.CleanupFinalization as Finalization
import Muninn.StoredPolicy as Stored
import Muninn.ReceiptLedger as Ledger
import Muninn.ReceiptTypes as Receipt
import Muninn.CatalogInputs as Input
import Muninn.Dialogue as Dialogue
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool)
open import Data.String using (String)
open import Data.List using (List)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
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
        using (perform; finishStepDefinition)
      open Proof.Model.Family.At excluded family pointer accepted rules intent request taskSlot world current
        using (tickUsesCurrent)
      continuation = "Cleanup is waiting for remaining work."
      missing = Ledger.continueDialogue receiptSlot progress (guidance "I cannot read the current repository settings.")

      module Verified (ready : Task.Ready world) (quiet : Step.Pass.NoEdit world) where
        open Completion.Model.Family.At.Verified excluded family pointer accepted rules intent request taskSlot
          world current seen valid progress continuation guidance missing receiptSlot names located found ready
          public using (reply; after; committed; currentOutcome)
        open Finish.Model.Family excluded family pointer accepted rules intent request taskSlot using (finish)

        selected : Decisions.next ≡ Decision.doFinish
        selected = Decisions.nextForCompletion (proj₁ ready) quiet (proj₂ ready)

        performsFinish : DB.execute (perform receiptSlot progress guidance) world ≡
          (Worker.response reply , after)
        performsFinish rewrite selected = trans
          (cong (λ transaction → DB.execute transaction world) (finishStepDefinition receiptSlot progress guidance))
          (trans (Proof.executionMapping Worker.response (finish progress continuation guidance missing) world)
            (cong (λ outcome → Worker.response (proj₁ outcome) , proj₂ outcome) committed))

        tickFinishes : DB.execute (tick guidance) world ≡ (Worker.response reply , after)
        tickFinishes = trans (tickUsesCurrent receiptSlot names progress guidance found seen) performsFinish

        checkedBeforeCompletion : Outcome.Complete Step.selection accepted Step.intent world world
        checkedBeforeCompletion = currentOutcome
