{-# OPTIONS --safe #-}
-- Once protected work is released and the finite pass is quiet, finish it.
module Muninn.PolicyCleanupWorkerRest where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.CleanupLoop as Loop
import Muninn.CleanupNoStall as NoStall
import Muninn.PolicyCleanupBatch as Batch
import Muninn.PolicyCleanupWorker as Worker
import Muninn.PolicyCleanupWorkerProof as Proof
import Muninn.PolicyCleanupWorkerFinish as Finish
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
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
module DB = O.DB

module Model (excluded : List String → String → Bool) where
  module Outcome = E.Model excluded
  module Family (family pointer : ℕ) (accepted : O.World) (rules : List String)
    (intent : Outcome.Intent (E.rule family rules) accepted)
    (request : Input.Mutation (Input.PolicyTarget × Input.PolicyDraft)) (taskSlot : ℕ) where
    module Policy = Stored.Family family pointer
    open Proof.Model.Family excluded family pointer accepted rules intent request taskSlot using (id; meaning; owner)
    open Worker.Model.Family excluded family pointer accepted rules intent request taskSlot using (tick)

    module At (world : O.World) (current : Policy.Saved world)
      (seen : Policy.observe world ≡ just current) (valid : O.Admissible world)
      (receiptSlot : ℕ) (names : Receipt.Names id meaning) (progress : Receipt.Work)
      (guidance : String → Dialogue.Prompt)
      (located : DB.lookup receiptSlot world ≡ just (Ledger.recordAt {id = id} owner (Receipt.active meaning names progress)))
      (found : Ledger.find id world ≡ just (Ledger.found receiptSlot owner (Receipt.active meaning names progress))) where
      module Step = Batch.Model.Family.Selected excluded family pointer accepted rules intent id taskSlot current
      module Task = Finalization.Model.Task excluded Step.selection accepted Step.intent id taskSlot
      module Clean = Loop.Model.Run excluded Step.selection accepted Step.intent

      module Released (actual : Task.TaskAt world)
        (released : Clean.Use.Released world) (quiet : Step.Pass.NoEdit world) where
        module Stall = NoStall.Model.Run.At excluded Step.selection accepted Step.intent world valid released quiet

        module Unblocked (noBlocker : Stall.NoBlocker) where
          ready : Task.Ready world
          ready = actual , Stall.noPending noBlocker

          open Finish.Model.Family.At.Verified excluded family pointer accepted rules intent request taskSlot
            world current seen valid receiptSlot names progress guidance located found ready quiet
            public using (reply; after; tickFinishes; checkedBeforeCompletion)

          finishes : DB.execute (tick guidance) world ≡ (Worker.response reply , after)
          finishes = tickFinishes

          outcome : Outcome.Complete Step.selection accepted Step.intent world world
          outcome = checkedBeforeCompletion
