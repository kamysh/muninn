{-# OPTIONS --safe #-}
-- Finite worker steps followed by checked completion of the same request.
module Muninn.PolicyCleanupWorkerConverges where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.CleanupLoop as Loop
import Muninn.CleanupNoStall as NoStall
import Muninn.CleanupFollowupResolution as FollowupResolution
import Muninn.PolicyCleanupBatch as Batch
import Muninn.PolicyCleanupWorker as Worker
import Muninn.PolicyCleanupWorkerContinue as Continue
import Muninn.PolicyCleanupWorkerDrain as Drain
import Muninn.PolicyCleanupWorkerRest as Rest
import Muninn.ReceiptTypes as Receipt
import Muninn.CatalogInputs as Input
import Muninn.RequestIdentity as Identity
import Muninn.Dialogue as Dialogue
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool)
open import Data.String using (String)
open import Data.List using (List)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
module DB = O.DB

module Model (excluded : List String → String → Bool) where
  module Outcome = E.Model excluded
  module Family (family pointer : ℕ) (accepted : O.World) (rules : List String)
    (intent : Outcome.Intent (E.rule family rules) accepted)
    (request : Input.Mutation (Input.PolicyTarget × Input.PolicyDraft)) (taskSlot receiptSlot : ℕ)
    (names : Receipt.Names (Input.Mutation.operationId request) (Identity.mutation Identity.kApplyPolicy request))
    (progress : Receipt.Work) (guidance : String → Dialogue.Prompt) where
    open Worker.Model.Family excluded family pointer accepted rules intent request taskSlot using (id; tick)
    open Continue.Model.Family excluded family pointer accepted rules intent request taskSlot receiptSlot names progress guidance using (Context)
    open Context using (current; seen; valid; task; located; receipt)
    open Drain.Model.Family excluded family pointer accepted rules intent request taskSlot receiptSlot names progress guidance using (drain; Result)
    open Result using (final; context; quiet)

    module At (before : O.World) (initial : Context before) where
      run = drain before initial
      world = final run
      ctx = context run
      module Step = Batch.Model.Family.Selected excluded family pointer accepted rules intent id taskSlot (current ctx)
      module Clean = Loop.Model.Run excluded Step.selection accepted Step.intent

      module Released (released : Clean.Use.Released world) where
        module Stall = NoStall.Model.Run.At excluded Step.selection accepted Step.intent world (valid ctx) released (quiet run)
        module Unblocked (noBlocker : Stall.NoBlocker) where
          open Rest.Model.Family.At.Released.Unblocked excluded family pointer accepted rules intent request taskSlot
            world (current ctx) (seen ctx) (valid ctx) receiptSlot names progress guidance (located ctx) (receipt ctx)
            (task ctx) released (quiet run) noBlocker
            using (reply; after; finishes; outcome)

          finalTransaction : DB.execute (tick guidance) world ≡ (Worker.response reply , after)
          finalTransaction = finishes

          checkedOutcome : Outcome.Complete Step.selection accepted Step.intent world world
          checkedOutcome = outcome

        module AfterFollowup (childWorld : O.World) (childIntent : Outcome.Intent Step.selection childWorld) where
          module Child = Loop.Model.Run excluded Step.selection childWorld childIntent
          module Completed (covered : Child.Covered world) (complete : Child.Final.NoPending world) where
            module Evidence = FollowupResolution.Model.Run.At excluded Step.selection accepted Step.intent
              childWorld childIntent world (valid ctx) covered complete
            open Unblocked Evidence.noBlocker public using (finalTransaction; checkedOutcome)
