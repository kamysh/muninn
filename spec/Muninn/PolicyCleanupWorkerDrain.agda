{-# OPTIONS --safe #-}
-- Repeated actual worker transactions reach a quiet state in finite time.
module Muninn.PolicyCleanupWorkerDrain where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.CleanupProgress as Progress
import Muninn.PolicyCleanupBatch as Batch
import Muninn.PolicyCleanupWorker as Worker
import Muninn.PolicyCleanupWorkerProof as Proof
import Muninn.PolicyCleanupWorkerRun as Runs
import Muninn.PolicyCleanupWorkerContinue as Continue
import Muninn.ReceiptTypes as Receipt
import Muninn.CatalogInputs as Input
import Muninn.RequestIdentity as Identity
import Muninn.Dialogue as Dialogue
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Data.Bool using (Bool)
open import Data.String using (String)
open import Data.List using (List)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; proj₂)
open import Relation.Nullary using (yes; no)
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
    open Context using (current; seen; valid; task; receipt)
    open Runs.Model.Family excluded family pointer accepted rules intent request taskSlot using (Run; stop; advance; edit)

    module At (world : O.World) (ctx : Context world) where
      module Step = Batch.Model.Family.Selected excluded family pointer accepted rules intent id taskSlot (current ctx)

    record Result (before : O.World) : Set where
      constructor result
      field final : O.World
            context : Context final
            count : ℕ
            trace : Run count before final
            quiet : At.Step.Pass.NoEdit final context final

    drainWith : (world : O.World) → Context world → Acc _<_ (Progress.mass world) → Result world
    drainWith world ctx (acc smaller) with At.Step.Pass.available? world ctx world
    ... | no none = result world ctx zero (stop world) (At.Step.Pass.noAvailableMeansNoEdit world ctx world none)
    ... | yes available with drainWith (proj₂ (DB.execute (tick guidance) world))
      (Continue.Model.Family.At.next excluded family pointer accepted rules intent request taskSlot receiptSlot names progress guidance world ctx available)
      (smaller (Proof.Model.Family.At.tickProgresses excluded family pointer accepted rules intent request taskSlot
        world (current ctx) receiptSlot names progress guidance (receipt ctx) (seen ctx) (task ctx) available))
    ...   | result final nextCtx count trace quiet = result final nextCtx (suc count)
      (advance (edit (current ctx) receiptSlot names progress guidance (receipt ctx) (seen ctx) (task ctx) available) trace) quiet

    drain : (world : O.World) → Context world → Result world
    drain world ctx = drainWith world ctx (<-wellFounded (Progress.mass world))
