{-# OPTIONS --safe #-}
-- A resumed covering follow-up completes after its remaining holders release.
module Muninn.PolicyCleanupChildCompletion where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.PolicyRuleAdmission as Admission
import Muninn.CleanupCompletion as Completion
import Muninn.CleanupFinalization as Finalization
import Muninn.CleanupLoop as Loop
import Muninn.PolicyCleanupBatch as Batch
import Muninn.PolicyCleanupWorker as Worker
import Muninn.PolicyCleanupWorkerContinue as Continue
import Muninn.PolicyCleanupWorkerFinish as Finish
import Muninn.PolicyCleanupChildResume as Resume
import Muninn.PolicyCleanupAfterFollowup as Handoff
import Muninn.PolicyCleanupRetry as Retry
import Muninn.PolicyCleanupRetryHistory as History
import Muninn.PolicyCleanupPathPolicy as PathPolicy
import Muninn.StoredPolicy as Stored
import Muninn.ReceiptTypes as Receipt
import Muninn.CatalogInputs as Input
import Muninn.RequestIdentity as Identity
import Muninn.Dialogue as Dialogue
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool)
open import Data.String using (String)
open import Data.List using (List)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≢_; sym; cong; subst)

module Exec = O.Execution

module Model where
  module Outcome = E.Model
  module Family (family pointer : ℕ) (accepted : O.World) (rules : List String)
    (validRules : Admission.Entries (Data.List.map Data.String.toList rules))
    (intent : Outcome.Intent (E.rule family rules validRules) accepted)
    (childAccepted : O.World) (childRules : List String)
    (childValidRules : Admission.Entries (Data.List.map Data.String.toList childRules))
    (childIntent : Outcome.Intent (E.rule family childRules childValidRules) childAccepted)
    (request : Input.Mutation (Input.PolicyTarget × Input.PolicyDraft))
    (taskSlot childSlot receiptSlot : ℕ)
    (names : Receipt.Names (Input.Mutation.operationId request) (Identity.mutation Identity.kApplyPolicy request))
    (progress : Receipt.Work) (guidance : String → Dialogue.Prompt) where
    open Worker.Model.Family family pointer accepted rules validRules intent request taskSlot using (id)
    open Continue.Model.Family family pointer accepted rules validRules intent request taskSlot receiptSlot names progress guidance using (Context)
    open Context using (current)
    module At (world : O.World) (ctx : Context world) (distinct : taskSlot ≢ childSlot) where
      module ChildStep = Batch.Model.Family.Selected family pointer childAccepted childRules childValidRules childIntent id childSlot (current ctx)
      module Child = Finalization.Model.Task ChildStep.selection childAccepted ChildStep.intent id childSlot
      module ChildLoop = Loop.Model.Run ChildStep.selection childAccepted ChildStep.intent
      module Completed (ready : Child.Ready world) (quiet : ChildStep.Pass.NoEdit world) (covered : ChildLoop.Covered world) where
        open Resume.Model.Family.At.Completed family pointer accepted rules validRules intent childAccepted childRules childValidRules childIntent
          request taskSlot childSlot receiptSlot names progress guidance world ctx distinct ready quiet covered
          using (after; nextContext; nextProgress; capturedAfter)
        module Policy = Stored.Family family pointer
        open Continue.Model.Family family pointer childAccepted childRules childValidRules childIntent request childSlot receiptSlot names nextProgress guidance
          using () renaming (Context to ChildContext)
        open ChildContext using () renaming (current to childCurrent; seen to childSeen; valid to childValid; task to childTask; located to childLocated; receipt to childReceipt)
        open Retry.Model.Family family pointer childAccepted childRules childValidRules childIntent request childSlot receiptSlot names nextProgress guidance using (build; Run; prepend; prependCompletes)
        open Run using (last; path) renaming (after to finalWorld; quiet to finalQuiet)
        resumed = build after nextContext
        finalContext = last resumed
        module Start = Loop.Model.Run (Policy.rule (childCurrent nextContext)) childAccepted
          (History.Model.Family.intentFor family pointer childAccepted childRules childValidRules childIntent request childSlot receiptSlot names nextProgress guidance (Policy.rule (childCurrent nextContext)))
        module Step = Batch.Model.Family.Selected family pointer childAccepted childRules childValidRules childIntent id childSlot (childCurrent finalContext)
        module Final = Loop.Model.Run Step.selection childAccepted Step.intent
        module FinalTask = Finalization.Model.Task Step.selection childAccepted Step.intent id childSlot
        trail = History.Model.Family.trace family pointer childAccepted childRules childValidRules childIntent request childSlot receiptSlot names nextProgress guidance
          after nextContext (path resumed)
        finalCovered : Final.Covered (finalWorld resumed)
        finalCovered = Start.coveredTrace (proj₂ trail) capturedAfter
        module Released (released : Final.Use.Released (finalWorld resumed)) where
          none : Final.Final.NoPending (finalWorld resumed)
          none = Final.noPendingAtRest (finalWorld resumed) (childValid finalContext) finalCovered released (finalQuiet resumed)
          readyToFinish : FinalTask.Ready (finalWorld resumed)
          readyToFinish = childTask finalContext , none
          open Finish.Model.Family.At.Verified family pointer childAccepted childRules childValidRules childIntent request childSlot
            (finalWorld resumed) (childCurrent finalContext) (childSeen finalContext) (childValid finalContext)
            receiptSlot names nextProgress guidance (childLocated finalContext) (childReceipt finalContext) readyToFinish (finalQuiet resumed)
            public using (reply; tickFinishes) renaming (after to resultWorld)

          open Handoff.Model.Family.At.Completed.ParentCanFinish family pointer accepted rules validRules intent childAccepted childRules childValidRules childIntent
            request taskSlot childSlot receiptSlot names progress guidance world ctx distinct ready quiet covered
            using () renaming (tickFinishes to parentFinishes)
          open Worker.Model.Family family pointer accepted rules validRules intent request taskSlot using () renaming (tick to parentTick)
          open Worker.Model.Family family pointer childAccepted childRules childValidRules childIntent request childSlot using () renaming (tick to childTick)

          finishBoth : Exec.Script ⊤
          finishBoth = Exec.atomic (parentTick guidance) (λ _ →
            prepend (path resumed) (Exec.atomic (childTick guidance) (λ _ → Exec.done tt)))

          bothFinish : Exec.Completed finishBoth world tt resultWorld
          bothFinish = Exec.committed
            (subst (λ initial → Exec.Completed
              (prepend (path resumed) (Exec.atomic (childTick guidance) (λ _ → Exec.done tt))) initial tt resultWorld)
              (sym (cong proj₂ parentFinishes))
              (prependCompletes (path resumed) _
                (subst (λ final → Exec.Completed (Exec.atomic (childTick guidance) (λ _ → Exec.done tt)) (finalWorld resumed) tt final)
                  (cong proj₂ tickFinishes) (Exec.committed Exec.stop))))
