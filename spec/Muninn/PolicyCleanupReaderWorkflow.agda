{-# OPTIONS --safe #-}
-- A reader release followed by the actual finite cleanup-worker transactions.
module Muninn.PolicyCleanupReaderWorkflow where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.PolicyRuleAdmission as Admission
import Muninn.ReaderRelease as Release
import Muninn.PolicyCleanupWorker as Worker
import Muninn.PolicyCleanupWorkerRun as Runs
import Muninn.PolicyCleanupWorkerDrain as Drain
import Muninn.PolicyCleanupWorkerRest as Rest
import Muninn.CleanupLoop as Loop
import Muninn.CleanupNoStall as NoStall
import Muninn.CleanupFollowupResolution as FollowupResolution
import Muninn.PolicyCleanupBatch as Batch
import Muninn.PolicyCleanupWorkerContinue as Continue
import Muninn.PolicyCleanupReaderResume as Resume
import Muninn.PolicyCleanupRetry as Retry
import Muninn.ReceiptTypes as Receipt
import Muninn.CatalogInputs as Input
import Muninn.RequestIdentity as Identity
import Muninn.Dialogue as Dialogue
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool)
open import Data.String using (String)
open import Data.List using (List)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; subst)
module DB = O.DB
module Exec = O.Execution

module Model where
  module Outcome = E.Model
  module Family (family pointer : ℕ) (accepted : O.World) (rules : List String)
    (validRules : Admission.Entries (Data.List.map Data.String.toList rules))
    (intent : Outcome.Intent (E.rule family rules validRules) accepted)
    (request : Input.Mutation (Input.PolicyTarget × Input.PolicyDraft)) (taskSlot receiptSlot : ℕ)
    (names : Receipt.Names (Input.Mutation.operationId request) (Identity.mutation Identity.kApplyPolicy request))
    (progress : Receipt.Work) (guidance : String → Dialogue.Prompt) where
    open Worker.Model.Family family pointer accepted rules validRules intent request taskSlot using (id; tick)
    open Runs.Model.Family family pointer accepted rules validRules intent request taskSlot using (Run; stop; advance; edit)
    open Continue.Model.Family family pointer accepted rules validRules intent request taskSlot receiptSlot names progress guidance using (Context)
    open Drain.Model.Family family pointer accepted rules validRules intent request taskSlot receiptSlot names progress guidance using (Result)
    open Result using (final; trace; context; quiet)
    open Context using (current; seen; valid; task; located; receipt)

    script : ∀ {count before after} → Run count before after → Exec.Script ⊤
    script (stop world) = Exec.done tt
    script (advance (edit current slot savedNames savedProgress stepGuidance found seen actual available) rest) =
      Exec.atomic (tick stepGuidance) (λ _ → script rest)

    scriptCompletes : ∀ {count before after} (run : Run count before after) →
      Exec.Completed (script run) before tt after
    scriptCompletes (stop world) = Exec.stop
    scriptCompletes (advance (edit current slot savedNames savedProgress stepGuidance found seen actual available) rest) =
      Exec.committed (scriptCompletes rest)

    prepend : ∀ {count before after} → Run count before after → Exec.Script ⊤ → Exec.Script ⊤
    prepend (stop world) tail = tail
    prepend (advance (edit current slot savedNames savedProgress stepGuidance found seen actual available) rest) tail =
      Exec.atomic (tick stepGuidance) (λ _ → prepend rest tail)

    prependCompletes : ∀ {count before after final} (run : Run count before after) (tail : Exec.Script ⊤) →
      Exec.Completed tail after tt final → Exec.Completed (prepend run tail) before tt final
    prependCompletes (stop world) tail done = done
    prependCompletes (advance (edit current slot savedNames savedProgress stepGuidance found seen actual available) rest) tail done =
      Exec.committed (prependCompletes rest tail done)

    module At (world : O.World) (ctx : Context world) (readerOwner : O.Owner) (reader : ℕ)
      (actual : Release.ReaderAt readerOwner reader world) where
      open Resume.Model.Family.At family pointer accepted rules validRules intent request taskSlot receiptSlot names progress guidance
        world ctx readerOwner reader actual using (finish; nextContext; resumed)

      workflow : Exec.Script ⊤
      workflow = Exec.atomic finish (λ _ → script (trace resumed))

      workflowCompletes : Exec.Completed workflow world tt (final resumed)
      workflowCompletes = Exec.committed (scriptCompletes (trace resumed))

      module Recover = Retry.Model.Family family pointer accepted rules validRules intent request taskSlot receiptSlot names progress guidance
      releasedWorld = Data.Product.proj₂ (DB.execute finish world)
      planned = Recover.build releasedWorld nextContext

      recoverableWorkflow : Exec.Script ⊤
      recoverableWorkflow = Exec.atomic finish (λ _ → Recover.script (Recover.Run.path planned))

      recoverableCompletes : Exec.Completed recoverableWorkflow world tt (Recover.Run.after planned)
      recoverableCompletes = Exec.committed (Recover.completes (Recover.Run.path planned))

      restartContext : ∀ {observed} → Exec.Interrupted recoverableWorkflow world observed → Context observed
      restartContext (residual , Exec.stop) = ctx
      restartContext (residual , Exec.committed prefix) = Recover.prefixContext (Recover.Run.path planned) prefix

      retryAfterInterruption : ∀ {observed} (interruption : Exec.Interrupted recoverableWorkflow world observed) →
        Recover.Run observed (restartContext interruption)
      retryAfterInterruption {observed} interruption = Recover.build observed (restartContext interruption)

      module AfterInterruption {observed : O.World} (interruption : Exec.Interrupted recoverableWorkflow world observed) where
        attempted = retryAfterInterruption interruption
        retryEnd = Recover.Run.after attempted
        retryContext = Recover.Run.last attempted
        module RetryStep = Batch.Model.Family.Selected family pointer accepted rules validRules intent id taskSlot (current retryContext)
        module RetryClean = Loop.Model.Run RetryStep.selection accepted RetryStep.intent

        module Released (released : RetryClean.Use.Released retryEnd) where
          module Stall = NoStall.Model.Run.At RetryStep.selection accepted RetryStep.intent retryEnd
            (valid retryContext) released (Recover.Run.quiet attempted)
          module Unblocked (noBlocker : Stall.NoBlocker) where
            open Rest.Model.Family.At.Released.Unblocked family pointer accepted rules validRules intent request taskSlot
              retryEnd (current retryContext) (seen retryContext) (valid retryContext) receiptSlot names progress guidance
              (located retryContext) (receipt retryContext) (task retryContext) released (Recover.Run.quiet attempted) noBlocker
              using (reply; after; finishes; outcome)

            retryWorkflow : Exec.Script ⊤
            retryWorkflow = Recover.prepend (Recover.Run.path attempted) (Exec.atomic (tick guidance) (λ _ → Exec.done tt))

            retryCompletes : Exec.Completed retryWorkflow observed tt after
            retryCompletes = Recover.prependCompletes (Recover.Run.path attempted) _
              (subst (λ final → Exec.Completed (Exec.atomic (tick guidance) (λ _ → Exec.done tt)) retryEnd tt final)
                (cong Data.Product.proj₂ finishes) (Exec.committed Exec.stop))

            retryOutcome : Outcome.Complete RetryStep.selection accepted RetryStep.intent retryEnd retryEnd
            retryOutcome = outcome

          module AfterFollowup (childWorld : O.World) (childIntent : Outcome.Intent RetryStep.selection childWorld) where
            module Child = Loop.Model.Run RetryStep.selection childWorld childIntent
            module Completed (covered : Child.Covered retryEnd) (complete : Child.Final.NoPending retryEnd) where
              module Evidence = FollowupResolution.Model.Run.At RetryStep.selection accepted RetryStep.intent
                childWorld childIntent retryEnd (valid retryContext) covered complete
              open Unblocked Evidence.noBlocker public using (retryWorkflow; retryCompletes; retryOutcome)

      end = final resumed
      endContext = context resumed
      module Step = Batch.Model.Family.Selected family pointer accepted rules validRules intent id taskSlot (current endContext)
      module Clean = Loop.Model.Run Step.selection accepted Step.intent

      module Released (released : Clean.Use.Released end) where
        module Stall = NoStall.Model.Run.At Step.selection accepted Step.intent end (valid endContext) released (quiet resumed)
        module Unblocked (noBlocker : Stall.NoBlocker) where
          open Rest.Model.Family.At.Released.Unblocked family pointer accepted rules validRules intent request taskSlot
            end (current endContext) (seen endContext) (valid endContext) receiptSlot names progress guidance
            (located endContext) (receipt endContext) (task endContext) released (quiet resumed) noBlocker
            using (reply; after; finishes; outcome)

          completeWorkflow : Exec.Script ⊤
          completeWorkflow = Exec.atomic finish (λ _ → prepend (trace resumed) (Exec.atomic (tick guidance) (λ _ → Exec.done tt)))

          completed : Exec.Completed completeWorkflow world tt after
          completed = Exec.committed (prependCompletes (trace resumed) _
            (subst (λ final → Exec.Completed (Exec.atomic (tick guidance) (λ _ → Exec.done tt)) end tt final)
              (cong Data.Product.proj₂ finishes) (Exec.committed Exec.stop)))

          checkedOutcome : Outcome.Complete Step.selection accepted Step.intent end end
          checkedOutcome = outcome
