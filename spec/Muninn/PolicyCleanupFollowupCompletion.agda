{-# OPTIONS --safe #-}
-- A completed follow-up continues through the original worker final transaction.
module Muninn.PolicyCleanupFollowupCompletion where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.PolicyRuleAdmission as Admission
import Muninn.PolicyCleanupAfterFollowup as Followup
import Muninn.PolicyCleanupRetry as Retry
import Muninn.PolicyCleanupWorker as Worker
import Muninn.PolicyCleanupWorkerContinue as Continue
import Muninn.PolicyCleanupWorkerRest as Rest
import Muninn.CleanupLoop as Loop
import Muninn.CleanupNoStall as NoStall
import Muninn.PolicyCleanupBatch as Batch
import Muninn.StoredPolicy as Stored
import Muninn.CleanupFinalization as Finalization
import Muninn.ReceiptTypes as Receipt
import Muninn.CatalogInputs as Input
import Muninn.RequestIdentity as Identity
import Muninn.Dialogue as Dialogue
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool)
open import Data.String using (String)
open import Data.List using (List)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≢_; sym; cong; subst)
module DB = O.DB
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
    module Policy = Stored.Family family pointer
    open Worker.Model.Family family pointer accepted rules validRules intent request taskSlot using (id)
    open Continue.Model.Family family pointer accepted rules validRules intent request taskSlot receiptSlot names progress guidance using (Context)
    open Context using (current)

    module At (world : O.World) (ctx : Context world) (distinct : taskSlot ≢ childSlot) where
      module ChildStep = Batch.Model.Family.Selected family pointer childAccepted childRules childValidRules childIntent id childSlot (current ctx)
      module Child = Finalization.Model.Task ChildStep.selection childAccepted ChildStep.intent id childSlot

      module Completed (ready : Child.Ready world) (quiet : ChildStep.Pass.NoEdit world) where
        open Followup.Model.Family.At.Completed family pointer accepted rules validRules intent childAccepted childRules childValidRules childIntent
          request taskSlot childSlot receiptSlot names progress guidance world ctx distinct ready quiet
          using (nextProgress; after; nextContext; childTick; tickFinishes)
        module ParentRetry = Retry.Model.Family family pointer accepted rules validRules intent request taskSlot receiptSlot names nextProgress guidance
        resumed = ParentRetry.build after nextContext
        open Continue.Model.Family family pointer accepted rules validRules intent request taskSlot receiptSlot names nextProgress guidance
          using () renaming (Context to ParentContext)
        open ParentContext using () renaming
          (current to parentCurrent; seen to parentSeen; valid to parentValid; task to parentTask; located to parentLocated; receipt to parentReceipt)
        open Worker.Model.Family family pointer accepted rules validRules intent request taskSlot using () renaming (tick to parentTick)
        parentEnd = ParentRetry.Run.after resumed
        parentCtx = ParentRetry.Run.last resumed
        module ParentStep = Batch.Model.Family.Selected family pointer accepted rules validRules intent id taskSlot (parentCurrent parentCtx)
        module Clean = Loop.Model.Run ParentStep.selection accepted ParentStep.intent

        module Released (released : Clean.Use.Released parentEnd) where
          module Stall = NoStall.Model.Run.At ParentStep.selection accepted ParentStep.intent parentEnd
            (parentValid parentCtx) released (ParentRetry.Run.quiet resumed)
          module Unblocked (noBlocker : Stall.NoBlocker) where
            open Rest.Model.Family.At.Released.Unblocked family pointer accepted rules validRules intent request taskSlot
              parentEnd (parentCurrent parentCtx) (parentSeen parentCtx) (parentValid parentCtx) receiptSlot names nextProgress guidance
              (parentLocated parentCtx) (parentReceipt parentCtx) (parentTask parentCtx) released (ParentRetry.Run.quiet resumed) noBlocker
              using (finishes; outcome) renaming (after to finalAfter)

            finishAfterFollowup : Exec.Script ⊤
            finishAfterFollowup = Exec.atomic (childTick guidance) (λ _ →
              ParentRetry.prepend (ParentRetry.Run.path resumed) (Exec.atomic (parentTick guidance) (λ _ → Exec.done tt)))

            finishesAfterFollowup : Exec.Completed finishAfterFollowup world tt finalAfter
            finishesAfterFollowup = Exec.committed
              (subst (λ initial → Exec.Completed
                (ParentRetry.prepend (ParentRetry.Run.path resumed) (Exec.atomic (parentTick guidance) (λ _ → Exec.done tt))) initial tt finalAfter)
                (sym (cong proj₂ tickFinishes))
                (ParentRetry.prependCompletes (ParentRetry.Run.path resumed) _
                  (subst (λ final → Exec.Completed (Exec.atomic (parentTick guidance) (λ _ → Exec.done tt)) parentEnd tt final)
                    (cong proj₂ finishes) (Exec.committed Exec.stop))))

            checkedBeforeFinalization : Outcome.Complete ParentStep.selection accepted ParentStep.intent parentEnd parentEnd
            checkedBeforeFinalization = outcome
