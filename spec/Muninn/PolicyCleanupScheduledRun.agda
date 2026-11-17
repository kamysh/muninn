{-# OPTIONS --safe #-}
-- Automatic creation is followed by actual productive follow-up steps.
module Muninn.PolicyCleanupScheduledRun where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.PolicyRuleAdmission as Admission
import Muninn.CleanupDecision as Decision
import Muninn.CleanupFinalization as Finalization
import Muninn.PolicyCleanupBatch as Batch
import Muninn.PolicyCleanupWorker as Worker
import Muninn.PolicyCleanupWorkerContinue as Continue
import Muninn.PolicyCleanupScheduledContext as Scheduled
import Muninn.PolicyCleanupParentContinue as Parent
import Muninn.PolicyCleanupRetry as Retry
import Muninn.ReceiptTypes as Receipt
import Muninn.CatalogInputs as Input
import Muninn.RequestIdentity as Identity
import Muninn.Dialogue as Dialogue
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool)
open import Data.String using (String)
open import Data.List using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ; _×_; _,_; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (sym; cong; subst)
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
    open Continue.Model.Family family pointer accepted rules validRules intent request taskSlot receiptSlot names progress guidance using (Context)
    open Context using (current; task)
    module At (world : O.World) (ctx : Context world) where
      module Step = Batch.Model.Family.Selected family pointer accepted rules validRules intent id taskSlot (current ctx)
      module Task = Finalization.Model.Task Step.selection accepted Step.intent id taskSlot
      module Decisions = Decision.Model.Family.Current family pointer accepted rules validRules intent id taskSlot (current ctx)
      open Scheduled.Model.Family.At family pointer accepted rules validRules intent request taskSlot receiptSlot names progress guidance world ctx
        using (childIntent; after; next; slot; childRules; parentContext; childContext; differentTasks; capturedCoverage)
      module Blocked (quiet : Step.Pass.NoEdit world)
        (pending : Σ ℕ (λ key → Task.Final.Pending key world))
        (blocker : Σ (ℕ × O.Record) (λ row → row ∈ world × Decisions.Followup.Unscheduled row)) where
        open Scheduled.Model.Family.At.Blocked family pointer accepted rules validRules intent request taskSlot receiptSlot names progress guidance
          world ctx quiet pending blocker using (tickSchedules)
        open Retry.Model.Family family pointer after childRules (E.admitted Step.selection) childIntent request slot receiptSlot names next guidance
          using (build; Run; script; completes)
        open Run using (last; path) renaming (after to finalWorld)
        work = build after childContext
        end = finalWorld work
        nextParent = Parent.Model.Family.parentContinues family pointer accepted rules validRules intent after childRules (E.admitted Step.selection) childIntent
          request taskSlot slot receiptSlot names next guidance after parentContext childContext (path work)
        scheduleAndWork : Exec.Script ⊤
        scheduleAndWork = Exec.atomic (tick guidance) (λ _ → script (path work))
        schedulingAndWorkCompletes : Exec.Completed scheduleAndWork world tt end
        schedulingAndWorkCompletes = Exec.committed
          (subst (λ initial → Exec.Completed (script (path work)) initial tt end)
            (sym (cong proj₂ tickSchedules)) (completes (path work)))
