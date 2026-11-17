{-# OPTIONS --safe #-}
-- Run a covering follow-up, then finish the parent and remaining follow-up.
module Muninn.PolicyCleanupFollowupRun where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.PolicyRuleAdmission as Admission
import Muninn.CleanupLoop as Loop
import Muninn.CleanupFinalization as Finalization
import Muninn.PolicyCleanupBatch as Batch
import Muninn.PolicyCleanupWorker as Worker
import Muninn.PolicyCleanupWorkerContinue as Continue
import Muninn.PolicyCleanupParentContinue as Parent
import Muninn.PolicyCleanupRetry as Retry
import Muninn.PolicyCleanupRetryHistory as History
import Muninn.StoredPolicy as Stored
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
open import Relation.Binary.PropositionalEquality using (_≢_)
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
    open Continue.Model.Family family pointer childAccepted childRules childValidRules childIntent request childSlot receiptSlot names progress guidance
      using () renaming (Context to ChildContext)
    open ChildContext using () renaming (current to childCurrent; valid to childValid; task to childTask)
    open Retry.Model.Family family pointer childAccepted childRules childValidRules childIntent request childSlot receiptSlot names progress guidance
      using (build; Run; script; completes)
    open Run using (last; path; quiet) renaming (after to finalWorld)
    open History.Model.Family family pointer childAccepted childRules childValidRules childIntent request childSlot receiptSlot names progress guidance using (trace; intentFor)
    module At (world : O.World) (parent : Context world) (child : ChildContext world) (distinct : taskSlot ≢ childSlot) where
      module Start = Loop.Model.Run (Policy.rule (childCurrent child)) childAccepted (intentFor (Policy.rule (childCurrent child)))
      module Captured (covered : Start.Covered world) where
        run = build world child
        end = finalWorld run
        childEnd = last run
        parentEnd = Parent.Model.Family.parentContinues family pointer accepted rules validRules intent childAccepted childRules childValidRules childIntent
          request taskSlot childSlot receiptSlot names progress guidance world parent child (path run)
        module Step = Batch.Model.Family.Selected family pointer childAccepted childRules childValidRules childIntent id childSlot (childCurrent childEnd)
        module Final = Loop.Model.Run Step.selection childAccepted Step.intent
        module FinalTask = Finalization.Model.Task Step.selection childAccepted Step.intent id childSlot
        coveredEnd : Final.Covered end
        coveredEnd = Start.coveredTrace (proj₂ (trace world child (path run))) covered
        module Released (released : Final.Use.Released end) where
          noPending : Final.Final.NoPending end
          noPending = Final.noPendingAtRest end (childValid childEnd) coveredEnd released (quiet run)
          ready : FinalTask.Ready end
          ready = childTask childEnd , noPending
          work : Exec.Script ⊤
          work = script (path run)
          workCompletes : Exec.Completed work world tt end
          workCompletes = completes (path run)
