{-# OPTIONS --safe #-}
-- Reconnection inspects the original receipt before restarting cleanup.
module Muninn.PolicyCleanupDatabaseResume where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.PolicyRuleAdmission as Admission
import Muninn.DatabaseResumption as Database
import Muninn.RequestAdmission as Admission
import Muninn.PolicyCleanupWorker as Worker
import Muninn.PolicyCleanupWorkerContinue as Continue
import Muninn.PolicyCleanupRetry as Retry
import Muninn.PolicyCleanupWorkerRest as Rest
import Muninn.PolicyCleanupBatch as Batch
import Muninn.CleanupLoop as Loop
import Muninn.CleanupNoStall as NoStall
import Muninn.Config as Config
import Muninn.ReceiptTypes as Receipt
import Muninn.CatalogInputs as Input
import Muninn.RequestIdentity as Identity
import Muninn.Dialogue as Dialogue
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool)
open import Data.String using (String)
open import Data.List using (List)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; cong; subst)
module Exec = O.Execution

module Protocol (Environment : Set) (Fields : List String)
  (Prerequisites : Identity.Meaning → O.World → Environment → Set)
  (Result : Identity.Meaning → Set)
  (Achieved : (subject : Identity.Meaning) → O.World → Result subject → Set) where
  module Adapter = Admission.Protocol Environment Fields Prerequisites Result Achieved
  open Database.Protocol Environment Fields Prerequisites Result Achieved using (serve; inspect; waitingResponds; resumesActive)

  module Model where
    module Outcome = E.Model
    module Family (family pointer : ℕ) (accepted : O.World) (rules : List String)
      (validRules : Admission.Entries (Data.List.map Data.String.toList rules))
      (intent : Outcome.Intent (E.rule family rules validRules) accepted)
      (request : Input.Mutation (Input.PolicyTarget × Input.PolicyDraft)) (taskSlot receiptSlot : ℕ)
      (names : Receipt.Names (Input.Mutation.operationId request) (Identity.mutation Identity.kApplyPolicy request))
      (progress : Receipt.Work) (guidance : String → Dialogue.Prompt) where
      open Worker.Model.Family family pointer accepted rules validRules intent request taskSlot using (id; meaning; owner)
      open Continue.Model.Family family pointer accepted rules validRules intent request taskSlot receiptSlot names progress guidance using (Context)
      open Context using (current; seen; valid; task; located; receipt)
      open Retry.Model.Family family pointer accepted rules validRules intent request taskSlot receiptSlot names progress guidance
        using (Run; build; script; completes; prepend; prependCompletes; prefixContext)
      open Run using (last; path; quiet) renaming (after to runAfter)

      module At (world : O.World) (ctx : Context world) (bootstrap : Config.BootstrapConfig)
        (originalIntent : String) (facts : Dialogue.Facts.Rows) (workRefs : List Input.OperationId)
        (access : Database.Access) where
        dialogue = Dialogue.context id originalIntent facts workRefs
        session = Database.session bootstrap dialogue access

        whileWaiting : serve meaning (Database.session bootstrap dialogue Database.waiting) world ≡
          (Adapter.ask (just dialogue) Database.waitingPrompt , world)
        whileWaiting = waitingResponds meaning bootstrap dialogue world

        receiptFirst : serve meaning (Database.observe Database.usable session) world ≡
          (Adapter.knownWork id meaning receiptSlot progress , world)
        receiptFirst = resumesActive meaning bootstrap dialogue access receiptSlot owner names progress world (receipt ctx)

        resumed = build world ctx
        resumedCompletes : Exec.Completed (script (path resumed)) world tt (runAfter resumed)
        resumedCompletes = completes (path resumed)

        reconnectAndRetry : Exec.Script ⊤
        reconnectAndRetry = Exec.atomic (inspect meaning dialogue) (λ _ → script (path resumed))

        reconnectAndRetryCompletes : Exec.Completed reconnectAndRetry world tt (runAfter resumed)
        reconnectAndRetryCompletes = Exec.committed
          (subst (λ initial → Exec.Completed (script (path resumed)) initial tt (runAfter resumed))
            (sym (cong proj₂ receiptFirst)) resumedCompletes)

        restartContext : ∀ {observed} → Exec.Interrupted reconnectAndRetry world observed → Context observed
        restartContext (residual , Exec.stop) = ctx
        restartContext {observed} (residual , Exec.committed prefix) = prefixContext (path resumed)
          (subst (λ initial → Exec.Prefix (script (path resumed)) initial residual observed) (cong proj₂ receiptFirst) prefix)

        retryAfterInterruption : ∀ {observed} (interruption : Exec.Interrupted reconnectAndRetry world observed) →
          Run observed (restartContext interruption)
        retryAfterInterruption {observed} interruption = build observed (restartContext interruption)

        end = runAfter resumed
        endContext = last resumed
        module Step = Batch.Model.Family.Selected family pointer accepted rules validRules intent id taskSlot (current endContext)
        module Clean = Loop.Model.Run Step.selection accepted Step.intent

        module Released (released : Clean.Use.Released end) where
          module Stall = NoStall.Model.Run.At Step.selection accepted Step.intent end (valid endContext) released (quiet resumed)
          module Unblocked (noBlocker : Stall.NoBlocker) where
            open Rest.Model.Family.At.Released.Unblocked family pointer accepted rules validRules intent request taskSlot
              end (current endContext) (seen endContext) (valid endContext) receiptSlot names progress guidance
              (located endContext) (receipt endContext) (task endContext) released (quiet resumed) noBlocker
              using (reply; after; finishes; outcome)
            open Worker.Model.Family family pointer accepted rules validRules intent request taskSlot using (tick)

            completeAfterReconnect : Exec.Script ⊤
            completeAfterReconnect = Exec.atomic (inspect meaning dialogue) (λ _ →
              prepend (path resumed) (Exec.atomic (tick guidance) (λ _ → Exec.done tt)))

            completesAfterReconnect : Exec.Completed completeAfterReconnect world tt after
            completesAfterReconnect = Exec.committed
              (subst (λ initial → Exec.Completed
                (prepend (path resumed) (Exec.atomic (tick guidance) (λ _ → Exec.done tt))) initial tt after)
                (sym (cong proj₂ receiptFirst))
                (prependCompletes (path resumed) _
                  (subst (λ final → Exec.Completed (Exec.atomic (tick guidance) (λ _ → Exec.done tt)) end tt final)
                    (cong proj₂ finishes) (Exec.committed Exec.stop))))

            checkedOutcome : Outcome.Complete Step.selection accepted Step.intent end end
            checkedOutcome = outcome
