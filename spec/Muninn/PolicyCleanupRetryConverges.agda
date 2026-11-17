{-# OPTIONS --safe #-}
-- Interrupted worker progress plus retry reaches the full cleanup outcome.
module Muninn.PolicyCleanupRetryConverges where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.PolicyRuleAdmission as Admission
import Muninn.CleanupCompletion as Completion
import Muninn.CleanupLoop as Loop
import Muninn.CleanupNoStall as NoStall
import Muninn.CleanupOrder as Order
import Muninn.PolicyCleanupBatch as Batch
import Muninn.PolicyCleanupWorker as Worker
import Muninn.PolicyCleanupWorkerContinue as Continue
import Muninn.PolicyCleanupWorkerRest as Rest
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
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; cong; subst)
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
    module Policy = Stored.Family family pointer
    open Worker.Model.Family family pointer accepted rules validRules intent request taskSlot using (id; tick)
    open Continue.Model.Family family pointer accepted rules validRules intent request taskSlot receiptSlot names progress guidance using (Context)
    open Context using (current; seen; valid; task; located; receipt)
    open Retry.Model.Family family pointer accepted rules validRules intent request taskSlot receiptSlot names progress guidance
      using (Path; Run; build; script; prepend; prependCompletes; prefixPath; append)
    open Run using (after; last; path; quiet)
    open History.Model.Family family pointer accepted rules validRules intent request taskSlot receiptSlot names progress guidance using (canonical; intentFor; completed; trace)

    module At (before : O.World) (initial : Context before) {end lastContext}
      (original : Path before initial end lastContext) {observed}
      (interruption : Exec.Interrupted (script original) before observed) where
      reached = proj₁ (prefixPath original (proj₂ interruption))
      beforeRetry = proj₂ (prefixPath original (proj₂ interruption))
      retried = build observed reached
      finalWorld = after retried
      finalContext = last retried
      wholePath = append beforeRetry (path retried)
      module Step = Batch.Model.Family.Selected family pointer accepted rules validRules intent id taskSlot (current finalContext)
      module Clean = Loop.Model.Run Step.selection accepted Step.intent

      module Released (released : Clean.Use.Released finalWorld) where
        module Stall = NoStall.Model.Run.At Step.selection accepted Step.intent finalWorld (valid finalContext) released (quiet retried)
        module Unblocked (noBlocker : Stall.NoBlocker) where
          samePolicy = PathPolicy.Model.Family.sameRule family pointer accepted rules validRules intent request taskSlot receiptSlot names progress guidance before initial wholePath
          noPending : Completion.Model.Contract.NoPending (Policy.rule (current initial)) accepted (intentFor (Policy.rule (current initial))) finalWorld
          noPending = subst (λ selection → Completion.Model.Contract.NoPending (canonical selection) accepted (intentFor selection) finalWorld)
            samePolicy (Stall.noPending noBlocker)

          originalOutcome : Outcome.Complete (Policy.rule (current initial)) accepted (intentFor (Policy.rule (current initial))) before finalWorld
          originalOutcome = completed before initial wholePath noPending

          open Rest.Model.Family.At.Released.Unblocked family pointer accepted rules validRules intent request taskSlot
            finalWorld (current finalContext) (seen finalContext) (valid finalContext) receiptSlot names progress guidance
            (located finalContext) (receipt finalContext) (task finalContext) released (quiet retried) noBlocker
            using (finishes) renaming (after to finalAfter)

          retryAndFinish : Exec.Script ⊤
          retryAndFinish = prepend (path retried) (Exec.atomic (tick guidance) (λ _ → Exec.done tt))

          retryFinishes : Exec.Completed retryAndFinish observed tt finalAfter
          retryFinishes = prependCompletes (path retried) _
            (subst (λ end → Exec.Completed (Exec.atomic (tick guidance) (λ _ → Exec.done tt)) finalWorld tt end)
              (cong proj₂ finishes) (Exec.committed Exec.stop))

        module Covered (covered : Clean.Covered finalWorld) where
          noBlocker : Stall.NoBlocker
          noBlocker ((source , value) , present , outside , owned , remaining) = outside
            (covered source value (Order.memberLookup finalWorld source value (O.Admissible.unique (valid finalContext)) present) owned)
          open Unblocked noBlocker public using (noPending; originalOutcome; retryAndFinish; retryFinishes)

      module Start = Loop.Model.Run (Policy.rule (current initial)) accepted (intentFor (Policy.rule (current initial)))
      module InitiallyCovered (coveredBefore : Start.Covered before) where
        coveredAfter : Clean.Covered finalWorld
        coveredAfter = Start.coveredTrace (proj₂ (trace before initial wholePath)) coveredBefore
        module ReleasedAll (released : Clean.Use.Released finalWorld) where
          open Released.Covered released coveredAfter public using (noPending; originalOutcome; retryAndFinish; retryFinishes)

    module Accepted (initial : Context accepted) {end lastContext}
      (original : Path accepted initial end lastContext) {observed}
      (interruption : Exec.Interrupted (script original) accepted observed) where
      open At accepted initial original interruption
      open InitiallyCovered Start.acceptedCovered public
