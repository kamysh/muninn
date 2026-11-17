{-# OPTIONS --safe #-}
-- Actual retry paths preserve the independently specified cleanup frame.
module Muninn.PolicyCleanupRetryHistory where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.PolicyRuleAdmission as Admission
import Muninn.Config as Config
import Muninn.CleanupProgress as Progress
import Muninn.PolicyCleanupBatch as Batch
import Muninn.CleanupHistory as History
import Muninn.CleanupCompletion as Completion
import Muninn.CleanupAlignment as Alignment
import Muninn.PolicyCleanupWorker as Worker
import Muninn.PolicyCleanupWorkerTrace as WorkerTrace
import Muninn.PolicyCleanupWorkerContinue as Continue
import Muninn.PolicyCleanupStablePolicy as Stable
import Muninn.PolicyCleanupRetry as Retry
import Muninn.StoredPolicy as Stored
import Muninn.ReceiptTypes as Receipt
import Muninn.CatalogInputs as Input
import Muninn.RequestIdentity as Identity
import Muninn.Dialogue as Dialogue
open import Data.Nat using (ℕ; zero; _+_)
open import Data.Bool using (Bool)
open import Data.String using (String)
open import Data.List using (List)
open import Data.Product using (Σ; _×_; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; subst)
module DB = O.DB

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
    open Context using (current; seen; valid; task; receipt)
    open Retry.Model.Family family pointer accepted rules validRules intent request taskSlot receiptSlot names progress guidance
      using (Path; stop; step)

    canonical : E.Rule → E.Rule
    canonical selection = E.rule family (E.exclusions selection) (E.admitted selection)

    intentFor : (selection : E.Rule) → Outcome.Intent (canonical selection) accepted
    intentFor selection = record
      { keys = Outcome.Intent.keys intent
      ; uniqueBefore = Outcome.Intent.uniqueBefore intent
      ; covers = Outcome.Intent.covers intent }

    module Pass (selection : E.Rule) = Progress.Model.Pass (canonical selection) accepted (intentFor selection)

    module At (world : O.World) (ctx : Context world) where
      module Step = Batch.Model.Family.Selected family pointer accepted rules validRules intent id taskSlot (current ctx)
      after = proj₂ (DB.execute (tick guidance) world)
      next : Step.Pass.Available world → Context after
      next = Continue.Model.Family.At.next family pointer accepted rules validRules intent request taskSlot receiptSlot names progress guidance world ctx

      combine : (available : Step.Pass.Available world) {final : O.World} →
        Σ ℕ (λ count → Pass.Trace (Policy.rule (current ctx)) count world after) →
        Σ ℕ (λ count → Pass.Trace (Policy.rule (current (next available))) count after final) →
        Σ ℕ (λ count → Pass.Trace (Policy.rule (current ctx)) count world final)
      combine available (firstCount , first) (laterCount , later) = firstCount + laterCount ,
        History.Model.History.appendTrace (Policy.rule (current ctx)) accepted
          (intentFor (Policy.rule (current ctx))) first
          (subst (λ policy → Pass.Trace policy laterCount after _) (Stable.Model.Family.At.sameRule family pointer accepted rules validRules intent request taskSlot receiptSlot names progress guidance world ctx available) later)

    trace : ∀ world (ctx : Context world) {after last} → Path world ctx after last →
      Σ ℕ (λ count → Pass.Trace (Policy.rule (current ctx)) count world after)
    trace world ctx (stop .world .ctx) = zero , Pass.stop {selection = Policy.rule (current ctx)} world
    trace world ctx (step .world .ctx available rest) = At.combine world ctx available
      (WorkerTrace.Model.Family.At.tickTrace family pointer accepted rules validRules intent request taskSlot world (current ctx)
        receiptSlot names progress guidance (receipt ctx) (seen ctx) (task ctx) available)
      (trace (At.after world ctx) (At.next world ctx available) rest)

    preserves : ∀ world (ctx : Context world) {after last} (path : Path world ctx after last) →
      Outcome.Safety (Policy.rule (current ctx)) world after
    preserves world ctx path = History.Model.History.traceSafety (Policy.rule (current ctx)) accepted
      (intentFor (Policy.rule (current ctx))) (proj₂ (trace world ctx path)) (valid ctx)

    completed : ∀ world (ctx : Context world) {after last} (path : Path world ctx after last) →
      Completion.Model.Contract.NoPending (Policy.rule (current ctx)) accepted (intentFor (Policy.rule (current ctx))) after →
      Outcome.Complete (Policy.rule (current ctx)) accepted (intentFor (Policy.rule (current ctx))) world after
    completed world ctx path none = Alignment.Model.Contract.completeFromNoPending
      (Policy.rule (current ctx)) accepted (intentFor (Policy.rule (current ctx))) (proj₂ (trace world ctx path)) (valid ctx) none
