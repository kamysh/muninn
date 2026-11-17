{-# OPTIONS --safe #-}
-- Crash boundaries preserve enough existing state to restart the same worker.
module Muninn.PolicyCleanupRetry where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.PolicyRuleAdmission as Admission
import Muninn.CleanupProgress as Progress
import Muninn.PolicyCleanupBatch as Batch
import Muninn.PolicyCleanupWorker as Worker
import Muninn.PolicyCleanupWorkerProof as Proof
import Muninn.PolicyCleanupWorkerContinue as Continue
import Muninn.ReceiptTypes as Receipt
import Muninn.CatalogInputs as Input
import Muninn.RequestIdentity as Identity
import Muninn.Dialogue as Dialogue
open import Data.Nat using (ℕ; _<_)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Data.Bool using (Bool)
open import Data.String using (String)
open import Data.List using (List)
open import Data.Product using (Σ; _×_; _,_; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no)
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
    open Continue.Model.Family family pointer accepted rules validRules intent request taskSlot receiptSlot names progress guidance using (Context)
    open Context using (current; seen; task; receipt)

    module At (world : O.World) (ctx : Context world) where
      module Step = Batch.Model.Family.Selected family pointer accepted rules validRules intent id taskSlot (current ctx)
      after = proj₂ (DB.execute (tick guidance) world)
      next : Step.Pass.Available world → Context after
      next = Continue.Model.Family.At.next family pointer accepted rules validRules intent request taskSlot receiptSlot names progress guidance world ctx
      decreases : Step.Pass.Available world → Progress.mass after < Progress.mass world
      decreases = Proof.Model.Family.At.tickProgresses family pointer accepted rules validRules intent request taskSlot
        world (current ctx) receiptSlot names progress guidance (receipt ctx) (seen ctx) (task ctx)

    data Path : (before : O.World) → Context before → (after : O.World) → Context after → Set where
      stop : ∀ world (ctx : Context world) → Path world ctx world ctx
      step : ∀ world (ctx : Context world) (available : At.Step.Pass.Available world ctx world)
        {after : O.World} {last : Context after} →
        Path (At.after world ctx) (At.next world ctx available) after last → Path world ctx after last

    record Run (before : O.World) (initial : Context before) : Set where
      constructor run
      field after : O.World
            last : Context after
            path : Path before initial after last
            quiet : At.Step.Pass.NoEdit after last after

    buildWith : (world : O.World) → (ctx : Context world) → Acc _<_ (Progress.mass world) → Run world ctx
    buildWith world ctx (acc smaller) with At.Step.Pass.available? world ctx world
    ... | no none = run world ctx (stop world ctx) (At.Step.Pass.noAvailableMeansNoEdit world ctx world none)
    ... | yes available with buildWith (At.after world ctx) (At.next world ctx available) (smaller (At.decreases world ctx available))
    ...   | run after last path quiet = run after last (step world ctx available path) quiet

    build : (world : O.World) → (ctx : Context world) → Run world ctx
    build world ctx = buildWith world ctx (<-wellFounded (Progress.mass world))

    script : ∀ {before initial after last} → Path before initial after last → Exec.Script ⊤
    script (stop world ctx) = Exec.done tt
    script (step world ctx available rest) = Exec.atomic (tick guidance) (λ _ → script rest)

    completes : ∀ {before initial after last} (path : Path before initial after last) →
      Exec.Completed (script path) before tt after
    completes (stop world ctx) = Exec.stop
    completes (step world ctx available rest) = Exec.committed (completes rest)

    prepend : ∀ {before initial after last} → Path before initial after last → Exec.Script ⊤ → Exec.Script ⊤
    prepend (stop world ctx) tail = tail
    prepend (step world ctx available rest) tail = Exec.atomic (tick guidance) (λ _ → prepend rest tail)

    prependCompletes : ∀ {before initial after last final} (path : Path before initial after last) (tail : Exec.Script ⊤) →
      Exec.Completed tail after tt final → Exec.Completed (prepend path tail) before tt final
    prependCompletes (stop world ctx) tail done = done
    prependCompletes (step world ctx available rest) tail done = Exec.committed (prependCompletes rest tail done)

    prefixContext : ∀ {before initial after last residual observed}
      (path : Path before initial after last) → Exec.Prefix (script path) before residual observed → Context observed
    prefixContext (stop world ctx) Exec.stop = ctx
    prefixContext (step world ctx available rest) Exec.stop = ctx
    prefixContext (step world ctx available rest) (Exec.committed prefix) = prefixContext rest prefix

    append : ∀ {before initial middle current after last} →
      Path before initial middle current → Path middle current after last → Path before initial after last
    append (stop world ctx) later = later
    append (step world ctx available rest) later = step world ctx available (append rest later)

    prefixPath : ∀ {before initial after last residual observed}
      (path : Path before initial after last) → Exec.Prefix (script path) before residual observed →
      Σ (Context observed) (λ reached → Path before initial observed reached)
    prefixPath (stop world ctx) Exec.stop = ctx , stop world ctx
    prefixPath (step world ctx available rest) Exec.stop = ctx , stop world ctx
    prefixPath (step world ctx available rest) (Exec.committed prefix) with prefixPath rest prefix
    ... | reached , preceding = reached , step world ctx available preceding

    restartContext : ∀ {before initial after last observed} (path : Path before initial after last) →
      Exec.Interrupted (script path) before observed → Context observed
    restartContext path (residual , prefix) = prefixContext path prefix

    retry : ∀ {before initial after last observed} (path : Path before initial after last)
      (interruption : Exec.Interrupted (script path) before observed) → Run observed (restartContext path interruption)
    retry {observed = observed} path interruption = build observed (restartContext path interruption)
