{-# OPTIONS --safe #-}
-- Connect the actual finite cleanup pass to the shared interruption semantics.
module Muninn.ExclusionRecovery where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.CleanupLoop as Loop
import Muninn.CleanupHistory as History
import Muninn.ReaderRelease as Release
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool)
open import Data.String using (String)
open import Data.List using (List)
open import Data.Product using (Σ; _×_; _,_; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; trans; cong)
module Exec = O.Execution
module DB = O.DB

module Model (excluded : List String → String → Bool) where
  module Outcome = E.Model excluded

  module Run (selection : E.Rule) (accepted : O.World) (intent : Outcome.Intent selection accepted) where
    module Worker = Loop.Model.Run excluded selection accepted intent
    module Pass = Worker.Pass
    module Core = Worker.Core
    module Safety = History.Model.History excluded selection accepted intent

    -- The script executes exactly the transactions selected by the actual pass.
    fromTrace : ∀ {count before after} → Pass.Trace count before after → Exec.Script ⊤
    fromTrace (Pass.stop world) = Exec.done tt
    fromTrace (Pass.edit key before ready rest) = Exec.atomic (Core.transaction key) (λ _ → fromTrace rest)

    pass : O.World → Exec.Script ⊤
    pass world = fromTrace (Pass.Result.trace (Pass.run world))

    traceCompletes : ∀ {count before after} (trace : Pass.Trace count before after) →
      Exec.Completed (fromTrace trace) before tt after
    traceCompletes (Pass.stop world) = Exec.stop
    traceCompletes (Pass.edit key before ready rest) = Exec.committed (traceCompletes rest)

    -- Every crash boundary in the script corresponds to a real prefix of
    -- committed cleanup transactions; no tentative statement is published.
    prefixTrace : ∀ {count before after residual observed} (trace : Pass.Trace count before after) →
      Exec.Prefix (fromTrace trace) before residual observed → Σ ℕ (λ count → Pass.Trace count before observed)
    prefixTrace (Pass.stop before) Exec.stop = zero , Pass.stop before
    prefixTrace (Pass.edit key before ready rest) Exec.stop = zero , Pass.stop before
    prefixTrace (Pass.edit key before ready rest) (Exec.committed prefix) with prefixTrace rest prefix
    ... | count , committed = suc count , Pass.edit key before ready committed

    completedTrace : ∀ {count before after reply final} (trace : Pass.Trace count before after) →
      Exec.Completed (fromTrace trace) before reply final → final ≡ after
    completedTrace (Pass.stop world) Exec.stop = refl
    completedTrace (Pass.edit key before ready rest) (Exec.committed prefix) = completedTrace rest prefix

    terminates : ∀ world → Exec.Completed (pass world) world tt (Pass.Result.after (Pass.run world))
    terminates world = traceCompletes (Pass.Result.trace (Pass.run world))

    interruptedSafe : ∀ observed → O.Admissible accepted → Exec.Interrupted (pass accepted) accepted observed →
      Outcome.Safety selection accepted observed
    interruptedSafe observed valid (residual , prefix) with prefixTrace (Pass.Result.trace (Pass.run accepted)) prefix
    ... | count , trace = Safety.traceSafety trace valid

    -- Once temporary holders have released the captured records, a retry
    -- after any transaction boundary reaches the independently fixed outcome.
    converges : ∀ observed reply final → O.Admissible accepted → Worker.Use.Released accepted →
      Exec.Interrupted (pass accepted) accepted observed → Exec.Completed (pass observed) observed reply final →
      Outcome.Complete selection accepted intent accepted final
    converges observed reply final valid released (residual , prefix) completed
      with prefixTrace (Pass.Result.trace (Pass.run accepted)) prefix
    ... | count , trace = subst (Outcome.Complete selection accepted intent accepted)
      (sym (completedTrace (Pass.Result.trace (Pass.run observed)) completed))
      (Worker.resumes trace valid released)

    -- After a holder finishes, the original fixed workset remains in force.
    -- A subsequent pass reassesses the current store, rather than restoring
    -- a cursor or assuming that cleanup has already completed.
    coveredAfterReader : ∀ world reader → Worker.Covered world → Worker.Covered (DB.delete reader world)
    coveredAfterReader world reader covered key value found owned =
      covered key value (Release.lookupBeforeDelete world reader key value found) owned

    afterWaitConverges : ∀ observed reply final → O.Admissible observed → Worker.Covered observed →
      Worker.Use.Released observed → Exec.Completed (pass observed) observed reply final →
      Outcome.Complete selection accepted intent observed final
    afterWaitConverges observed reply final valid covered released completed =
      subst (Outcome.Complete selection accepted intent observed)
        (sym (completedTrace (Pass.Result.trace (Pass.run observed)) completed))
        (Worker.completeTrace (Pass.Result.trace (Pass.run observed)) valid covered released (Pass.Result.noEdit (Pass.run observed)))

    readerReleaseThenRetry : ∀ world reader readerOwner reply final → O.Admissible world → Worker.Covered world →
      Release.ReaderAt readerOwner reader world → Worker.Use.Released (DB.delete reader world) →
      Exec.Completed (pass (DB.delete reader world)) (DB.delete reader world) reply final →
      Outcome.Complete selection accepted intent (DB.delete reader world) final
    readerReleaseThenRetry world reader readerOwner reply final valid covered actual released completed =
      afterWaitConverges (DB.delete reader world) reply final
        (O.deleteUnreferencedPreservesAdmissibility reader world valid (Release.privateUnreferenced world readerOwner reader valid actual))
        (coveredAfterReader world reader covered) released completed

    interruptedThenReaderRelease : ∀ observed reader readerOwner reply final →
      O.Admissible accepted → Exec.Interrupted (pass accepted) accepted observed →
      Release.ReaderAt readerOwner reader observed → Worker.Use.Released (DB.delete reader observed) →
      Exec.Completed (pass (DB.delete reader observed)) (DB.delete reader observed) reply final →
      Outcome.Safety selection accepted observed ×
      Outcome.Complete selection accepted intent (DB.delete reader observed) final
    interruptedThenReaderRelease observed reader readerOwner reply final valid (residual , prefix) actual released completed
      with prefixTrace (Pass.Result.trace (Pass.run accepted)) prefix
    ... | count , trace = Safety.traceSafety trace valid ,
      readerReleaseThenRetry observed reader readerOwner reply final
        (Pass.traceAdmissible trace valid) (Worker.coveredTrace trace Worker.acceptedCovered) actual released completed

    -- The release is the existing atomic operation, followed by the same
    -- cleanup pass; no separate recovery record or restart of Muninn is used.
    releaseAndRetry : ∀ world reader readerOwner reply final →
      Release.ReaderAt readerOwner reader world →
      Exec.Completed (pass (DB.delete reader world)) (DB.delete reader world) reply final →
      Exec.Completed
        (Exec.atomic (Release.finish readerOwner reader tt (λ _ → tt)) (λ _ → pass (DB.delete reader world)))
        world reply final
    releaseAndRetry world reader readerOwner reply final actual completed = Exec.committed
      (subst (λ outcome → Exec.Completed (pass (DB.delete reader world)) (proj₂ outcome) reply final)
        (sym (Release.executes readerOwner reader tt (λ _ → tt) world actual)) completed)
