{-# OPTIONS --safe #-}
-- A finished holder's atomic release followed by actual productive cleanup.
module Muninn.ReaderReleaseCleanup where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.ReaderRelease as Release
import Muninn.CleanupResumption as Resumption
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool)
open import Data.String using (String)
open import Data.List using (List)
open import Data.Maybe using (just)
open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)
module DB = O.DB
module Exec = O.Execution

module Model where
  module M = E.Model

  module Current (selection : E.Rule) (before : O.World) (valid : O.Admissible before)
    (owner : O.Owner) (finished : ℕ) (actual : Release.ReaderAt owner finished before) where
    module Holds = Release.Model.Family selection
    module Gate = Holds.Gate
    after = DB.delete finished before
    validAfter = O.deleteUnreferencedPreservesAdmissibility finished before valid
      (Release.privateUnreferenced before owner finished valid actual)
    module Resume = Resumption.Model.Current selection after validAfter
    module Work = Resume.Work

    -- Other holders may still be using unrelated or canonical needed records.
    -- This condition concerns only records still pending in this fresh pass.
    OtherUseReleased : Set
    OtherUseReleased = ∀ key → Work.Final.Pending key after →
      (pin : M.Protected selection before key) → Gate.sourceOf pin ≡ finished

    released : OtherUseReleased → Work.Use.Released after
    released others key pending pin = Holds.notFromRemoved before finished key pin
      (trans (sym (Holds.backwardSource before finished key pin))
        (others key pending (Holds.protectedBackward before finished key pin)))

    cleanupComplete : OtherUseReleased → M.Complete selection after Resume.intent after Resume.after
    cleanupComplete others = Work.finishes validAfter (released others)

    workflow : ∀ {A : Set} → A → (O.World → A) → Exec.Script A
    workflow ready replan = Exec.atomic (Release.finish owner finished ready replan)
      (λ _ → Resume.prepend Resume.trail (Exec.done ready))

    workflowCompletes : ∀ {A : Set} (ready : A) replan →
      Exec.Completed (workflow ready replan) before ready Resume.after
    workflowCompletes ready replan = Exec.committed
      (subst (λ outcome → Exec.Completed (Resume.prepend Resume.trail (Exec.done ready))
        (proj₂ outcome) ready Resume.after)
        (sym (Release.executes owner finished ready replan before actual))
        (Resume.prependCompleted Resume.trail Exec.stop))

    savedWorkset : ∀ task taskOwner requestId ids note → DB.lookup task before ≡ just (O.recordOf taskOwner (O.cleanupWork requestId ids note)) →
      DB.lookup task Resume.after ≡ just (O.recordOf taskOwner (O.cleanupWork requestId ids note))
    savedWorkset task taskOwner requestId ids note found = Work.Pass.traceMetadata Resume.trail task _
      (trans (DB.deletePreservesOther finished task before (Release.differentFromReader before owner finished actual task _ found (λ ()))) found) refl
