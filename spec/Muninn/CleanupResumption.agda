{-# OPTIONS --safe #-}
-- Productive cleanup followed by admission of the original request's reader.
module Muninn.CleanupResumption where

import Muninn.OwnedState as O
import Muninn.Catalog as Catalog
import Muninn.ExclusionOutcomes as E
import Muninn.ExclusionClassifier as Classifier
import Muninn.CleanupLoop as Loop
import Muninn.CleanupAdmission as Admission
import Muninn.CleanupAdmissionStorage as Insert
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool)
open import Data.String using (String)
open import Data.List using (List)
open import Data.Maybe using (just)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
module DB = O.DB
module Exec = O.Execution

module Model (excluded : List String → String → Bool) where
  module M = E.Model excluded

  module Current (selection : E.Rule) (before : O.World) (valid : O.Admissible before) where
    intent : M.Intent selection before
    intent = M.captureIntent selection before (O.Admissible.unique valid)
    module Work = Loop.Model.Run excluded selection before intent
    module Gate = Admission.Model.Family excluded selection

    result = Work.Pass.run before
    after = Work.Pass.Result.after result
    trail = Work.Pass.Result.trace result
    validAfter = Work.Pass.traceAdmissible trail valid
    coveredAfter = Work.coveredTrace trail Work.acceptedCovered

    noPending : Work.Use.Released before → Work.Final.NoPending after
    noPending released = Work.noPendingAtRest after validAfter coveredAfter
      (Work.Use.releasedTrace trail valid released) (Work.Pass.Result.noEdit result)

    -- The fresh capture covers every remaining family row, including rows
    -- tracked by older saved cleanup tasks. Their claim lists stay unchanged.
    noFence : Work.Use.Released before → ∀ key → ¬ Gate.Pending after key
    noFence released key (claimed , value , found , owned , indexed , inj₁ unneeded) =
      noPending released key (value , found , coveredAfter key value found owned , owned , indexed , inj₁ unneeded)
    noFence released key (claimed , value , found , owned , indexed , inj₂ noncanonical)
      with Classifier.Model.Assessment.needed? excluded selection after key
    ... | yes needed = noncanonical (Work.canonicalAtRest after key value
      (Work.Use.releasedTrace trail valid released) (Work.Pass.Result.noEdit result)
      found (coveredAfter key value found owned) needed)
    ... | no unneeded = noPending released key
      (value , found , coveredAfter key value found owned , owned , indexed , inj₁ unneeded)

    allowed : Work.Use.Released before → ∀ slot refs payload → Gate.Allowed after slot refs payload
    allowed released slot refs payload key pending reached = noFence released key pending

    admitsCurrent : ∀ {A : Set} (request : Catalog.Request) slot refs payload
      (ready : Catalog.Request → ℕ → A) (replan : Catalog.Request → O.World → A) →
      Work.Use.Released before → Insert.Fresh after slot → Gate.Resolved after refs →
      Gate.Clean (Gate.proposed after slot refs payload) refs →
      DB.execute (Gate.admit slot refs payload (ready request) (replan request)) after ≡
        (ready request slot , Gate.proposed after slot refs payload)
    admitsCurrent request slot refs payload ready replan released fresh resolved clean =
      Gate.accepts slot refs payload (ready request) (replan request) after fresh resolved clean
        (allowed released slot refs payload)

    prepend : ∀ {A : Set} {count start finish} → Work.Pass.Trace count start finish →
      Exec.Script A → Exec.Script A
    prepend (Work.Pass.stop world) suffix = suffix
    prepend (Work.Pass.edit key world eligible later) suffix =
      Exec.atomic (Work.Core.transaction key) (λ _ → prepend later suffix)

    prependCompleted : ∀ {A : Set} {count start finish final reply} (trace : Work.Pass.Trace count start finish)
      {suffix : Exec.Script A} → Exec.Completed suffix finish reply final →
      Exec.Completed (prepend trace suffix) start reply final
    prependCompleted (Work.Pass.stop world) completed = completed
    prependCompleted (Work.Pass.edit key world eligible later) completed =
      Exec.committed (prependCompleted later completed)

    -- Both continuation callbacks receive the same original catalog request.
    workflow : ∀ {A : Set} → Catalog.Request → ℕ → List O.Reference → String →
      (Catalog.Request → ℕ → A) → (Catalog.Request → O.World → A) → Exec.Script A
    workflow request slot refs payload ready replan = prepend trail
      (Exec.atomic (Gate.admit slot refs payload (ready request) (replan request)) Exec.done)

    readerCompletes : ∀ {A : Set} (request : Catalog.Request) slot refs payload
      (ready : Catalog.Request → ℕ → A) (replan : Catalog.Request → O.World → A) →
      Work.Use.Released before → Insert.Fresh after slot → Gate.Resolved after refs →
      Gate.Clean (Gate.proposed after slot refs payload) refs →
      Exec.Completed (Exec.atomic (Gate.admit slot refs payload (ready request) (replan request)) Exec.done)
        after (ready request slot) (Gate.proposed after slot refs payload)
    readerCompletes request slot refs payload ready replan released fresh resolved clean =
      subst (λ outcome → Exec.Completed
        (Exec.atomic (Gate.admit slot refs payload (ready request) (replan request)) Exec.done)
        after (proj₁ outcome) (proj₂ outcome))
        (admitsCurrent request slot refs payload ready replan released fresh resolved clean)
        (Exec.committed Exec.stop)

    finishes : ∀ {A : Set} (request : Catalog.Request) slot refs payload
      (ready : Catalog.Request → ℕ → A) (replan : Catalog.Request → O.World → A) →
      Work.Use.Released before → Insert.Fresh after slot → Gate.Resolved after refs →
      Gate.Clean (Gate.proposed after slot refs payload) refs →
      Exec.Completed (workflow request slot refs payload ready replan)
        before (ready request slot) (Gate.proposed after slot refs payload)
    finishes request slot refs payload ready replan released fresh resolved clean =
      prependCompleted trail (readerCompletes request slot refs payload ready replan released fresh resolved clean)

    savedWorkset : ∀ {A : Set} (request : Catalog.Request) slot refs payload
      (ready : Catalog.Request → ℕ → A) (replan : Catalog.Request → O.World → A) task ids note →
      DB.lookup task before ≡ just (O.recordOf (E.targetOwner selection) (O.cleanupWork ids note)) →
      DB.lookup task (proj₂ (DB.execute (Gate.admit slot refs payload (ready request) (replan request)) after)) ≡
        just (O.recordOf (E.targetOwner selection) (O.cleanupWork ids note))
    savedWorkset request slot refs payload ready replan task ids note found =
      Gate.savedWorkset slot refs payload (ready request) (replan request) after task ids note
        (Work.Pass.traceMetadata trail task _ found refl)
