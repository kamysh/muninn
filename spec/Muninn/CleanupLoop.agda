{-# OPTIONS --safe #-}
-- The executable cleanup pass reaches the existing completion contract.
module Muninn.CleanupLoop where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.ExclusionClassifier as Classifier
import Muninn.CleanupEffects as Effects
import Muninn.CleanupProgress as Progress
import Muninn.CleanupCompletion as Completion
import Muninn.CleanupAlignment as Alignment
import Muninn.CleanupReleased as Released
import Muninn.CleanupObservations as Observations
import Muninn.CleanupOrder as Order
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false)
open import Data.String using (String)
open import Data.List using (List)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
module DB = O.DB

module Model (excluded : List String → String → Bool) where
  module M = E.Model excluded
  module Assessment = Classifier.Model excluded

  module Run (selection : E.Rule) (accepted : O.World) (intent : M.Intent selection accepted) where
    module Pass = Progress.Model.Pass excluded selection accepted intent
    module Core = Effects.Model.Core excluded selection accepted intent
    module Final = Completion.Model.Contract excluded selection accepted intent
    module Aligned = Alignment.Model.Contract excluded selection accepted intent
    module Use = Released.Model.Loop excluded selection accepted intent

    Covered : O.World → Set
    Covered world = ∀ key value → DB.lookup key world ≡ just value → O.owner value ≡ E.targetOwner selection → key ∈ M.Intent.keys intent

    acceptedCovered : Covered accepted
    acceptedCovered key value found owned = M.Intent.covers intent key value (Observations.lookupMember accepted key value found) owned

    coveredTrace : ∀ {count before after} → Pass.Trace count before after → Covered before → Covered after
    coveredTrace trail covered key value found owned with Aligned.traceAncestor trail key value found
    ... | Aligned.ancestor original first owner role = covered key original first (trans (sym owner) owned)

    controlRooted : ∀ world role → E.indexedRole role ≡ false → M.rootedRole selection world role ≡ true
    controlRooted world E.administrative proof = refl
    controlRooted world E.holder proof = refl
    controlRooted world E.artifact ()
    controlRooted world E.baselineAnchor ()
    controlRooted world (E.baselineBinding _) ()
    controlRooted world (E.checkoutBinding _ _) ()
    controlRooted world (E.snapshot _) ()
    controlRooted world (E.legacyFile _) ()
    controlRooted world (E.graphContainer _ _) ()
    controlRooted world (E.attached _ _) ()

    unneededIndexed : ∀ world key value → DB.lookup key world ≡ just value → ¬ M.Needed selection world key → E.indexed value ≡ true
    unneededIndexed world key value found unneeded with E.indexed value in indexed
    ... | true = refl
    ... | false = ⊥-elim (unneeded (M.root key value found rooted))
      where
      rooted : M.rooted selection world value ≡ true
      rooted with E.ownerEqual (O.owner value) (E.targetOwner selection)
      ... | yes same = controlRooted world (E.classify (O.body value)) indexed
      ... | no different = refl

    canonicalAtRest : ∀ world key value → Use.Released world → Pass.NoEdit world → DB.lookup key world ≡ just value →
      key ∈ M.Intent.keys intent → M.Needed selection world key → M.project selection world value ≡ value
    canonicalAtRest world key value released quiet found captured needed with Final.projectionView world value
    ... | inj₁ canonical = canonical
    ... | inj₂ (owned , indexed , changed) = ⊥-elim (quiet key
      (inj₂ (value , found , captured , owned , indexed , needed , released key pending , changed)))
      where pending = value , found , captured , owned , indexed , inj₂ (needed , changed)

    referenceUse : ∀ world value ref → ref ∈ O.references (O.body value) → M.project selection world value ≡ value →
      (ref ∈ M.referencesFor M.permanent selection world value) ⊎ (ref ∈ M.heldReferences value)
    referenceUse world value ref included exact with E.classify (O.body value)
    ... | E.administrative = inj₁ (subst (λ v → ref ∈ O.references (O.body v)) (sym exact) included)
    ... | E.artifact = inj₁ (subst (λ v → ref ∈ O.references (O.body v)) (sym exact) included)
    ... | E.baselineAnchor = inj₁ (subst (λ v → ref ∈ O.references (O.body v)) (sym exact) included)
    ... | E.baselineBinding path = inj₁ (subst (λ v → ref ∈ O.references (O.body v)) (sym exact) included)
    ... | E.checkoutBinding selected path = inj₁ (subst (λ v → ref ∈ O.references (O.body v)) (sym exact) included)
    ... | E.snapshot selected = inj₁ (subst (λ v → ref ∈ O.references (O.body v)) (sym exact) included)
    ... | E.legacyFile path = inj₁ (subst (λ v → ref ∈ O.references (O.body v)) (sym exact) included)
    ... | E.graphContainer selected inUse = inj₁ (subst (λ v → ref ∈ O.references (O.body v)) (sym exact) included)
    ... | E.attached parent gate = inj₁ (subst (λ v → ref ∈ O.references (O.body v)) (sym exact) included)
    ... | E.holder = inj₂ included

    referenceNeed : ∀ world source value ref → DB.lookup source world ≡ just value →
      ref ∈ O.references (O.body value) → O.Resolves world (O.owner value) ref →
      M.Needed selection world source → M.project selection world value ≡ value →
      M.Needed selection world (O.target ref) ⊎ M.Protected selection world (O.target ref)
    referenceNeed world source value ref found included resolved needed canonical with referenceUse world value ref included canonical
    ... | inj₁ permanent = inj₁ (M.required needed (M.reference source value ref found permanent resolved))
    ... | inj₂ held = inj₂ (M.held source value ref found held resolved)

    sourceCandidate : ∀ world key → O.Admissible world → Covered world → Use.Released world → Pass.NoEdit world →
      Final.Candidate key world → (incoming : Completion.Incoming key world) → Final.Candidate (Completion.incomingSource incoming) world
    sourceCandidate world key valid covered released quiet (target , targetFound , captured , owned , indexed , unneeded , unprotected)
      incoming@((source , value) , present , ref , included , refl)
      with Assessment.Assessment.needed? selection world source
    ... | no sourceUnneeded = value , sourceFound , sourceCaptured , sourceOwned , unneededIndexed world source value sourceFound sourceUnneeded , sourceUnneeded , sourceUnprotected
      where
      sourceFound = Order.memberLookup world source value (O.Admissible.unique valid) present
      resolved = All.lookup (All.lookup (O.Admissible.sound valid) present) included
      targetSame = just-injective (trans (sym (O.Resolves.found resolved)) targetFound)
      sourceOwned = Completion.familyReferenceOwner (O.owner value) (O.owner (O.Resolves.value resolved)) (E.family selection)
        (O.Resolves.rightOwner resolved) (trans (cong O.owner targetSame) owned)
      sourceCaptured = covered source value sourceFound sourceOwned
      sourceUnprotected : ¬ M.Protected selection world source
      sourceUnprotected protected = unprotected (M.requireReference source value ref protected sourceFound included resolved)
    ... | yes sourceNeeded = ⊥-elim (Data.Sum.[ unneeded , unprotected ]
      (referenceNeed world source value ref sourceFound included resolved sourceNeeded
        (canonicalAtRest world source value released quiet sourceFound sourceCaptured sourceNeeded)))
      where
      sourceFound = Order.memberLookup world source value (O.Admissible.unique valid) present
      resolved = All.lookup (All.lookup (O.Admissible.sound valid) present) included
      targetSame = just-injective (trans (sym (O.Resolves.found resolved)) targetFound)
      sourceOwned = Completion.familyReferenceOwner (O.owner value) (O.owner (O.Resolves.value resolved)) (E.family selection)
        (O.Resolves.rightOwner resolved) (trans (cong O.owner targetSame) owned)
      sourceCaptured = covered source value sourceFound sourceOwned

    noPendingAtRest : ∀ world → O.Admissible world → Covered world → Use.Released world → Pass.NoEdit world → Final.NoPending world
    noPendingAtRest world valid covered released quiet key pending@(value , found , captured , owned , indexed , remaining) with remaining
    ... | inj₂ (needed , changed) = quiet key (inj₂ (value , found , captured , owned , indexed , needed , released key pending , changed))
    ... | inj₁ unneeded with Final.closedComponentProgress world (Final.candidates world) key valid
      (Final.candidatesComplete world key candidate) (λ chosen present → Final.candidatesSound world chosen present)
      (λ chosen present incoming → Final.candidatesComplete world (Completion.incomingSource incoming)
        (sourceCandidate world chosen valid covered released quiet (Final.candidatesSound world chosen present) incoming))
      where candidate = value , found , captured , owned , indexed , unneeded , released key pending
    ...   | chosen , present , ready = quiet chosen (inj₁ ready)

    completeTrace : ∀ {count before after} → Pass.Trace count before after → O.Admissible before → Covered before →
      Use.Released before → Pass.NoEdit after → M.Complete selection accepted intent before after
    completeTrace {after = after} trail valid covered released quiet = Aligned.completeFromNoPending trail valid
      (noPendingAtRest after (Pass.traceAdmissible trail valid) (coveredTrace trail covered)
        (Use.releasedTrace trail valid released) quiet)

    finishes : O.Admissible accepted → Use.Released accepted →
      M.Complete selection accepted intent accepted (Pass.Result.after (Pass.run accepted))
    finishes valid released = completeTrace (Pass.Result.trace (Pass.run accepted)) valid acceptedCovered released (Pass.Result.noEdit (Pass.run accepted))

    resumes : ∀ {count observed} → Pass.Trace count accepted observed → O.Admissible accepted → Use.Released accepted →
      M.Complete selection accepted intent accepted (Pass.Result.after (Pass.run observed))
    resumes {observed = observed} first valid released = completeTrace (Aligned.Hist.appendTrace first (Pass.Result.trace (Pass.run observed))) valid acceptedCovered released (Pass.Result.noEdit (Pass.run observed))

  module Followup (selection : E.Rule) (original : O.World) (intent : M.Intent selection original) where
    module Parent = Completion.Model.Contract excluded selection original intent

    module Current (world : O.World) (valid : O.Admissible world) where
      captured : M.Intent selection world
      captured = M.captureIntent selection world (O.Admissible.unique valid)
      module Work = Run selection world captured

      coversNewBlocker : ∀ key value → DB.lookup key world ≡ just value → O.owner value ≡ E.targetOwner selection → key ∈ M.Intent.keys captured
      coversNewBlocker = Work.acceptedCovered

      parentNoPending : Work.Use.Released world → Parent.NoPending (Work.Pass.Result.after (Work.Pass.run world))
      parentNoPending released key (value , found , oldCaptured , owned , indexed , remaining) =
        Work.noPendingAtRest after (Work.Pass.traceAdmissible trail valid) (Work.coveredTrace trail Work.acceptedCovered)
          (Work.Use.releasedTrace trail valid released) (Work.Pass.Result.noEdit (Work.Pass.run world)) key
          (value , found , Work.coveredTrace trail Work.acceptedCovered key value found owned , owned , indexed , remaining)
        where
        trail = Work.Pass.Result.trace (Work.Pass.run world)
        after = Work.Pass.Result.after (Work.Pass.run world)

      savedOriginalTask : ∀ slot payload → DB.lookup slot world ≡ just (O.recordOf (E.targetOwner selection) (O.cleanupWork (M.Intent.keys intent) payload)) →
        DB.lookup slot (Work.Pass.Result.after (Work.Pass.run world)) ≡ just (O.recordOf (E.targetOwner selection) (O.cleanupWork (M.Intent.keys intent) payload))
      savedOriginalTask slot payload found = Work.Pass.traceMetadata (Work.Pass.Result.trace (Work.Pass.run world)) slot _ found refl
