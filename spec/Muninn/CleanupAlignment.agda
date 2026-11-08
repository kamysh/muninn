{-# OPTIONS --safe #-}
module Muninn.CleanupAlignment where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.CleanupEffects as Effects
import Muninn.CleanupProgress as Progress
import Muninn.CleanupHistory as History
import Muninn.CleanupCompletion as Completion
import Muninn.CleanupObservations as Observations
import Muninn.CleanupReverseViews as ReverseViews
import Muninn.CleanupReverseNeed as ReverseNeed
import Muninn.CleanupNeed as Need
import Muninn.CleanupNeedScope as Scope
import Muninn.CleanupStorage as Storage
import Muninn.CleanupOrder as Order
open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (Bool; true; false)
open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
module DB = O.DB

filterRetain : ∀ keep mask keys → (∀ key → keep key ≡ true → mask key ≡ true) →
  E.filterKeys mask (E.filterKeys keep keys) ≡ E.filterKeys keep keys
filterRetain keep mask [] positive = refl
filterRetain keep mask (key ∷ keys) positive with keep key in selected
... | false = filterRetain keep mask keys positive
... | true rewrite positive key selected = cong (key ∷_) (filterRetain keep mask keys positive)

module Model (excluded : List String → String → Bool) where
  module M = E.Model excluded
  module Obs = Observations.Model excluded
  module BackViews = ReverseViews.Model excluded
  module BackNeed = ReverseNeed.Model excluded
  module Needs = Need.Model excluded
  module Targets = Scope.Model excluded
  module Store = Storage.Model excluded

  module Contract (selection : E.Rule) (accepted : O.World) (intent : M.Intent selection accepted) where
    module Pass = Progress.Model.Pass excluded selection accepted intent
    module Core = Effects.Model.Core excluded selection accepted intent
    module Hist = History.Model.History excluded selection accepted intent
    module Steps = Obs.Step selection accepted intent
    module Final = Completion.Model.Contract excluded selection accepted intent

    planOrigin : ∀ chosen world (plan : Core.Plan chosen world) key value →
      DB.lookup key (proj₂ (DB.execute (Core.compile chosen world plan) world)) ≡ just value → BackNeed.Origin selection world key value
    planOrigin chosen world (Core.retain denied) key value found = BackNeed.origin value found refl
    planOrigin chosen world (Core.erase ready) key value found with chosen ≟ key
    ... | yes refl with trans (sym (DB.deleteAbsent key world)) found
    ...   | ()
    planOrigin chosen world (Core.erase ready) key value found | no distinct = BackNeed.origin value
      (trans (sym (DB.deletePreservesOther chosen key world distinct)) found) refl
    planOrigin chosen world (Core.trim (stored , present , captured , owned , indexed , needed , unprotected , changed)) key value found with chosen ≟ key
    ... | no distinct = BackNeed.origin value (trans (sym (DB.writePreservesOther chosen key (M.project selection world stored) world distinct)) found) refl
    ... | yes refl = BackNeed.origin stored present (trans (cong (M.project selection world) (sym same)) (Store.projectIdempotent selection world stored))
      where
      same : M.project selection world stored ≡ value
      same = just-injective (trans (sym (DB.writeVisible key (M.project selection world stored) world)) found)

    stepOrigin : ∀ chosen world key value → DB.lookup key (Pass.next chosen world) ≡ just value → BackNeed.Origin selection world key value
    stepOrigin chosen world = planOrigin chosen world (Core.decide chosen world)

    backwardPlain : ∀ {count before after} → Pass.Trace count before after → O.Admissible before → ∀ key value →
      DB.lookup key after ≡ just value → O.kind (O.body value) ≢ O.structuralSnapshotK → DB.lookup key before ≡ just value
    backwardPlain (Pass.stop world) valid key value found nonSnapshot = found
    backwardPlain (Pass.edit chosen before ready later) valid key value found nonSnapshot =
      Obs.Support.backwardPlain (Steps.stepSupport chosen before valid) key value
        (backwardPlain later (Core.transactionAdmissible chosen before valid) key value found nonSnapshot) nonSnapshot

    traceSupport : ∀ {count before after} → Pass.Trace count before after → O.Admissible before → Obs.Support selection before after
    traceSupport trail valid = record
      { safe = Hist.traceSafety trail valid
      ; uniqueBefore = O.Admissible.unique valid
      ; uniqueAfter = O.Admissible.unique (Pass.traceAdmissible trail valid)
      ; backwardPlain = backwardPlain trail valid }

    traceNeededBackward : ∀ {count before after} → Pass.Trace count before after → O.Admissible before →
      M.familyRegistered selection before ≡ true → ∀ key → M.Needed selection after key → M.Needed selection before key
    traceNeededBackward (Pass.stop world) valid registered key needed = needed
    traceNeededBackward (Pass.edit chosen before ready later) valid registered key needed =
      BackNeed.Reverse.neededBackward selection before (Pass.next chosen before) (Steps.stepSupport chosen before valid) registered (stepOrigin chosen before) key
        (traceNeededBackward later (Core.transactionAdmissible chosen before valid)
          (Obs.registrationPositive selection before (Pass.next chosen before) (Steps.stepSupport chosen before valid) registered) key needed)

    record Ancestor (before : O.World) (key : ℕ) (value : O.Record) : Set where
      constructor ancestor
      field original : O.Record
            found : DB.lookup key before ≡ just original
            owner : O.owner value ≡ O.owner original
            role : E.classify (O.body value) ≡ E.classify (O.body original)

    traceAncestor : ∀ {count before after} → Pass.Trace count before after → ∀ key value → DB.lookup key after ≡ just value → Ancestor before key value
    traceAncestor (Pass.stop world) key value found = ancestor value found refl refl
    traceAncestor (Pass.edit chosen before ready later) key value found with traceAncestor later key value found
    ... | ancestor middle present owner role with stepOrigin chosen before key middle present
    ... | BackNeed.origin original first same = ancestor original first
      (trans owner (Needs.projectionOwner selection before middle original same))
      (trans role (Needs.projectionClass selection before middle original same))

    earlierCanonical : ∀ before after → Obs.Support selection before after → M.familyRegistered selection before ≡ true → ∀ value →
      M.project selection before (M.project selection after value) ≡ M.project selection after value
    earlierCanonical before after support registered value with Observations.snapshotView value
    ... | Observations.plain nonSnapshot = trans (cong (M.project selection before) (Obs.projectionPlain selection after value nonSnapshot))
      (trans (Obs.projectionPlain selection before value nonSnapshot) (sym (Obs.projectionPlain selection after value nonSnapshot)))
    ... | Observations.snapshot owner selected nodes edges payload with E.ownerEqual owner (E.targetOwner selection) in decision
    ...   | no different rewrite decision = refl
    ...   | yes same rewrite decision = cong₂ (λ ns es → O.recordOf owner (O.structuralSnapshot selected ns es payload))
      (filterRetain (M.symbolVisible selection after owner selected) (M.symbolVisible selection before owner selected) nodes
        (λ key → BackViews.Reverse.symbolBackward selection before after support owner selected key registered))
      (filterRetain (M.edgeVisible selection after owner selected) (M.edgeVisible selection before owner selected) edges
        (λ key → BackViews.Reverse.edgeBackward selection before after support owner selected key registered))

    canonicalRegistered : ∀ {count before after} → Pass.Trace count before after → O.Admissible before →
      M.familyRegistered selection before ≡ true → M.Complete selection accepted intent after after →
      ∀ key value → key ∈ M.Intent.keys intent → DB.lookup key before ≡ just value → M.Needed selection before key →
      DB.lookup key after ≡ just (M.project selection before value)
    canonicalRegistered {before = before} {after = after} trail valid registered completed key value captured found needed
      with Hist.neededFrame trail valid key value found needed
    ... | Hist.content retained present same nodes edges = trans present (cong just (trans (sym beforeFixed) same))
      where
      finalFixed : retained ≡ M.project selection after retained
      finalFixed = just-injective (trans (sym present) (M.Complete.canonical completed key retained captured present
        (Hist.neededAcrossTrace trail valid key needed)))
      beforeFixed : M.project selection before retained ≡ retained
      beforeFixed = trans (cong (M.project selection before) finalFixed)
        (trans (earlierCanonical before after (traceSupport trail valid) registered retained) (sym finalFixed))

    canonical : ∀ {count before after} → Pass.Trace count before after → O.Admissible before →
      M.Complete selection accepted intent after after → ∀ key value → key ∈ M.Intent.keys intent →
      DB.lookup key before ≡ just value → M.Needed selection before key → DB.lookup key after ≡ just (M.project selection before value)
    canonical {before = before} {after = after} trail valid completed key value captured found needed
      with M.familyRegistered selection before in registered
    ... | true = canonicalRegistered trail valid registered completed key value captured found needed
    ... | false with Observations.snapshotView value
    ...   | Observations.plain nonSnapshot = trans (Hist.originalNeededPlain trail valid key value found needed nonSnapshot)
        (cong just (sym (Obs.projectionPlain selection before value nonSnapshot)))
    ...   | Observations.snapshot owner selected nodes edges payload with E.ownerEqual owner (E.targetOwner selection)
    ...     | no different = Pass.traceUnrelated trail key value found different
    ...     | yes owned = ⊥-elim (Observations.falseNotTrue (trans (sym registered)
        (Targets.neededRegistration selection before key value found owned refl needed)))

    unneededPersists : ∀ {count before after} → Pass.Trace count before after → O.Admissible before →
      ∀ key value → DB.lookup key after ≡ just value → O.owner value ≡ E.targetOwner selection → E.indexed value ≡ true →
      ¬ M.Needed selection before key → ¬ M.Needed selection after key
    unneededPersists {before = before} {after = after} trail valid key value found owned indexed unneeded needed
      with M.familyRegistered selection before in registered
    ... | true = unneeded (traceNeededBackward trail valid registered key needed)
    ... | false = Observations.falseNotTrue (trans (sym registered)
      (BackViews.Reverse.registrationBackward selection before after (traceSupport trail valid)
        (Targets.neededRegistration selection after key value found owned indexed needed)))

    reclaimed : ∀ {count before after} → Pass.Trace count before after → O.Admissible before →
      M.Complete selection accepted intent after after → ∀ key value → key ∈ M.Intent.keys intent → DB.lookup key before ≡ just value →
      O.owner value ≡ E.targetOwner selection → E.indexed value ≡ true → ¬ M.Needed selection before key → DB.lookup key after ≡ nothing
    reclaimed {before = before} {after = after} trail valid completed key value captured found owned indexed unneeded
      with DB.lookup key after in observed
    ... | nothing = refl
    ... | just retained with traceAncestor trail key retained observed
    ...   | ancestor original first sameOwner sameRole with just-injective (trans (sym found) first)
    ...     | refl = trans (sym observed) (M.Complete.reclaimed completed key retained captured observed
        (trans sameOwner owned) (trans (cong E.indexedRole sameRole) indexed)
        (unneededPersists trail valid key retained observed (trans sameOwner owned) (trans (cong E.indexedRole sameRole) indexed) unneeded))

    complete : ∀ {count before after} → Pass.Trace count before after → O.Admissible before →
      M.Complete selection accepted intent after after → M.Complete selection accepted intent before after
    complete trail valid completed = record
      { safety = Hist.traceSafety trail valid
      ; uniqueAfter = M.Complete.uniqueAfter completed
      ; canonical = canonical trail valid completed
      ; outsideCapture = Pass.traceOutsideCapture trail
      ; reclaimed = reclaimed trail valid completed
      ; noNewRecords = λ key value present → Ancestor.original (traceAncestor trail key value
          (Order.memberLookup _ key value (M.Complete.uniqueAfter completed) present)) , Ancestor.found (traceAncestor trail key value
          (Order.memberLookup _ key value (M.Complete.uniqueAfter completed) present)) }

    completeFromNoPending : ∀ {count before after} → Pass.Trace count before after → O.Admissible before →
      Final.NoPending after → M.Complete selection accepted intent before after
    completeFromNoPending {after = after} trail valid none = complete trail valid
      (Final.completeWithoutPending after (O.Admissible.unique (Pass.traceAdmissible trail valid)) none)

    passComplete : ∀ before → O.Admissible before →
      Final.NoPending (Pass.Result.after (Pass.run before)) → M.Complete selection accepted intent before (Pass.Result.after (Pass.run before))
    passComplete before valid none = completeFromNoPending (Pass.Result.trace (Pass.run before)) valid none

    resumedComplete : ∀ {n m before observed after} → Pass.Trace n before observed → Pass.Trace m observed after →
      O.Admissible before → M.Complete selection accepted intent after after → M.Complete selection accepted intent before after
    resumedComplete first second valid completed = complete (Hist.appendTrace first second) valid completed

    resumedPassComplete : ∀ {count before observed} → Pass.Trace count before observed → O.Admissible before →
      Final.NoPending (Pass.Result.after (Pass.run observed)) →
      M.Complete selection accepted intent before (Pass.Result.after (Pass.run observed))
    resumedPassComplete first valid none = completeFromNoPending (Hist.appendTrace first (Pass.Result.trace (Pass.run _))) valid none
