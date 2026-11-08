{-# OPTIONS --safe #-}
module Muninn.CleanupHistory where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.CleanupEffects as Effects
import Muninn.CleanupProgress as Progress
import Muninn.CleanupProtection as Protection
import Muninn.CleanupObservations as Observations
import Muninn.CleanupViews as Views
import Muninn.CleanupNeed as Need
import Muninn.CleanupStorage as Storage
open import Data.Nat using (ℕ; _+_)
open import Data.Bool using (Bool; true; false)
open import Data.String using (String)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (just)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
module DB = O.DB

filterAbsorb : ∀ first second keys →
  (∀ key → key ∈ keys → first key ≡ true → second key ≡ true) →
  E.filterKeys first (E.filterKeys second keys) ≡ E.filterKeys first keys
filterAbsorb first second [] positive = refl
filterAbsorb first second (key ∷ keys) positive with first key in selected
... | true rewrite positive key (here refl) selected | selected =
  cong (key ∷_) (filterAbsorb first second keys (λ k present → positive k (there present)))
... | false with second key
...   | false = filterAbsorb first second keys (λ k present → positive k (there present))
...   | true rewrite selected = filterAbsorb first second keys (λ k present → positive k (there present))

module Model (excluded : List String → String → Bool) where
  module M = E.Model excluded
  module Obs = Observations.Model excluded
  module View = Views.Model excluded
  module Needs = Need.Model excluded
  module Store = Storage.Model excluded
  module Protected = Protection.Model excluded

  module History (selection : E.Rule) (accepted : O.World) (intent : M.Intent selection accepted) where
    module Pass = Progress.Model.Pass excluded selection accepted intent
    module Core = Effects.Model.Core excluded selection accepted intent
    module Support = Obs.Step selection accepted intent
    module Pins = Protected.Trace selection accepted intent

    targetProjection : ∀ world selected nodes edges payload →
      M.project selection world (O.recordOf (E.targetOwner selection) (O.structuralSnapshot selected nodes edges payload)) ≡
      O.recordOf (E.targetOwner selection) (O.structuralSnapshot selected
        (E.filterKeys (M.symbolVisible selection world (E.targetOwner selection) selected) nodes)
        (E.filterKeys (M.edgeVisible selection world (E.targetOwner selection) selected) edges) payload)
    targetProjection world selected nodes edges payload with E.ownerEqual (E.targetOwner selection) (E.targetOwner selection)
    ... | yes same = refl
    ... | no different = ⊥-elim (different refl)

    nodeNeeded : ∀ before source selected nodes edges payload key → O.Admissible before →
      DB.lookup source before ≡ just (O.recordOf (E.targetOwner selection) (O.structuralSnapshot selected nodes edges payload)) →
      M.Needed selection before source → key ∈ nodes → M.symbolVisible selection before (E.targetOwner selection) selected key ≡ true → M.Needed selection before key
    nodeNeeded before source selected nodes edges payload key valid found needed present visible =
      M.required needed (M.reference source value ref found permanent resolved)
      where
      value = O.recordOf (E.targetOwner selection) (O.structuralSnapshot selected nodes edges payload)
      ref = O.reference key O.symbolK
      raw : ref ∈ O.references (O.body value)
      raw = there (∈-++⁺ˡ (∈-map⁺ (λ key → O.reference key O.symbolK) present))
      resolved : O.Resolves before (E.targetOwner selection) ref
      resolved = All.lookup (Storage.lookupAll before source value (O.Admissible.sound valid) found) raw
      filtered : ref ∈ O.references (O.body (O.recordOf (E.targetOwner selection) (O.structuralSnapshot selected
        (E.filterKeys (M.symbolVisible selection before (E.targetOwner selection) selected) nodes)
        (E.filterKeys (M.edgeVisible selection before (E.targetOwner selection) selected) edges) payload)))
      filtered = there (∈-++⁺ˡ (∈-map⁺ (λ key → O.reference key O.symbolK)
        (E.filterKeysComplete _ nodes key present visible)))
      permanent : ref ∈ M.referencesFor M.permanent selection before value
      permanent = subst (λ refs → ref ∈ refs) (sym (Needs.refsNotHolder selection before value (λ ())))
        (subst (λ v → ref ∈ O.references (O.body v)) (sym (targetProjection before selected nodes edges payload)) filtered)

    edgeNeeded : ∀ before source selected nodes edges payload key → O.Admissible before →
      DB.lookup source before ≡ just (O.recordOf (E.targetOwner selection) (O.structuralSnapshot selected nodes edges payload)) →
      M.Needed selection before source → key ∈ edges → M.edgeVisible selection before (E.targetOwner selection) selected key ≡ true → M.Needed selection before key
    edgeNeeded before source selected nodes edges payload key valid found needed present visible =
      M.required needed (M.reference source value ref found permanent resolved)
      where
      value = O.recordOf (E.targetOwner selection) (O.structuralSnapshot selected nodes edges payload)
      ref = O.reference key O.edgeK
      raw : ref ∈ O.references (O.body value)
      raw = there (∈-++⁺ʳ (map (λ key → O.reference key O.symbolK) nodes) (∈-map⁺ (λ key → O.reference key O.edgeK) present))
      resolved : O.Resolves before (E.targetOwner selection) ref
      resolved = All.lookup (Storage.lookupAll before source value (O.Admissible.sound valid) found) raw
      filtered : ref ∈ O.references (O.body (O.recordOf (E.targetOwner selection) (O.structuralSnapshot selected
        (E.filterKeys (M.symbolVisible selection before (E.targetOwner selection) selected) nodes)
        (E.filterKeys (M.edgeVisible selection before (E.targetOwner selection) selected) edges) payload)))
      filtered = there (∈-++⁺ʳ (map (λ key → O.reference key O.symbolK)
          (E.filterKeys (M.symbolVisible selection before (E.targetOwner selection) selected) nodes))
        (∈-map⁺ (λ key → O.reference key O.edgeK) (E.filterKeysComplete _ edges key present visible)))
      permanent : ref ∈ M.referencesFor M.permanent selection before value
      permanent = subst (λ refs → ref ∈ refs) (sym (Needs.refsNotHolder selection before value (λ ())))
        (subst (λ v → ref ∈ O.references (O.body v)) (sym (targetProjection before selected nodes edges payload)) filtered)

    absorbProjection : ∀ before middle source selected nodes edges payload value → O.Admissible before → Obs.Support selection before middle →
      DB.lookup source before ≡ just (O.recordOf (E.targetOwner selection) (O.structuralSnapshot selected nodes edges payload)) →
      M.Needed selection before source → O.owner value ≡ E.targetOwner selection →
      O.kind (O.body value) ≡ O.structuralSnapshotK → E.classify (O.body value) ≡ E.snapshot selected →
      (∀ key → key ∈ E.snapshotNodes value → key ∈ nodes) → (∀ key → key ∈ E.snapshotEdges value → key ∈ edges) →
      M.project selection before (M.project selection middle value) ≡ M.project selection before value
    absorbProjection before middle source selected nodes edges payload value valid support found needed owner kind role nodeSubset edgeSubset
      with Observations.snapshotView value
    ... | Observations.plain nonSnapshot = ⊥-elim (nonSnapshot kind)
    ... | Observations.snapshot storedOwner storedSelected ns es text with owner | role
    ...   | refl | refl = trans (cong (M.project selection before) (targetProjection middle selected ns es text))
        (trans (targetProjection before selected (E.filterKeys (M.symbolVisible selection middle (E.targetOwner selection) selected) ns)
          (E.filterKeys (M.edgeVisible selection middle (E.targetOwner selection) selected) es) text)
          (trans (cong₂ (λ n e → O.recordOf (E.targetOwner selection) (O.structuralSnapshot selected n e text))
            (filterAbsorb (M.symbolVisible selection before (E.targetOwner selection) selected)
              (M.symbolVisible selection middle (E.targetOwner selection) selected) ns
              (λ key present visible → View.View.symbolPositive selection before middle selected key support
                (nodeNeeded before source selected nodes edges payload key valid found needed (nodeSubset key present) visible) visible))
            (filterAbsorb (M.edgeVisible selection before (E.targetOwner selection) selected)
              (M.edgeVisible selection middle (E.targetOwner selection) selected) es
              (λ key present visible → View.View.edgePositive selection before middle selected key valid support
                (edgeNeeded before source selected nodes edges payload key valid found needed (edgeSubset key present) visible) visible)))
            (sym (targetProjection before selected ns es text))))

    neededAcrossTrace : ∀ {count before after} → Pass.Trace count before after → O.Admissible before → ∀ key → M.Needed selection before key → M.Needed selection after key
    neededAcrossTrace (Pass.stop world) valid key needed = needed
    neededAcrossTrace (Pass.edit chosen before ready later) valid key needed = neededAcrossTrace later
      (Core.transactionAdmissible chosen before valid) key
      (Needs.neededSurvives selection before (Pass.next chosen before) key valid (Support.stepSupport chosen before valid) needed)

    originalNeededPlain : ∀ {count before after} → Pass.Trace count before after → O.Admissible before → ∀ key value →
      DB.lookup key before ≡ just value → M.Needed selection before key → O.kind (O.body value) Relation.Binary.PropositionalEquality.≢ O.structuralSnapshotK → DB.lookup key after ≡ just value
    originalNeededPlain (Pass.stop world) valid key value found needed nonSnapshot = found
    originalNeededPlain (Pass.edit chosen before ready later) valid key value found needed nonSnapshot = originalNeededPlain later
      (Core.transactionAdmissible chosen before valid) key value
      (Obs.neededSame selection before (Pass.next chosen before) key value (Core.transactionSafety chosen before) found needed nonSnapshot)
      (Needs.neededSurvives selection before (Pass.next chosen before) key valid (Support.stepSupport chosen before valid) needed) nonSnapshot

    record ContentFrame (before after : O.World) (key : ℕ) (value : O.Record) : Set where
      constructor content
      field retained : O.Record
            present : DB.lookup key after ≡ just retained
            projected : M.project selection before retained ≡ M.project selection before value
            nodes : ∀ member → member ∈ E.snapshotNodes retained → member ∈ E.snapshotNodes value
            edges : ∀ member → member ∈ E.snapshotEdges retained → member ∈ E.snapshotEdges value

    contentTuple : ∀ {before after key value} → ContentFrame before after key value →
      Σ O.Record (λ retained → (DB.lookup key after ≡ just retained) ×
        ((M.project selection before retained ≡ M.project selection before value) ×
          ((∀ member → member ∈ E.snapshotNodes retained → member ∈ E.snapshotNodes value) ×
           (∀ member → member ∈ E.snapshotEdges retained → member ∈ E.snapshotEdges value))))
    contentTuple (content retained present projected nodes edges) = retained , present , projected , nodes , edges

    neededFrame : ∀ {count before after} → Pass.Trace count before after → O.Admissible before → ∀ key value →
      DB.lookup key before ≡ just value → M.Needed selection before key → ContentFrame before after key value
    neededFrame (Pass.stop world) valid key value found needed = content value found refl (λ member seen → seen) (λ member seen → seen)
    neededFrame trail@(Pass.edit chosen before ready later) valid key value found needed with Observations.snapshotView value
    ... | Observations.plain nonSnapshot = content value (originalNeededPlain trail valid key value found needed nonSnapshot) refl (λ member seen → seen) (λ member seen → seen)
    ... | Observations.snapshot owner selected nodes edges payload with E.ownerEqual owner (E.targetOwner selection)
    ...   | no different = content value (Pass.traceUnrelated trail key value found different) refl (λ member seen → seen) (λ member seen → seen)
    ...   | yes refl with M.Safety.needed (Core.transactionSafety chosen before) key value found needed
    ...     | middleValue , middleFound , firstProjection , firstNodes , firstEdges
      with neededFrame later (Core.transactionAdmissible chosen before valid) key middleValue middleFound
        (Needs.neededSurvives selection before (Pass.next chosen before) key valid (Support.stepSupport chosen before valid) needed)
    ...       | content finalValue finalFound laterProjection laterNodes laterEdges = content finalValue finalFound
      (trans (sym finalAbsorption) (trans (cong (M.project selection before) laterProjection) (trans firstAbsorption firstProjection)))
      (λ member present → firstNodes member (laterNodes member present))
      (λ member present → firstEdges member (laterEdges member present))
      where
      original : O.Record
      original = O.recordOf (E.targetOwner selection) (O.structuralSnapshot selected nodes edges payload)
      middle : O.World
      middle = Pass.next chosen before
      supported : Obs.Support selection before middle
      supported = Support.stepSupport chosen before valid
      middleOwner : O.owner middleValue ≡ E.targetOwner selection
      middleOwner = Needs.projectionOwner selection before middleValue original firstProjection
      middleKind : O.kind (O.body middleValue) ≡ O.structuralSnapshotK
      middleKind = Needs.projectionKind selection before middleValue original firstProjection
      middleClass : E.classify (O.body middleValue) ≡ E.snapshot selected
      middleClass = Needs.projectionClass selection before middleValue original firstProjection
      finalOwner : O.owner finalValue ≡ E.targetOwner selection
      finalOwner = trans (Needs.projectionOwner selection middle finalValue middleValue laterProjection) middleOwner
      finalKind : O.kind (O.body finalValue) ≡ O.structuralSnapshotK
      finalKind = trans (Needs.projectionKind selection middle finalValue middleValue laterProjection) middleKind
      finalClass : E.classify (O.body finalValue) ≡ E.snapshot selected
      finalClass = trans (Needs.projectionClass selection middle finalValue middleValue laterProjection) middleClass
      firstAbsorption : M.project selection before (M.project selection middle middleValue) ≡ M.project selection before middleValue
      firstAbsorption = absorbProjection before middle key selected nodes edges payload middleValue valid supported found needed
        middleOwner middleKind middleClass firstNodes firstEdges
      finalAbsorption : M.project selection before (M.project selection middle finalValue) ≡ M.project selection before finalValue
      finalAbsorption = absorbProjection before middle key selected nodes edges payload finalValue valid supported found needed
        finalOwner finalKind finalClass
        (λ member present → firstNodes member (laterNodes member present))
        (λ member present → firstEdges member (laterEdges member present))

    traceSafety : ∀ {count before after} → Pass.Trace count before after → O.Admissible before → M.Safety selection before after
    traceSafety trail valid = record
      { unrelated = Pass.traceUnrelated trail
      ; metadata = Pass.traceMetadata trail
      ; needed = λ key value found needed → contentTuple (neededFrame trail valid key value found needed)
      ; protected = Pins.originalProtectedRecord trail }

    passSafety : ∀ before → O.Admissible before → M.Safety selection before (Pass.Result.after (Pass.run before))
    passSafety before valid = traceSafety (Pass.Result.trace (Pass.run before)) valid

    appendTrace : ∀ {n m before observed after} → Pass.Trace n before observed → Pass.Trace m observed after → Pass.Trace (n + m) before after
    appendTrace (Pass.stop world) second = second
    appendTrace (Pass.edit chosen before ready later) second = Pass.edit chosen before ready (appendTrace later second)

    resumedSafety : ∀ {n m before observed after} → Pass.Trace n before observed → Pass.Trace m observed after →
      O.Admissible before → M.Safety selection before after
    resumedSafety first second valid = traceSafety (appendTrace first second) valid

    resumedPassSafety : ∀ {count before observed} → Pass.Trace count before observed → O.Admissible before →
      M.Safety selection before (Pass.Result.after (Pass.run observed))
    resumedPassSafety first valid = resumedSafety first (Pass.Result.trace (Pass.run _)) valid
