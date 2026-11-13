{-# OPTIONS --safe #-}
module Muninn.CleanupNeed where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.CleanupObservations as Observations
import Muninn.CleanupNeedScope as Scope
import Muninn.CleanupViews as Views
import Muninn.CleanupStorage as Storage
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; _∧_)
open import Data.String using (String)
open import Data.List using (List; []; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻; ∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (just)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
module DB = O.DB

module Model where
  module M = E.Model
  module Obs = Observations.Model
  module View = Views.Model
  module Store = Storage.Model
  module Target = Scope.Model

  projectClass : ∀ selection world value → E.classify (O.body (M.project selection world value)) ≡ E.classify (O.body value)
  projectClass selection world value with Store.shape selection world value
  ... | Store.plain exact = cong (λ v → E.classify (O.body v)) exact
  ... | Store.hiddenDelta owner selected version path answer same = cong (λ v → E.classify (O.body v)) same
  ... | Store.snapshot owner selected nodes edges payload with E.ownerEqual owner (E.targetOwner selection)
  ...   | yes same = refl
  ...   | no different = refl

  projectionOwner : ∀ selection world retained original → M.project selection world retained ≡ M.project selection world original → O.owner retained ≡ O.owner original
  projectionOwner selection world retained original same = trans (sym (Store.projectOwner selection world retained))
    (trans (cong O.owner same) (Store.projectOwner selection world original))

  projectionKind : ∀ selection world retained original → M.project selection world retained ≡ M.project selection world original → O.kind (O.body retained) ≡ O.kind (O.body original)
  projectionKind selection world retained original same = trans (sym (Store.projectKind selection world retained))
    (trans (cong (λ v → O.kind (O.body v)) same) (Store.projectKind selection world original))

  projectionCheckout : ∀ selection world retained original →
    M.project selection world retained ≡ M.project selection world original →
    E.snapshotCheckout retained ≡ E.snapshotCheckout original
  projectionCheckout selection world retained original same = trans (sym (Store.projectCheckout selection world retained))
    (trans (cong E.snapshotCheckout same) (Store.projectCheckout selection world original))

  projectionClass : ∀ selection world retained original → M.project selection world retained ≡ M.project selection world original → E.classify (O.body retained) ≡ E.classify (O.body original)
  projectionClass selection world retained original same = trans (sym (projectClass selection world retained))
    (trans (cong (λ v → E.classify (O.body v)) same) (projectClass selection world original))

  rolePositive : ∀ selection before after role → Obs.Support selection before after → M.rootedRole selection before role ≡ true → M.rootedRole selection after role ≡ true

  rolePositive selection before after E.administrative support rooted = refl
  rolePositive selection before after E.holder support rooted = refl
  rolePositive selection before after E.artifact support ()
  rolePositive selection before after (E.attached parent gate) support ()
  rolePositive selection before after (E.baselineAnchor) support rooted = (Views.andBoth (Obs.registrationPositive selection before after support (Scope.andLeft (M.familyRegistered selection before) (M.anyCheckoutLive selection before) (rooted))) (Obs.anyCheckoutPositive selection before after support (Scope.andRight (M.familyRegistered selection before) (M.anyCheckoutLive selection before) (rooted))))
  rolePositive selection before after (E.baselineBinding path gitDefault) support rooted = (Views.andBoth (Obs.registrationPositive selection before after support (Scope.andLeft (M.familyRegistered selection before) ((M.anyCheckoutLive selection before) ∧ (M.includedWithGit selection (E.targetOwner selection) gitDefault path)) (rooted))) (Views.andBoth (Obs.anyCheckoutPositive selection before after support (Scope.andLeft (M.anyCheckoutLive selection before) (M.includedWithGit selection (E.targetOwner selection) gitDefault path) (Scope.andRight (M.familyRegistered selection before) ((M.anyCheckoutLive selection before) ∧ (M.includedWithGit selection (E.targetOwner selection) gitDefault path)) (rooted)))) (Scope.andRight (M.anyCheckoutLive selection before) (M.includedWithGit selection (E.targetOwner selection) gitDefault path) (Scope.andRight (M.familyRegistered selection before) ((M.anyCheckoutLive selection before) ∧ (M.includedWithGit selection (E.targetOwner selection) gitDefault path)) (rooted)))))
  rolePositive selection before after (E.checkoutBinding selected path) support rooted = Views.andBoth (Obs.registrationPositive selection before after support (Scope.andLeft _ _ rooted)) (Obs.checkoutPositive selection before after selected support (Scope.andRight _ _ rooted))
  rolePositive selection before after (E.snapshot selected) support rooted = (Views.andBoth (Obs.registrationPositive selection before after support (Scope.andLeft (M.familyRegistered selection before) (M.checkoutLive selection before selected) (rooted))) (Obs.checkoutPositive selection before after selected support (Scope.andRight (M.familyRegistered selection before) (M.checkoutLive selection before selected) (rooted))))
  rolePositive selection before after (E.legacyFile path gitDefault) support rooted = (Views.andBoth (Obs.registrationPositive selection before after support (Scope.andLeft (M.familyRegistered selection before) ((M.legacyReadable selection before) ∧ (M.includedWithGit selection (E.targetOwner selection) gitDefault path)) (rooted))) (Views.andBoth (Obs.legacyPositive selection before after support (Scope.andLeft (M.legacyReadable selection before) (M.includedWithGit selection (E.targetOwner selection) gitDefault path) (Scope.andRight (M.familyRegistered selection before) ((M.legacyReadable selection before) ∧ (M.includedWithGit selection (E.targetOwner selection) gitDefault path)) (rooted)))) (Scope.andRight (M.legacyReadable selection before) (M.includedWithGit selection (E.targetOwner selection) gitDefault path) (Scope.andRight (M.familyRegistered selection before) ((M.legacyReadable selection before) ∧ (M.includedWithGit selection (E.targetOwner selection) gitDefault path)) (rooted)))))
  rolePositive selection before after (E.graphContainer Data.Maybe.nothing inUse) support rooted = (Views.andBoth (Scope.andLeft (inUse) ((M.familyRegistered selection before) ∧ (M.anyCheckoutLive selection before)) (rooted)) (Views.andBoth (Obs.registrationPositive selection before after support (Scope.andLeft (M.familyRegistered selection before) (M.anyCheckoutLive selection before) (Scope.andRight (inUse) ((M.familyRegistered selection before) ∧ (M.anyCheckoutLive selection before)) (rooted)))) (Obs.anyCheckoutPositive selection before after support (Scope.andRight (M.familyRegistered selection before) (M.anyCheckoutLive selection before) (Scope.andRight (inUse) ((M.familyRegistered selection before) ∧ (M.anyCheckoutLive selection before)) (rooted))))))
  rolePositive selection before after (E.graphContainer (just selected) inUse) support rooted = (Views.andBoth (Scope.andLeft (inUse) ((M.familyRegistered selection before) ∧ (M.checkoutLive selection before selected)) (rooted)) (Views.andBoth (Obs.registrationPositive selection before after support (Scope.andLeft (M.familyRegistered selection before) (M.checkoutLive selection before selected) (Scope.andRight (inUse) ((M.familyRegistered selection before) ∧ (M.checkoutLive selection before selected)) (rooted)))) (Obs.checkoutPositive selection before after selected support (Scope.andRight (M.familyRegistered selection before) (M.checkoutLive selection before selected) (Scope.andRight (inUse) ((M.familyRegistered selection before) ∧ (M.checkoutLive selection before selected)) (rooted))))))

  rootPositive : ∀ selection before after value → Obs.Support selection before after → M.rooted selection before value ≡ true → M.rooted selection after value ≡ true
  rootPositive selection before after value support rooted with E.ownerEqual (O.owner value) (E.targetOwner selection)
  ... | no different = refl
  ... | yes same = rolePositive selection before after (E.classify (O.body value)) support rooted

  refsNotHolder : ∀ selection world value → E.classify (O.body value) ≢ E.holder →
    M.referencesFor M.permanent selection world value ≡ O.references (O.body (M.project selection world value))
  refsNotHolder selection world value nonHolder with E.classify (O.body value)
  ... | E.holder = ⊥-elim (nonHolder refl)
  ... | E.administrative = refl
  ... | E.artifact = refl
  ... | E.baselineAnchor = refl
  ... | E.baselineBinding path gitDefault = refl
  ... | E.checkoutBinding selected path = refl
  ... | E.snapshot selected = refl
  ... | E.legacyFile path gitDefault = refl
  ... | E.graphContainer selected inUse = refl
  ... | E.attached parent gate = refl

  memberNotHolder : ∀ selection world value ref → ref ∈ M.referencesFor M.permanent selection world value → E.classify (O.body value) ≢ E.holder
  memberNotHolder selection world value ref present with E.classify (O.body value)
  ... | E.holder with present
  ...   | ()
  memberNotHolder selection world value ref present | E.administrative = λ ()
  memberNotHolder selection world value ref present | E.artifact = λ ()
  memberNotHolder selection world value ref present | E.baselineAnchor = λ ()
  memberNotHolder selection world value ref present | E.baselineBinding path gitDefault = λ ()
  memberNotHolder selection world value ref present | E.checkoutBinding selected path = λ ()
  memberNotHolder selection world value ref present | E.snapshot selected = λ ()
  memberNotHolder selection world value ref present | E.legacyFile path gitDefault = λ ()
  memberNotHolder selection world value ref present | E.graphContainer selected inUse = λ ()
  memberNotHolder selection world value ref present | E.attached parent gate = λ ()

  projectedRefsPositive : ∀ selection before after value ref → O.Admissible before → Obs.Support selection before after →
    M.Needed selection before (O.target ref) → ref ∈ O.references (O.body (M.project selection before value)) →
    ref ∈ O.references (O.body (M.project selection after value))
  projectedRefsPositive selection before after value ref valid support needed present with Observations.snapshotView value
  ... | Observations.plain nonSnapshot = subst (λ v → ref ∈ O.references (O.body v))
      (trans (Obs.projectionPlain selection before value nonSnapshot) (sym (Obs.projectionPlain selection after value nonSnapshot))) present
  ... | Observations.snapshot owner selected nodes edges payload with E.ownerEqual owner (E.targetOwner selection)
  ...   | no different = present
  ...   | yes refl with present
  ...     | here same = here same
  ...     | there later with ∈-++⁻ (map (λ key → O.reference key O.symbolK)
          (E.filterKeys (M.symbolVisible selection before (E.targetOwner selection) selected) nodes)) later
  ...       | inj₁ node with ∈-map⁻ (λ key → O.reference key O.symbolK) node
  ...         | key , filtered , refl = there (∈-++⁺ˡ (∈-map⁺ (λ key → O.reference key O.symbolK)
            (E.filterKeysComplete (M.symbolVisible selection after (E.targetOwner selection) selected) nodes key
              (Storage.filterSubset _ nodes key filtered)
              (View.View.symbolPositive selection before after selected key support needed (E.filterKeysSound _ nodes key filtered)))))
  projectedRefsPositive selection before after value ref valid support needed present | Observations.snapshot owner selected nodes edges payload
    | yes refl | there later | inj₂ edge with ∈-map⁻ (λ key → O.reference key O.edgeK) edge
  ... | key , filtered , refl = there (∈-++⁺ʳ (map (λ key → O.reference key O.symbolK)
      (E.filterKeys (M.symbolVisible selection after (E.targetOwner selection) selected) nodes))
        (∈-map⁺ (λ key → O.reference key O.edgeK)
          (E.filterKeysComplete (M.edgeVisible selection after (E.targetOwner selection) selected) edges key
            (Storage.filterSubset _ edges key filtered)
            (View.View.edgePositive selection before after selected key valid support needed (E.filterKeysSound _ edges key filtered)))))

  projectedRefsPositive selection before after value ref valid support needed present | Observations.delta owner selected version path answer =
    subst (λ row → ref ∈ O.references (O.body row))
      (Store.projectWorldIndependent selection before after value (λ ())) present

  referencePersist : ∀ selection before after original retained ref → O.Admissible before → Obs.Support selection before after →
    M.Needed selection before (O.target ref) → M.project selection before retained ≡ M.project selection before original →
    ref ∈ M.referencesFor M.permanent selection before original → ref ∈ M.referencesFor M.permanent selection after retained
  referencePersist selection before after original retained ref valid support needed same present =
    subst (λ refs → ref ∈ refs) (sym (refsNotHolder selection after retained nonHolderRetained))
      (projectedRefsPositive selection before after retained ref valid support needed
        (subst (λ v → ref ∈ O.references (O.body v)) (sym same)
          (subst (λ refs → ref ∈ refs) (refsNotHolder selection before original nonHolder) present)))
    where
    nonHolder : E.classify (O.body original) ≢ E.holder
    nonHolder = memberNotHolder selection before original ref present
    nonHolderRetained : E.classify (O.body retained) ≢ E.holder
    nonHolderRetained sameRole = nonHolder (trans (sym (projectionClass selection before retained original same)) sameRole)

  attachedNonSnapshot : ∀ selection world value ref → M.parentOf M.permanent selection world value ≡ just ref → Storage.PlainKind value
  attachedNonSnapshot selection world value ref parent with Observations.snapshotView value
  ... | Observations.plain nonSnapshot = nonSnapshot
  ... | Observations.snapshot owner selected nodes edges payload with parent
  ...   | ()

  attachedNonSnapshot selection world value ref parent | Observations.delta owner selected version path answer with parent
  ... | ()

  neededResolves : ∀ selection before after source ref →
    M.Safety selection before after → M.Needed selection before (O.target ref) →
    O.Resolves before source ref → O.Resolves after source ref
  neededResolves selection before after source ref safe needed resolved
    with M.Safety.needed safe (O.target ref) (O.Resolves.value resolved) (O.Resolves.found resolved) needed
  ... | retained , present , same , nodes , edges = record
    { value = retained; found = present
    ; rightKind = trans (projectionKind selection before retained (O.Resolves.value resolved) same) (O.Resolves.rightKind resolved)
    ; rightOwner = subst (O.MayReference source)
        (sym (projectionOwner selection before retained (O.Resolves.value resolved) same)) (O.Resolves.rightOwner resolved) }

  neededSurvives : ∀ selection before after key → O.Admissible before → Obs.Support selection before after →
    M.Needed selection before key → M.Needed selection after key
  neededSurvives selection before after key valid support needed@(M.root .key value found rooted)
    with M.Safety.needed (Obs.Support.safe support) key value found needed
  ... | retained , present , same , nodes , edges = M.root key retained present
      (trans (cong₂ (M.rootedFrom selection after) (projectionOwner selection before retained value same) (projectionClass selection before retained value same))
        (rootPositive selection before after value support rooted))
  neededSurvives selection before after key valid support needed@(M.required previous (M.reference source value ref found included resolved))
    with M.Safety.needed (Obs.Support.safe support) source value found previous
  ... | retained , present , same , nodes , edges = M.required (neededSurvives selection before after source valid support previous)
      (M.reference source retained ref present (referencePersist selection before after value retained ref valid support needed same included)
        (subst (λ sourceOwner → O.Resolves after sourceOwner ref)
          (sym (projectionOwner selection before retained value same))
          (neededResolves selection before after (O.owner value) ref (Obs.Support.safe support) needed resolved)))
  neededSurvives selection before after key valid support needed@(M.required previous
    (M.attachment parent parentValue child childValue parentFound childFound attached sameOwner)) =
    M.required (neededSurvives selection before after parent valid support previous)
      (M.attachment parent parentValue child childValue
        (Obs.neededSame selection before after parent parentValue (Obs.Support.safe support) parentFound previous
          (Target.parentNotSnapshot selection before childValue (O.reference parent (O.kind (O.body parentValue))) attached))
        (Obs.neededSame selection before after child childValue (Obs.Support.safe support) childFound needed
          (attachedNonSnapshot selection before childValue (O.reference parent (O.kind (O.body parentValue))) attached))
        (View.View.parentPositive selection before after child childValue (O.reference parent (O.kind (O.body parentValue))) support childFound needed attached) sameOwner)
