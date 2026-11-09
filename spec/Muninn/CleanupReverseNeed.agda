{-# OPTIONS --safe #-}
module Muninn.CleanupReverseNeed where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.CleanupObservations as Observations
import Muninn.CleanupViews as Views
import Muninn.CleanupReverseViews as ReverseViews
import Muninn.CleanupNeed as Need
import Muninn.CleanupNeedScope as Scope
import Muninn.CleanupStorage as Storage
import Muninn.ReceiptTypes as Receipt
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false; _∧_)
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
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
module DB = O.DB

boolSame : ∀ a b → (a ≡ true → b ≡ true) → (b ≡ true → a ≡ true) → a ≡ b
boolSame true b forward backward = sym (forward refl)
boolSame false false forward backward = refl
boolSame false true forward backward with backward refl
... | ()

module Model (excluded : List String → String → Bool) where
  module M = E.Model excluded
  module Obs = Observations.Model excluded
  module Needs = Need.Model excluded
  module Store = Storage.Model excluded
  module Targets = Scope.Model excluded
  module BackViews = ReverseViews.Model excluded

  record Origin (selection : E.Rule) (before : O.World) (key : ℕ) (value : O.Record) : Set where
    constructor origin
    field original : O.Record
          found : DB.lookup key before ≡ just original
          projected : M.project selection before value ≡ M.project selection before original

  parentProjection : ∀ selection world observed value →
    M.parentOf M.permanent selection world (M.project selection observed value) ≡ M.parentOf M.permanent selection world value
  parentProjection selection world observed value with Observations.snapshotView value
  ... | Observations.plain nonSnapshot = cong (M.parentOf M.permanent selection world) (Obs.projectionPlain selection observed value nonSnapshot)
  ... | Observations.snapshot owner selected nodes edges payload with E.ownerEqual owner (E.targetOwner selection)
  ...   | yes same = refl
  ...   | no different = refl

  module Reverse (selection : E.Rule) (before after : O.World) (support : Obs.Support selection before after)
    (registered : M.familyRegistered selection before ≡ true)
    (origins : ∀ key value → DB.lookup key after ≡ just value → Origin selection before key value) where
    module Back = BackViews.Reverse selection before after support

    registrationSame : M.familyRegistered selection before ≡ M.familyRegistered selection after
    registrationSame = boolSame (M.familyRegistered selection before) (M.familyRegistered selection after)
      (Obs.registrationPositive selection before after support) Back.registrationBackward
    legacySame : M.legacyReadable selection before ≡ M.legacyReadable selection after
    legacySame = boolSame (M.legacyReadable selection before) (M.legacyReadable selection after)
      (Obs.legacyPositive selection before after support) Back.legacyBackward
    anyCheckoutSame : M.anyCheckoutLive selection before ≡ M.anyCheckoutLive selection after
    anyCheckoutSame = boolSame (M.anyCheckoutLive selection before) (M.anyCheckoutLive selection after)
      (Obs.anyCheckoutPositive selection before after support) Back.anyCheckoutBackward
    checkoutSame : ∀ key → M.checkoutLive selection before key ≡ M.checkoutLive selection after key
    checkoutSame key = boolSame (M.checkoutLive selection before key) (M.checkoutLive selection after key)
      (Obs.checkoutPositive selection before after key support) (Back.checkoutBackward key)

    roleSame : ∀ role → M.rootedRole selection before role ≡ M.rootedRole selection after role
    roleSame E.administrative = refl
    roleSame E.holder = refl
    roleSame E.artifact = refl
    roleSame (E.attached parent gate) = refl
    roleSame E.baselineAnchor = cong₂ _∧_ registrationSame anyCheckoutSame
    roleSame (E.baselineBinding path) = cong₂ _∧_ registrationSame (cong (λ live → live ∧ M.included selection (E.targetOwner selection) path) anyCheckoutSame)
    roleSame (E.checkoutBinding selected path) = cong₂ _∧_ registrationSame (cong (λ live → live ∧ M.included selection (E.targetOwner selection) path) (checkoutSame selected))
    roleSame (E.snapshot selected) = cong₂ _∧_ registrationSame (checkoutSame selected)
    roleSame (E.legacyFile path) = cong₂ _∧_ registrationSame (cong (λ live → live ∧ M.included selection (E.targetOwner selection) path) legacySame)
    roleSame (E.graphContainer Data.Maybe.nothing inUse) = cong (inUse ∧_) (cong₂ _∧_ registrationSame anyCheckoutSame)
    roleSame (E.graphContainer (just selected) inUse) = cong (inUse ∧_) (cong₂ _∧_ registrationSame (checkoutSame selected))

    rootSame : ∀ value → M.rooted selection before value ≡ M.rooted selection after value
    rootSame value with E.ownerEqual (O.owner value) (E.targetOwner selection)
    ... | no different = refl
    ... | yes same = roleSame (E.classify (O.body value))

    projectedRefsBackward : ∀ value ref → ref ∈ O.references (O.body (M.project selection after value)) →
      ref ∈ O.references (O.body (M.project selection before value))
    projectedRefsBackward value ref present with Observations.snapshotView value
    ... | Observations.plain nonSnapshot = subst (λ v → ref ∈ O.references (O.body v))
      (trans (Obs.projectionPlain selection after value nonSnapshot) (sym (Obs.projectionPlain selection before value nonSnapshot))) present
    ... | Observations.snapshot owner selected nodes edges payload with E.ownerEqual owner (E.targetOwner selection)
    ...   | no different = present
    ...   | yes same with present
    ...     | here equal = here equal
    ...     | there later with ∈-++⁻ (map (λ key → O.reference key O.symbolK)
        (E.filterKeys (M.symbolVisible selection after owner selected) nodes)) later
    ...       | inj₁ node with ∈-map⁻ (λ key → O.reference key O.symbolK) node
    ...         | key , filtered , refl = there (∈-++⁺ˡ (∈-map⁺ (λ key → O.reference key O.symbolK)
        (E.filterKeysComplete (M.symbolVisible selection before owner selected) nodes key (Storage.filterSubset _ nodes key filtered)
          (Back.symbolBackward owner selected key registered (E.filterKeysSound _ nodes key filtered)))))
    projectedRefsBackward value ref present | Observations.snapshot owner selected nodes edges payload | yes same | there later | inj₂ edge
      with ∈-map⁻ (λ key → O.reference key O.edgeK) edge
    ... | key , filtered , refl = there (∈-++⁺ʳ (map (λ key → O.reference key O.symbolK)
        (E.filterKeys (M.symbolVisible selection before owner selected) nodes))
      (∈-map⁺ (λ key → O.reference key O.edgeK)
        (E.filterKeysComplete (M.edgeVisible selection before owner selected) edges key (Storage.filterSubset _ edges key filtered)
          (Back.edgeBackward owner selected key registered (E.filterKeysSound _ edges key filtered)))))

    refsBackward : ∀ original value ref → M.project selection before value ≡ M.project selection before original →
      ref ∈ M.referencesFor M.permanent selection after value → ref ∈ M.referencesFor M.permanent selection before original
    refsBackward original value ref same present = subst (λ refs → ref ∈ refs)
      (sym (Needs.refsNotHolder selection before original originalNotHolder))
      (subst (λ v → ref ∈ O.references (O.body v)) same
        (projectedRefsBackward value ref (subst (λ refs → ref ∈ refs) (Needs.refsNotHolder selection after value valueNotHolder) present)))
      where
      valueNotHolder = Needs.memberNotHolder selection after value ref present
      originalNotHolder : E.classify (O.body original) ≢ E.holder
      originalNotHolder equal = valueNotHolder (trans (Needs.projectionClass selection before value original same) equal)

    parentBackward : ∀ value ref → M.parentOf M.permanent selection after value ≡ just ref → M.parentOf M.permanent selection before value ≡ just ref
    parentBackward (O.recordOf owner (O.registration _)) ref ()
    parentBackward (O.recordOf owner (O.checkout _)) ref ()
    parentBackward (O.recordOf owner (O.creationIntent _)) ref ()
    parentBackward (O.recordOf owner (O.defaults _)) ref ()
    parentBackward (O.recordOf owner (O.policyVersion _ _)) ref ()
    parentBackward (O.recordOf owner (O.currentPolicy _)) ref ()
    parentBackward (O.recordOf owner (O.note _)) ref ()
    parentBackward (O.recordOf owner (O.notePosting _ _)) ref ()
    parentBackward (O.recordOf owner (O.noteVector _ _)) ref ()
    parentBackward (O.recordOf owner (O.fileVersion _)) ref ()
    parentBackward (O.recordOf owner (O.baseBinding _ _)) ref ()
    parentBackward (O.recordOf owner (O.deltaBinding _ _ _)) ref ()
    parentBackward (O.recordOf owner (O.basePointer _)) ref ()
    parentBackward (O.recordOf owner (O.edge _ _ _)) ref ()
    parentBackward (O.recordOf owner (O.structuralSnapshot _ _ _ _)) ref ()
    parentBackward (O.recordOf owner (O.legacy _ _)) ref ()
    parentBackward (O.recordOf owner (O.staging _ _)) ref ()
    parentBackward (O.recordOf owner (O.acceptedWork _ _)) ref ()
    parentBackward (O.recordOf owner (O.cleanupWork _ _ _)) ref ()
    parentBackward (O.recordOf owner (O.activeReader _ _)) ref ()
    parentBackward (O.recordOf owner (O.continuation _ _)) ref ()
    parentBackward (O.recordOf owner (O.receipt (Receipt.entry id (Receipt.active input names work)))) ref ()
    parentBackward (O.recordOf owner (O.receipt (Receipt.entry id (Receipt.finished input names reply)))) ref ()
    parentBackward (O.recordOf owner (O.receipt (Receipt.entry id (Receipt.used)))) ref ()
    parentBackward (O.recordOf owner (O.migration _)) ref ()
    parentBackward (O.recordOf owner (O.usage _)) ref ()
    parentBackward (O.recordOf owner (O.bootstrap _)) ref ()
    parentBackward (O.recordOf owner (O.modelCache _)) ref ()
    parentBackward (O.recordOf owner (O.coordination _)) ref ()
    parentBackward (O.recordOf owner (O.schemaResource _)) ref ()
    parentBackward (O.recordOf owner (O.graphResource _ _ _)) ref ()
    parentBackward (O.recordOf owner (O.publishedView _ _)) ref ()
    parentBackward (O.recordOf owner (O.logFile _)) ref ()
    parentBackward (O.recordOf owner (O.bootstrapStage _)) ref ()
    parentBackward (O.recordOf owner (O.chunk version payload)) ref parent = parent
    parentBackward (O.recordOf owner (O.posting chunk payload)) ref parent = parent
    parentBackward (O.recordOf owner (O.vector chunk payload)) ref parent = parent
    parentBackward (O.recordOf owner (O.symbol version path payload)) ref parent
      with M.versionPublishedAtPath selection after owner path version in published
    ... | true rewrite Back.publishedBackward owner path version registered published = parent
    ... | false with parent
    ...   | ()

    resolveBackward : ∀ source ref → O.Resolves after source ref → O.Resolves before source ref
    resolveBackward source ref resolved with origins (O.target ref) (O.Resolves.value resolved) (O.Resolves.found resolved)
    ... | origin original present same = record
      { value = original; found = present
      ; rightKind = trans (sym (Needs.projectionKind selection before (O.Resolves.value resolved) original same)) (O.Resolves.rightKind resolved)
      ; rightOwner = subst (O.MayReference source)
          (Needs.projectionOwner selection before (O.Resolves.value resolved) original same) (O.Resolves.rightOwner resolved) }

    neededBackward : ∀ key → M.Needed selection after key → M.Needed selection before key
    neededBackward key (M.root .key value found rooted) with origins key value found
    ... | origin original present same = M.root key original present (trans
      (cong₂ (M.rootedFrom selection before) (sym (Needs.projectionOwner selection before value original same))
        (sym (Needs.projectionClass selection before value original same))) (trans (rootSame value) rooted))
    neededBackward key (M.required previous (M.reference source value ref found included resolved))
      with origins source value found
    ... | origin original present same = M.required (neededBackward source previous)
      (M.reference source original ref present (refsBackward original value ref same included)
        (subst (λ sourceOwner → O.Resolves before sourceOwner ref)
          (Needs.projectionOwner selection before value original same)
          (resolveBackward (O.owner value) ref resolved)))
    neededBackward key (M.required previous (M.attachment parent parentValue child childValue parentFound childFound attached sameOwner)) =
      M.required (neededBackward parent previous)
        (M.attachment parent parentValue child childValue
          (Obs.Support.backwardPlain support parent parentValue parentFound
            (Targets.parentNotSnapshot selection after childValue (O.reference parent (O.kind (O.body parentValue))) attached))
          (Obs.Support.backwardPlain support child childValue childFound
            (Needs.attachedNonSnapshot selection after childValue (O.reference parent (O.kind (O.body parentValue))) attached))
          (parentBackward childValue (O.reference parent (O.kind (O.body parentValue))) attached) sameOwner)
