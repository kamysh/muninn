{-# OPTIONS --safe #-}
module Muninn.CleanupReleased where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.CleanupEffects as Effects
import Muninn.CleanupProgress as Progress
import Muninn.CleanupCompletion as Completion
import Muninn.CleanupAlignment as Alignment
import Muninn.CleanupProtection as Protection
import Muninn.CleanupObservations as Observations
import Muninn.CleanupReverseNeed as ReverseNeed
import Muninn.CleanupNeed as Need
import Muninn.CleanupStorage as Storage
import Muninn.CleanupHistory as History
import Muninn.CleanupViews as Views
import Muninn.ExclusionClassifier as Classifier
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false)
open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
module DB = O.DB

filterAll : ∀ keep keys → (∀ key → key ∈ keys → keep key ≡ true) → E.filterKeys keep keys ≡ keys
filterAll keep [] positive = refl
filterAll keep (key ∷ keys) positive rewrite positive key (here refl) = cong (key ∷_) (filterAll keep keys (λ k present → positive k (there present)))

module Model where
  module M = E.Model
  module Obs = Observations.Model
  module Pins = Protection.Model
  module Needs = Need.Model
  module Store = Storage.Model
  module View = Views.Model
  module BackNeed = ReverseNeed.Model

  heldRaw : ∀ value ref → ref ∈ M.heldReferences value → ref ∈ O.references (O.body value)
  heldRaw value ref present with E.classify (O.body value)
  ... | E.holder = present
  ... | E.administrative with present
  ...   | ()
  heldRaw value ref present | E.artifact with present
  ... | ()
  heldRaw value ref present | E.baselineAnchor with present
  ... | ()
  heldRaw value ref present | E.baselineBinding path gitDefault with present
  ... | ()
  heldRaw value ref present | E.checkoutBinding selected path with present
  ... | ()
  heldRaw value ref present | E.snapshot selected with present
  ... | ()
  heldRaw value ref present | E.legacyFile path gitDefault with present
  ... | ()
  heldRaw value ref present | E.graphContainer selected inUse with present
  ... | ()
  heldRaw value ref present | E.attached parent gate with present
  ... | ()

  temporaryChildPlain : ∀ selection world value ref → M.parentOf M.temporary selection world value ≡ just ref → Storage.PlainKind value
  temporaryChildPlain selection world value ref attached with Observations.snapshotView value
  ... | Observations.plain nonSnapshot = nonSnapshot
  ... | Observations.snapshot owner selected nodes edges payload with attached
  ...   | ()

  temporaryChildPlain selection world value ref attached | Observations.delta owner selected version path answer with attached
  ... | ()

  holdingChildPlain : ∀ flag selection world value ref → M.parentOf (M.temporaryFor flag) selection world value ≡ just ref → Storage.PlainKind value
  holdingChildPlain true selection world value ref ()
  holdingChildPlain false selection world value ref attached = temporaryChildPlain selection world value ref attached

  module Loop (selection : E.Rule) (accepted : O.World) (intent : M.Intent selection accepted) where
    module Pass = Progress.Model.Pass selection accepted intent
    module Core = Effects.Model.Core selection accepted intent
    module Final = Completion.Model.Contract selection accepted intent
    module Aligned = Alignment.Model.Contract selection accepted intent
    module Hist = History.Model.History selection accepted intent
    module Steps = Obs.Step selection accepted intent

    metadataEarlier : ∀ chosen before key value → DB.lookup key (Pass.next chosen before) ≡ just value → E.indexed value ≡ false → DB.lookup key before ≡ just value
    metadataEarlier chosen before key value found metadata with Aligned.stepOrigin chosen before key value found
    ... | BackNeed.origin original present same = trans present (cong just (just-injective (trans
      (sym (M.Safety.metadata (Core.transactionSafety chosen before) key original present
        (trans (sym (cong E.indexedRole (Needs.projectionClass selection before value original same))) metadata))) found)))

    protectedEarlier : ∀ chosen before key value → DB.lookup key (Pass.next chosen before) ≡ just value → M.Protected selection before key → DB.lookup key before ≡ just value
    protectedEarlier chosen before key value found protected with Aligned.stepOrigin chosen before key value found
    ... | BackNeed.origin original present same = trans present (cong just (just-injective (trans
      (sym (M.Safety.protected (Core.transactionSafety chosen before) key original present protected)) found)))

    mutual
      protectedBackward : ∀ chosen before → O.Admissible before → ∀ key → M.Protected selection (Pass.next chosen before) key → M.Protected selection before key
      protectedBackward chosen before valid key (M.held source value ref found included resolved) =
        M.held source value ref earlier included
          (All.lookup (Storage.lookupAll before source value (O.Admissible.sound valid) earlier) (heldRaw value ref included))
        where earlier = metadataEarlier chosen before source value found (Pins.holderIsMetadata value ref included)
      protectedBackward chosen before valid key (M.required previous (M.reference source value ref found included resolved)) =
        M.requireReference source value ref (protectedBackward chosen before valid source previous) earlier raw
          (All.lookup (Storage.lookupAll before source value (O.Admissible.sound valid) earlier) raw)
        where
        earlier = protectedEarlier chosen before source value found (protectedBackward chosen before valid source previous)
        raw = subst (λ refs → ref ∈ refs) (M.holdingReferences (M.readerOrigin previous) selection (Pass.next chosen before) value) included
      protectedBackward chosen before valid key (M.required previous
        (M.attachment parent parentValue child childValue parentFound childFound attached sameOwner)) =
        M.required (protectedBackward chosen before valid parent previous)
          (subst (λ mode → M.Dependency mode selection before parent child)
            (cong M.temporaryFor (sym (readerBackward chosen before valid parent previous)))
            (M.attachment parent parentValue child childValue
              (protectedEarlier chosen before parent parentValue parentFound (protectedBackward chosen before valid parent previous))
              (Obs.Support.backwardPlain (Steps.stepSupport chosen before valid) child childValue childFound
                (holdingChildPlain (M.readerOrigin previous) selection (Pass.next chosen before) childValue (O.reference parent (O.kind (O.body parentValue))) attached))
              (trans (Pins.holdingParentStable (M.readerOrigin previous) selection before (Pass.next chosen before) childValue) attached) sameOwner))

      readerBackward : ∀ chosen before (valid : O.Admissible before) key (pin : M.Protected selection (Pass.next chosen before) key) →
        M.readerOrigin (protectedBackward chosen before valid key pin) ≡ M.readerOrigin pin
      readerBackward chosen before valid key (M.held source value ref found included resolved) = refl
      readerBackward chosen before valid key (M.required previous (M.reference source value ref found included resolved)) = readerBackward chosen before valid source previous
      readerBackward chosen before valid key (M.required previous (M.attachment parent parentValue child childValue parentFound childFound attached sameOwner)) =
        readerBackward chosen before valid parent previous

    canonicalPositive : ∀ before after key value → O.Admissible before → Obs.Support selection before after →
      DB.lookup key before ≡ just value → M.Needed selection before key → M.project selection before value ≡ value → M.project selection after value ≡ value
    canonicalPositive before after key value valid support found needed canonical with Observations.snapshotView value
    ... | Observations.plain nonSnapshot = Obs.projectionPlain selection after value nonSnapshot
    ... | Observations.snapshot owner selected nodes edges payload with E.ownerEqual owner (E.targetOwner selection) in decision
    ...   | no different = refl
    ...   | yes refl = cong₂ (λ ns es → O.recordOf (E.targetOwner selection) (O.structuralSnapshot selected ns es payload))
        (filterAll (M.symbolVisible selection after (E.targetOwner selection) selected) nodes nodeVisible)
        (filterAll (M.edgeVisible selection after (E.targetOwner selection) selected) edges edgeVisible)
      where
      nodeBefore : ∀ member → member ∈ nodes → M.symbolVisible selection before (E.targetOwner selection) selected member ≡ true
      nodeBefore member present = E.filterKeysSound (M.symbolVisible selection before (E.targetOwner selection) selected) nodes member
        (subst (λ keys → member ∈ keys) (sym (cong E.snapshotNodes canonical)) present)
      edgeBefore : ∀ member → member ∈ edges → M.edgeVisible selection before (E.targetOwner selection) selected member ≡ true
      edgeBefore member present = E.filterKeysSound (M.edgeVisible selection before (E.targetOwner selection) selected) edges member
        (subst (λ keys → member ∈ keys) (sym (cong E.snapshotEdges canonical)) present)
      nodeVisible : ∀ member → member ∈ nodes → M.symbolVisible selection after (E.targetOwner selection) selected member ≡ true
      nodeVisible member present = View.View.symbolPositive selection before after selected member support
        (Hist.nodeNeeded before key selected nodes edges payload member valid found needed present (nodeBefore member present)) (nodeBefore member present)
      edgeVisible : ∀ member → member ∈ edges → M.edgeVisible selection after (E.targetOwner selection) selected member ≡ true
      edgeVisible member present = View.View.edgePositive selection before after selected member valid support
        (Hist.edgeNeeded before key selected nodes edges payload member valid found needed present (edgeBefore member present)) (edgeBefore member present)

    canonicalPositive before after key value valid support found needed canonical | Observations.delta owner selected version path answer =
      trans (sym (Store.projectWorldIndependent selection before after value (λ ()))) canonical

    Released : O.World → Set
    Released world = ∀ key → Final.Pending key world → ¬ M.Protected selection world key

    releasedStep : ∀ chosen before → O.Admissible before → Released before → Released (Pass.next chosen before)
    releasedStep chosen before valid released key pending@(value , found , captured , owned , indexed , remaining) protected
      with Classifier.Model.Assessment.needed? selection before key
    ... | no unneeded = released key (value , earlier , captured , owned , indexed , inj₁ unneeded) originalProtection
      where
      originalProtection = protectedBackward chosen before valid key protected
      earlier = protectedEarlier chosen before key value found originalProtection
    ... | yes needed with Final.projectionView before value
    ...   | inj₂ (owner , index , changed) = released key (value , earlier , captured , owned , indexed , inj₂ (needed , changed)) originalProtection
      where
      originalProtection = protectedBackward chosen before valid key protected
      earlier = protectedEarlier chosen before key value found originalProtection
    ...   | inj₁ canonical with remaining
    ...     | inj₁ unneeded = unneeded (Needs.neededSurvives selection before (Pass.next chosen before) key valid (Steps.stepSupport chosen before valid) needed)
    ...     | inj₂ (laterNeeded , changed) = Core.changedIsActual (Pass.next chosen before) value changed
        (canonicalPositive before (Pass.next chosen before) key value valid (Steps.stepSupport chosen before valid)
          (protectedEarlier chosen before key value found (protectedBackward chosen before valid key protected)) needed canonical)

    releasedTrace : ∀ {count before after} → Pass.Trace count before after → O.Admissible before → Released before → Released after
    releasedTrace (Pass.stop world) valid released = released
    releasedTrace (Pass.edit chosen before ready later) valid released = releasedTrace later (Core.transactionAdmissible chosen before valid)
      (releasedStep chosen before valid released)
