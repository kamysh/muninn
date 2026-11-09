{-# OPTIONS --safe #-}
-- Protection survives the existing fixed frame; it is not reclassified away.
module Muninn.CleanupProtection where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.CleanupEffects as Effects
import Muninn.CleanupProgress as Progress
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false)
open import Data.String using (String)
open import Data.List using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (just)
open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
module DB = O.DB

module Model (excluded : List String → String → Bool) where
  module M = E.Model excluded

  holderIsMetadata : ∀ value ref → ref ∈ M.heldReferences value → E.indexed value ≡ false
  holderIsMetadata value ref present with E.classify (O.body value)
  ... | E.holder = refl
  ... | E.administrative with present
  ...   | ()
  holderIsMetadata value ref present | E.artifact with present
  ... | ()
  holderIsMetadata value ref present | E.baselineAnchor with present
  ... | ()
  holderIsMetadata value ref present | E.baselineBinding path with present
  ... | ()
  holderIsMetadata value ref present | E.checkoutBinding selected path with present
  ... | ()
  holderIsMetadata value ref present | E.snapshot selected with present
  ... | ()
  holderIsMetadata value ref present | E.legacyFile path with present
  ... | ()
  holderIsMetadata value ref present | E.graphContainer selected inUse with present
  ... | ()
  holderIsMetadata value ref present | E.attached parent gate with present
  ... | ()

  temporaryParentStable : ∀ selection before after value →
    M.parentOf M.temporary selection before value ≡ M.parentOf M.temporary selection after value
  temporaryParentStable selection before after value with E.classify (O.body value)
  ... | E.administrative = refl
  ... | E.holder = refl
  ... | E.artifact = refl
  ... | E.baselineAnchor = refl
  ... | E.baselineBinding path = refl
  ... | E.checkoutBinding selected path = refl
  ... | E.snapshot selected = refl
  ... | E.legacyFile path = refl
  ... | E.graphContainer selected inUse = refl
  ... | E.attached parent gate = refl

  protectedResolves : ∀ selection before after source ref → M.Safety selection before after →
    M.Protected selection before (O.target ref) → O.Resolves before source ref → O.Resolves after source ref
  protectedResolves selection before after source ref safe pinned resolved = record
    { value = O.Resolves.value resolved
    ; found = M.Safety.protected safe (O.target ref) (O.Resolves.value resolved) (O.Resolves.found resolved) pinned
    ; rightKind = O.Resolves.rightKind resolved; rightOwner = O.Resolves.rightOwner resolved }

  holdingParentStable : ∀ flag selection before after value →
    M.parentOf (M.temporaryFor flag) selection before value ≡ M.parentOf (M.temporaryFor flag) selection after value
  holdingParentStable true selection before after value = refl
  holdingParentStable false selection before after value = temporaryParentStable selection before after value

  mutual
    protectedSurvives : ∀ selection before after key → M.Safety selection before after →
      M.Protected selection before key → M.Protected selection after key
    protectedSurvives selection before after key safe pin@(M.held source value ref found included resolved) =
      M.held source value ref (M.Safety.metadata safe source value found (holderIsMetadata value ref included))
        included (protectedResolves selection before after (O.owner value) ref safe pin resolved)
    protectedSurvives selection before after key safe pin@(M.required previous (M.reference source value ref found included resolved)) =
      M.requireReference source value ref (protectedSurvives selection before after source safe previous)
        (M.Safety.protected safe source value found previous)
        (subst (λ refs → ref ∈ refs) (M.holdingReferences (M.readerOrigin previous) selection before value) included)
        (protectedResolves selection before after (O.owner value) ref safe pin resolved)
    protectedSurvives selection before after key safe pin@(M.required previous
      (M.attachment parent parentValue child childValue parentFound childFound attached sameOwner)) =
      M.required (protectedSurvives selection before after parent safe previous)
        (subst (λ mode → M.Dependency mode selection after parent child)
          (cong M.temporaryFor (sym (readerSurvives selection before after parent safe previous)))
          (M.attachment parent parentValue child childValue
            (M.Safety.protected safe parent parentValue parentFound previous)
            (M.Safety.protected safe child childValue childFound pin)
            (trans (sym (holdingParentStable (M.readerOrigin previous) selection before after childValue)) attached) sameOwner))

    readerSurvives : ∀ selection before after key (safe : M.Safety selection before after) (pin : M.Protected selection before key) →
      M.readerOrigin (protectedSurvives selection before after key safe pin) ≡ M.readerOrigin pin
    readerSurvives selection before after key safe (M.held source value ref found included resolved) = refl
    readerSurvives selection before after key safe (M.required previous (M.reference source value ref found included resolved)) =
      readerSurvives selection before after source safe previous
    readerSurvives selection before after key safe (M.required previous (M.attachment parent parentValue child childValue parentFound childFound attached sameOwner)) =
      readerSurvives selection before after parent safe previous

  module Trace (selection : E.Rule) (accepted : O.World) (intent : M.Intent selection accepted) where
    module Pass = Progress.Model.Pass excluded selection accepted intent
    module Core = Effects.Model.Core excluded selection accepted intent

    protectionAcrossTrace : ∀ {count before after} → Pass.Trace count before after → ∀ key →
      M.Protected selection before key → M.Protected selection after key
    protectionAcrossTrace (Pass.stop world) key pinned = pinned
    protectionAcrossTrace (Pass.edit chosen before ready later) key pinned = protectionAcrossTrace later key
      (protectedSurvives selection before (Pass.next chosen before) key (Core.transactionSafety chosen before) pinned)

    originalProtectedRecord : ∀ {count before after} → Pass.Trace count before after → ∀ key value →
      DB.lookup key before ≡ just value → M.Protected selection before key → DB.lookup key after ≡ just value
    originalProtectedRecord (Pass.stop world) key value found pinned = found
    originalProtectedRecord (Pass.edit chosen before ready later) key value found pinned = originalProtectedRecord later key value
      (M.Safety.protected (Core.transactionSafety chosen before) key value found pinned)
      (protectedSurvives selection before (Pass.next chosen before) key (Core.transactionSafety chosen before) pinned)
