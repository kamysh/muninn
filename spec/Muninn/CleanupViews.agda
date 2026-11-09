{-# OPTIONS --safe #-}
module Muninn.CleanupViews where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.CleanupObservations as Observations
import Muninn.CleanupNeedScope as Scope
import Muninn.CleanupCompletion as Completion
import Muninn.CleanupStorage as Storage
import Muninn.CleanupOrder
import Muninn.ReceiptTypes as Receipt
open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (Bool; true; false; not; _∧_; if_then_else_)
open import Data.String using (String)
import Data.String as String
open import Data.List using (List; [])
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
module DB = O.DB

andBoth : ∀ {a b} → a ≡ true → b ≡ true → a ∧ b ≡ true
andBoth = cong₂ _∧_

notTrueFalse : ∀ b → not b ≡ true → b ≡ false
notTrueFalse false proof = refl
notTrueFalse true ()

module Model (excluded : List String → String → Bool) where
  module M = E.Model excluded
  module Support = Observations.Model excluded

  module View (selection : E.Rule) where
    includedAtTarget : ∀ path → M.included selection (E.targetOwner selection) path ≡ not (excluded (E.exclusions selection) path)
    includedAtTarget path with E.ownerEqual (E.targetOwner selection) (E.targetOwner selection)
    ... | yes same = refl
    ... | no different = ⊥-elim (different refl)

    ownedRooted : ∀ world value → O.owner value ≡ E.targetOwner selection → M.rootedRole selection world (E.classify (O.body value)) ≡ true → M.rooted selection world value ≡ true
    ownedRooted world value owned rooted with E.ownerEqual (O.owner value) (E.targetOwner selection)
    ... | yes same = rooted
    ... | no different = ⊥-elim (different owned)

    bindingIdentity : ∀ world owner selected path version value → M.bindingValue selection world owner selected path version value ≡ true →
      (O.owner value ≡ owner) × (O.kind (O.body value) ≢ O.structuralSnapshotK)

    bindingIdentity world owner selected path version (O.recordOf storedOwner (O.registration _)) ()
    bindingIdentity world owner selected path version (O.recordOf storedOwner (O.checkout _)) ()
    bindingIdentity world owner selected path version (O.recordOf storedOwner (O.creationIntent _)) ()
    bindingIdentity world owner selected path version (O.recordOf storedOwner (O.defaults _)) ()
    bindingIdentity world owner selected path version (O.recordOf storedOwner (O.policyVersion _ _)) ()
    bindingIdentity world owner selected path version (O.recordOf storedOwner (O.currentPolicy _)) ()
    bindingIdentity world owner selected path version (O.recordOf storedOwner (O.note _)) ()
    bindingIdentity world owner selected path version (O.recordOf storedOwner (O.notePosting _ _)) ()
    bindingIdentity world owner selected path version (O.recordOf storedOwner (O.noteVector _ _)) ()
    bindingIdentity world owner selected path version (O.recordOf storedOwner (O.fileVersion _)) ()
    bindingIdentity world owner selected path version (O.recordOf storedOwner (O.basePointer _)) ()
    bindingIdentity world owner selected path version (O.recordOf storedOwner (O.chunk _ _)) ()
    bindingIdentity world owner selected path version (O.recordOf storedOwner (O.posting _ _)) ()
    bindingIdentity world owner selected path version (O.recordOf storedOwner (O.vector _ _)) ()
    bindingIdentity world owner selected path version (O.recordOf storedOwner (O.symbol _ _ _)) ()
    bindingIdentity world owner selected path version (O.recordOf storedOwner (O.edge _ _ _)) ()
    bindingIdentity world owner selected path version (O.recordOf storedOwner (O.structuralSnapshot _ _ _ _)) ()
    bindingIdentity world owner selected path version (O.recordOf storedOwner (O.legacy _ _)) ()
    bindingIdentity world owner selected path version (O.recordOf storedOwner (O.staging _ _)) ()
    bindingIdentity world owner selected path version (O.recordOf storedOwner (O.acceptedWork _ _)) ()
    bindingIdentity world owner selected path version (O.recordOf storedOwner (O.cleanupWork _ _ _)) ()
    bindingIdentity world owner selected path version (O.recordOf storedOwner (O.activeReader _ _)) ()
    bindingIdentity world owner selected path version (O.recordOf storedOwner (O.continuation _ _)) ()
    bindingIdentity world owner selected path version (O.recordOf storedOwner (O.receipt _)) ()
    bindingIdentity world owner selected path version (O.recordOf storedOwner (O.migration _)) ()
    bindingIdentity world owner selected path version (O.recordOf storedOwner (O.usage _)) ()
    bindingIdentity world owner selected path version (O.recordOf storedOwner (O.bootstrap _)) ()
    bindingIdentity world owner selected path version (O.recordOf storedOwner (O.modelCache _)) ()
    bindingIdentity world owner selected path version (O.recordOf storedOwner (O.coordination _)) ()
    bindingIdentity world owner selected path version (O.recordOf storedOwner (O.schemaResource _)) ()
    bindingIdentity world owner selected path version (O.recordOf storedOwner (O.graphResource _ _ _)) ()
    bindingIdentity world owner selected path version (O.recordOf storedOwner (O.logFile _)) ()
    bindingIdentity world owner selected path version (O.recordOf storedOwner (O.bootstrapStage _)) ()
    bindingIdentity world owner selected path version (O.recordOf storedOwner (O.baseBinding storedVersion storedPath)) positive =
      sym (Completion.decisionWitness (E.ownerEqual owner storedOwner) ((Scope.andLeft (E.sameOwner owner storedOwner) ((Relation.Nullary.does (path String.≟ storedPath)) ∧ ((E.sameNat version storedVersion) ∧ (not (M.hasDelta owner selected path world)))) (positive)))) , (λ ())
    bindingIdentity world owner selected path version (O.recordOf storedOwner (O.deltaBinding checkout nothing storedPath)) ()
    bindingIdentity world owner selected path version (O.recordOf storedOwner (O.deltaBinding checkout (just storedVersion) storedPath)) positive =
      sym (Completion.decisionWitness (E.ownerEqual owner storedOwner) ((Scope.andLeft (E.sameOwner owner storedOwner) ((E.sameNat checkout selected) ∧ ((Relation.Nullary.does (path String.≟ storedPath)) ∧ (E.sameNat version storedVersion))) (positive)))) , (λ ())

    bindingRoot : ∀ world selected path version value → M.familyRegistered selection world ≡ true →
      M.checkoutLive selection world selected ≡ true → M.included selection (E.targetOwner selection) path ≡ true →
      M.bindingValue selection world (E.targetOwner selection) selected path version value ≡ true → M.rooted selection world value ≡ true

    bindingRoot world selected path version (O.recordOf storedOwner (O.registration _)) registered live included ()
    bindingRoot world selected path version (O.recordOf storedOwner (O.checkout _)) registered live included ()
    bindingRoot world selected path version (O.recordOf storedOwner (O.creationIntent _)) registered live included ()
    bindingRoot world selected path version (O.recordOf storedOwner (O.defaults _)) registered live included ()
    bindingRoot world selected path version (O.recordOf storedOwner (O.policyVersion _ _)) registered live included ()
    bindingRoot world selected path version (O.recordOf storedOwner (O.currentPolicy _)) registered live included ()
    bindingRoot world selected path version (O.recordOf storedOwner (O.note _)) registered live included ()
    bindingRoot world selected path version (O.recordOf storedOwner (O.notePosting _ _)) registered live included ()
    bindingRoot world selected path version (O.recordOf storedOwner (O.noteVector _ _)) registered live included ()
    bindingRoot world selected path version (O.recordOf storedOwner (O.fileVersion _)) registered live included ()
    bindingRoot world selected path version (O.recordOf storedOwner (O.basePointer _)) registered live included ()
    bindingRoot world selected path version (O.recordOf storedOwner (O.chunk _ _)) registered live included ()
    bindingRoot world selected path version (O.recordOf storedOwner (O.posting _ _)) registered live included ()
    bindingRoot world selected path version (O.recordOf storedOwner (O.vector _ _)) registered live included ()
    bindingRoot world selected path version (O.recordOf storedOwner (O.symbol _ _ _)) registered live included ()
    bindingRoot world selected path version (O.recordOf storedOwner (O.edge _ _ _)) registered live included ()
    bindingRoot world selected path version (O.recordOf storedOwner (O.structuralSnapshot _ _ _ _)) registered live included ()
    bindingRoot world selected path version (O.recordOf storedOwner (O.legacy _ _)) registered live included ()
    bindingRoot world selected path version (O.recordOf storedOwner (O.staging _ _)) registered live included ()
    bindingRoot world selected path version (O.recordOf storedOwner (O.acceptedWork _ _)) registered live included ()
    bindingRoot world selected path version (O.recordOf storedOwner (O.cleanupWork _ _ _)) registered live included ()
    bindingRoot world selected path version (O.recordOf storedOwner (O.activeReader _ _)) registered live included ()
    bindingRoot world selected path version (O.recordOf storedOwner (O.continuation _ _)) registered live included ()
    bindingRoot world selected path version (O.recordOf storedOwner (O.receipt _)) registered live included ()
    bindingRoot world selected path version (O.recordOf storedOwner (O.migration _)) registered live included ()
    bindingRoot world selected path version (O.recordOf storedOwner (O.usage _)) registered live included ()
    bindingRoot world selected path version (O.recordOf storedOwner (O.bootstrap _)) registered live included ()
    bindingRoot world selected path version (O.recordOf storedOwner (O.modelCache _)) registered live included ()
    bindingRoot world selected path version (O.recordOf storedOwner (O.coordination _)) registered live included ()
    bindingRoot world selected path version (O.recordOf storedOwner (O.schemaResource _)) registered live included ()
    bindingRoot world selected path version (O.recordOf storedOwner (O.graphResource _ _ _)) registered live included ()
    bindingRoot world selected path version (O.recordOf storedOwner (O.logFile _)) registered live included ()
    bindingRoot world selected path version (O.recordOf storedOwner (O.bootstrapStage _)) registered live included ()
    bindingRoot world selected path version (O.recordOf storedOwner (O.baseBinding storedVersion storedPath)) registered live included positive
      with Completion.decisionWitness (E.ownerEqual (E.targetOwner selection) storedOwner) ((Scope.andLeft (E.sameOwner (E.targetOwner selection) storedOwner) ((Relation.Nullary.does (path String.≟ storedPath)) ∧ ((E.sameNat version storedVersion) ∧ (not (M.hasDelta (E.targetOwner selection) selected path world)))) (positive)))
    ... | refl with Completion.decisionWitness (path String.≟ storedPath) ((Scope.andLeft (Relation.Nullary.does (path String.≟ storedPath)) ((E.sameNat version storedVersion) ∧ (not (M.hasDelta (E.targetOwner selection) selected path world))) (Scope.andRight (E.sameOwner (E.targetOwner selection) storedOwner) ((Relation.Nullary.does (path String.≟ storedPath)) ∧ ((E.sameNat version storedVersion) ∧ (not (M.hasDelta (E.targetOwner selection) selected path world)))) (positive))))
    ...   | refl = ownedRooted world (O.recordOf (E.targetOwner selection) (O.baseBinding storedVersion path)) refl
      (andBoth registered (andBoth (Support.checkoutImpliesAny selection world selected live) included))
    bindingRoot world selected path version (O.recordOf storedOwner (O.deltaBinding checkout nothing storedPath)) registered live included ()
    bindingRoot world selected path version (O.recordOf storedOwner (O.deltaBinding checkout (just storedVersion) storedPath)) registered live included positive
      with Completion.decisionWitness (E.ownerEqual (E.targetOwner selection) storedOwner) ((Scope.andLeft (E.sameOwner (E.targetOwner selection) storedOwner) ((E.sameNat checkout selected) ∧ ((Relation.Nullary.does (path String.≟ storedPath)) ∧ (E.sameNat version storedVersion))) (positive)))
    ... | refl with Completion.decisionWitness (checkout ≟ selected) ((Scope.andLeft (E.sameNat checkout selected) ((Relation.Nullary.does (path String.≟ storedPath)) ∧ (E.sameNat version storedVersion)) (Scope.andRight (E.sameOwner (E.targetOwner selection) storedOwner) ((E.sameNat checkout selected) ∧ ((Relation.Nullary.does (path String.≟ storedPath)) ∧ (E.sameNat version storedVersion))) (positive))))
    ...   | refl with Completion.decisionWitness (path String.≟ storedPath) ((Scope.andLeft (Relation.Nullary.does (path String.≟ storedPath)) (E.sameNat version storedVersion) (Scope.andRight (E.sameNat checkout selected) ((Relation.Nullary.does (path String.≟ storedPath)) ∧ (E.sameNat version storedVersion)) (Scope.andRight (E.sameOwner (E.targetOwner selection) storedOwner) ((E.sameNat checkout selected) ∧ ((Relation.Nullary.does (path String.≟ storedPath)) ∧ (E.sameNat version storedVersion))) (positive)))))
    ...     | refl = ownedRooted world (O.recordOf (E.targetOwner selection) (O.deltaBinding selected (just storedVersion) path)) refl
      (andBoth registered (andBoth live included))

    bindingForward : ∀ before after owner selected path version value → Support.Support selection before after →
      M.bindingValue selection before owner selected path version value ≡ true → M.bindingValue selection after owner selected path version value ≡ true

    bindingForward before after owner selected path version (O.recordOf storedOwner (O.registration _)) support ()
    bindingForward before after owner selected path version (O.recordOf storedOwner (O.checkout _)) support ()
    bindingForward before after owner selected path version (O.recordOf storedOwner (O.creationIntent _)) support ()
    bindingForward before after owner selected path version (O.recordOf storedOwner (O.defaults _)) support ()
    bindingForward before after owner selected path version (O.recordOf storedOwner (O.policyVersion _ _)) support ()
    bindingForward before after owner selected path version (O.recordOf storedOwner (O.currentPolicy _)) support ()
    bindingForward before after owner selected path version (O.recordOf storedOwner (O.note _)) support ()
    bindingForward before after owner selected path version (O.recordOf storedOwner (O.notePosting _ _)) support ()
    bindingForward before after owner selected path version (O.recordOf storedOwner (O.noteVector _ _)) support ()
    bindingForward before after owner selected path version (O.recordOf storedOwner (O.fileVersion _)) support ()
    bindingForward before after owner selected path version (O.recordOf storedOwner (O.basePointer _)) support ()
    bindingForward before after owner selected path version (O.recordOf storedOwner (O.chunk _ _)) support ()
    bindingForward before after owner selected path version (O.recordOf storedOwner (O.posting _ _)) support ()
    bindingForward before after owner selected path version (O.recordOf storedOwner (O.vector _ _)) support ()
    bindingForward before after owner selected path version (O.recordOf storedOwner (O.symbol _ _ _)) support ()
    bindingForward before after owner selected path version (O.recordOf storedOwner (O.edge _ _ _)) support ()
    bindingForward before after owner selected path version (O.recordOf storedOwner (O.structuralSnapshot _ _ _ _)) support ()
    bindingForward before after owner selected path version (O.recordOf storedOwner (O.legacy _ _)) support ()
    bindingForward before after owner selected path version (O.recordOf storedOwner (O.staging _ _)) support ()
    bindingForward before after owner selected path version (O.recordOf storedOwner (O.acceptedWork _ _)) support ()
    bindingForward before after owner selected path version (O.recordOf storedOwner (O.cleanupWork _ _ _)) support ()
    bindingForward before after owner selected path version (O.recordOf storedOwner (O.activeReader _ _)) support ()
    bindingForward before after owner selected path version (O.recordOf storedOwner (O.continuation _ _)) support ()
    bindingForward before after owner selected path version (O.recordOf storedOwner (O.receipt _)) support ()
    bindingForward before after owner selected path version (O.recordOf storedOwner (O.migration _)) support ()
    bindingForward before after owner selected path version (O.recordOf storedOwner (O.usage _)) support ()
    bindingForward before after owner selected path version (O.recordOf storedOwner (O.bootstrap _)) support ()
    bindingForward before after owner selected path version (O.recordOf storedOwner (O.modelCache _)) support ()
    bindingForward before after owner selected path version (O.recordOf storedOwner (O.coordination _)) support ()
    bindingForward before after owner selected path version (O.recordOf storedOwner (O.schemaResource _)) support ()
    bindingForward before after owner selected path version (O.recordOf storedOwner (O.graphResource _ _ _)) support ()
    bindingForward before after owner selected path version (O.recordOf storedOwner (O.logFile _)) support ()
    bindingForward before after owner selected path version (O.recordOf storedOwner (O.bootstrapStage _)) support ()
    bindingForward before after owner selected path version (O.recordOf storedOwner (O.baseBinding storedVersion storedPath)) support positive =
      andBoth ((Scope.andLeft (E.sameOwner owner storedOwner) ((Relation.Nullary.does (path String.≟ storedPath)) ∧ ((E.sameNat version storedVersion) ∧ (not (M.hasDelta owner selected path before)))) (positive))) (andBoth ((Scope.andLeft (Relation.Nullary.does (path String.≟ storedPath)) ((E.sameNat version storedVersion) ∧ (not (M.hasDelta owner selected path before))) (Scope.andRight (E.sameOwner owner storedOwner) ((Relation.Nullary.does (path String.≟ storedPath)) ∧ ((E.sameNat version storedVersion) ∧ (not (M.hasDelta owner selected path before)))) (positive))))
        (andBoth ((Scope.andLeft (E.sameNat version storedVersion) (not (M.hasDelta owner selected path before)) (Scope.andRight (Relation.Nullary.does (path String.≟ storedPath)) ((E.sameNat version storedVersion) ∧ (not (M.hasDelta owner selected path before))) (Scope.andRight (E.sameOwner owner storedOwner) ((Relation.Nullary.does (path String.≟ storedPath)) ∧ ((E.sameNat version storedVersion) ∧ (not (M.hasDelta owner selected path before)))) (positive)))))
          (cong not (Support.deltaAbsence selection before after owner selected path support
            (notTrueFalse _ ((Scope.andRight (E.sameNat version storedVersion) (not (M.hasDelta owner selected path before)) (Scope.andRight (Relation.Nullary.does (path String.≟ storedPath)) ((E.sameNat version storedVersion) ∧ (not (M.hasDelta owner selected path before))) (Scope.andRight (E.sameOwner owner storedOwner) ((Relation.Nullary.does (path String.≟ storedPath)) ∧ ((E.sameNat version storedVersion) ∧ (not (M.hasDelta owner selected path before)))) (positive))))))))))
    bindingForward before after owner selected path version (O.recordOf storedOwner (O.deltaBinding checkout nothing storedPath)) support ()
    bindingForward before after owner selected path version (O.recordOf storedOwner (O.deltaBinding checkout (just storedVersion) storedPath)) support positive = positive

    retainBinding : ∀ before after key value owner selected path version → Support.Support selection before after →
      DB.lookup key before ≡ just value → (owner ≡ E.targetOwner selection → M.familyRegistered selection before ≡ true) →
      M.checkoutLive selection before selected ≡ true → M.included selection owner path ≡ true →
      M.bindingValue selection before owner selected path version value ≡ true → DB.lookup key after ≡ just value
    retainBinding before after key value owner selected path version support found registered live included positive
      with bindingIdentity before owner selected path version value positive | E.ownerEqual owner (E.targetOwner selection)
    ... | sameOwner , nonSnapshot | no different = M.Safety.unrelated (Support.Support.safe support) key value found
        (λ owned → different (trans (sym sameOwner) owned))
    ... | sameOwner , nonSnapshot | yes refl = Support.neededSame selection before after key value (Support.Support.safe support) found
      (M.root key value found (bindingRoot before selected path version value (registered refl) live (trans (includedAtTarget path) included) positive)) nonSnapshot

    versionPositive : ∀ before after owner selected path version → Support.Support selection before after →
      (owner ≡ E.targetOwner selection → M.familyRegistered selection before ≡ true) →
      M.versionAtPath selection before owner selected path version ≡ true → M.versionAtPath selection after owner selected path version ≡ true
    versionPositive before after owner selected path version support registered positive
      with Observations.anyWitness (λ key value → M.bindingValue selection before owner selected path version value) before
        ((Scope.andRight (M.included selection owner path) (E.anyRow (λ key value → M.bindingValue selection before owner selected path version value) before) (Scope.andRight (M.checkoutLive selection before selected) ((M.included selection owner path) ∧ (E.anyRow (λ key value → M.bindingValue selection before owner selected path version value) before)) (positive))))
    ... | (key , value) , present , selectedBinding = andBoth
      (Support.checkoutPositive selection before after selected support ((Scope.andLeft (M.checkoutLive selection before selected) ((M.included selection owner path) ∧ (E.anyRow (λ key value → M.bindingValue selection before owner selected path version value) before)) (positive))))
      (andBoth ((Scope.andLeft (M.included selection owner path) (E.anyRow (λ key value → M.bindingValue selection before owner selected path version value) before) (Scope.andRight (M.checkoutLive selection before selected) ((M.included selection owner path) ∧ (E.anyRow (λ key value → M.bindingValue selection before owner selected path version value) before)) (positive))))
        (Observations.anyPresent (λ key value → M.bindingValue selection after owner selected path version value) after key value
          (Observations.lookupMember after key value (retainBinding before after key value owner selected path version support
            (Muninn.CleanupOrder.memberLookup before key value (Support.Support.uniqueBefore support) present) registered
            ((Scope.andLeft (M.checkoutLive selection before selected) ((M.included selection owner path) ∧ (E.anyRow (λ key value → M.bindingValue selection before owner selected path version value) before)) (positive))) ((Scope.andLeft (M.included selection owner path) (E.anyRow (λ key value → M.bindingValue selection before owner selected path version value) before) (Scope.andRight (M.checkoutLive selection before selected) ((M.included selection owner path) ∧ (E.anyRow (λ key value → M.bindingValue selection before owner selected path version value) before)) (positive)))) selectedBinding))
          (bindingForward before after owner selected path version value support selectedBinding)))

    publishedMetadata : ∀ world owner path version key value → M.checkoutVersionValue selection world owner path version key value ≡ true → E.indexed value ≡ false

    publishedMetadata world owner path version key (O.recordOf storedOwner (O.registration _)) ()
    publishedMetadata world owner path version key (O.recordOf storedOwner (O.checkout info)) positive = refl
    publishedMetadata world owner path version key (O.recordOf storedOwner (O.creationIntent _)) ()
    publishedMetadata world owner path version key (O.recordOf storedOwner (O.defaults _)) ()
    publishedMetadata world owner path version key (O.recordOf storedOwner (O.policyVersion _ _)) ()
    publishedMetadata world owner path version key (O.recordOf storedOwner (O.currentPolicy _)) ()
    publishedMetadata world owner path version key (O.recordOf storedOwner (O.note _)) ()
    publishedMetadata world owner path version key (O.recordOf storedOwner (O.notePosting _ _)) ()
    publishedMetadata world owner path version key (O.recordOf storedOwner (O.noteVector _ _)) ()
    publishedMetadata world owner path version key (O.recordOf storedOwner (O.fileVersion _)) ()
    publishedMetadata world owner path version key (O.recordOf storedOwner (O.baseBinding _ _)) ()
    publishedMetadata world owner path version key (O.recordOf storedOwner (O.deltaBinding _ _ _)) ()
    publishedMetadata world owner path version key (O.recordOf storedOwner (O.basePointer _)) ()
    publishedMetadata world owner path version key (O.recordOf storedOwner (O.chunk _ _)) ()
    publishedMetadata world owner path version key (O.recordOf storedOwner (O.posting _ _)) ()
    publishedMetadata world owner path version key (O.recordOf storedOwner (O.vector _ _)) ()
    publishedMetadata world owner path version key (O.recordOf storedOwner (O.symbol _ _ _)) ()
    publishedMetadata world owner path version key (O.recordOf storedOwner (O.edge _ _ _)) ()
    publishedMetadata world owner path version key (O.recordOf storedOwner (O.structuralSnapshot _ _ _ _)) ()
    publishedMetadata world owner path version key (O.recordOf storedOwner (O.legacy _ _)) ()
    publishedMetadata world owner path version key (O.recordOf storedOwner (O.staging _ _)) ()
    publishedMetadata world owner path version key (O.recordOf storedOwner (O.acceptedWork _ _)) ()
    publishedMetadata world owner path version key (O.recordOf storedOwner (O.cleanupWork _ _ _)) ()
    publishedMetadata world owner path version key (O.recordOf storedOwner (O.activeReader _ _)) ()
    publishedMetadata world owner path version key (O.recordOf storedOwner (O.continuation _ _)) ()
    publishedMetadata world owner path version key (O.recordOf storedOwner (O.receipt _)) ()
    publishedMetadata world owner path version key (O.recordOf storedOwner (O.migration _)) ()
    publishedMetadata world owner path version key (O.recordOf storedOwner (O.usage _)) ()
    publishedMetadata world owner path version key (O.recordOf storedOwner (O.bootstrap _)) ()
    publishedMetadata world owner path version key (O.recordOf storedOwner (O.modelCache _)) ()
    publishedMetadata world owner path version key (O.recordOf storedOwner (O.coordination _)) ()
    publishedMetadata world owner path version key (O.recordOf storedOwner (O.schemaResource _)) ()
    publishedMetadata world owner path version key (O.recordOf storedOwner (O.graphResource _ _ _)) ()
    publishedMetadata world owner path version key (O.recordOf storedOwner (O.logFile _)) ()
    publishedMetadata world owner path version key (O.recordOf storedOwner (O.bootstrapStage _)) ()

    publishedForward : ∀ before after owner path version key value → Support.Support selection before after →
      (owner ≡ E.targetOwner selection → M.familyRegistered selection before ≡ true) →
      M.checkoutVersionValue selection before owner path version key value ≡ true → M.checkoutVersionValue selection after owner path version key value ≡ true

    publishedForward before after owner path version key (O.recordOf storedOwner (O.registration _)) support registered ()
    publishedForward before after owner path version key (O.recordOf storedOwner (O.checkout info)) support registered positive =
      andBoth ((Scope.andLeft (E.sameOwner owner storedOwner) (M.versionAtPath selection before owner key path version) (positive))) (versionPositive before after owner key path version support registered ((Scope.andRight (E.sameOwner owner storedOwner) (M.versionAtPath selection before owner key path version) (positive))))
    publishedForward before after owner path version key (O.recordOf storedOwner (O.creationIntent _)) support registered ()
    publishedForward before after owner path version key (O.recordOf storedOwner (O.defaults _)) support registered ()
    publishedForward before after owner path version key (O.recordOf storedOwner (O.policyVersion _ _)) support registered ()
    publishedForward before after owner path version key (O.recordOf storedOwner (O.currentPolicy _)) support registered ()
    publishedForward before after owner path version key (O.recordOf storedOwner (O.note _)) support registered ()
    publishedForward before after owner path version key (O.recordOf storedOwner (O.notePosting _ _)) support registered ()
    publishedForward before after owner path version key (O.recordOf storedOwner (O.noteVector _ _)) support registered ()
    publishedForward before after owner path version key (O.recordOf storedOwner (O.fileVersion _)) support registered ()
    publishedForward before after owner path version key (O.recordOf storedOwner (O.baseBinding _ _)) support registered ()
    publishedForward before after owner path version key (O.recordOf storedOwner (O.deltaBinding _ _ _)) support registered ()
    publishedForward before after owner path version key (O.recordOf storedOwner (O.basePointer _)) support registered ()
    publishedForward before after owner path version key (O.recordOf storedOwner (O.chunk _ _)) support registered ()
    publishedForward before after owner path version key (O.recordOf storedOwner (O.posting _ _)) support registered ()
    publishedForward before after owner path version key (O.recordOf storedOwner (O.vector _ _)) support registered ()
    publishedForward before after owner path version key (O.recordOf storedOwner (O.symbol _ _ _)) support registered ()
    publishedForward before after owner path version key (O.recordOf storedOwner (O.edge _ _ _)) support registered ()
    publishedForward before after owner path version key (O.recordOf storedOwner (O.structuralSnapshot _ _ _ _)) support registered ()
    publishedForward before after owner path version key (O.recordOf storedOwner (O.legacy _ _)) support registered ()
    publishedForward before after owner path version key (O.recordOf storedOwner (O.staging _ _)) support registered ()
    publishedForward before after owner path version key (O.recordOf storedOwner (O.acceptedWork _ _)) support registered ()
    publishedForward before after owner path version key (O.recordOf storedOwner (O.cleanupWork _ _ _)) support registered ()
    publishedForward before after owner path version key (O.recordOf storedOwner (O.activeReader _ _)) support registered ()
    publishedForward before after owner path version key (O.recordOf storedOwner (O.continuation _ _)) support registered ()
    publishedForward before after owner path version key (O.recordOf storedOwner (O.receipt _)) support registered ()
    publishedForward before after owner path version key (O.recordOf storedOwner (O.migration _)) support registered ()
    publishedForward before after owner path version key (O.recordOf storedOwner (O.usage _)) support registered ()
    publishedForward before after owner path version key (O.recordOf storedOwner (O.bootstrap _)) support registered ()
    publishedForward before after owner path version key (O.recordOf storedOwner (O.modelCache _)) support registered ()
    publishedForward before after owner path version key (O.recordOf storedOwner (O.coordination _)) support registered ()
    publishedForward before after owner path version key (O.recordOf storedOwner (O.schemaResource _)) support registered ()
    publishedForward before after owner path version key (O.recordOf storedOwner (O.graphResource _ _ _)) support registered ()
    publishedForward before after owner path version key (O.recordOf storedOwner (O.logFile _)) support registered ()
    publishedForward before after owner path version key (O.recordOf storedOwner (O.bootstrapStage _)) support registered ()

    publishedPositive : ∀ before after owner path version → Support.Support selection before after →
      (owner ≡ E.targetOwner selection → M.familyRegistered selection before ≡ true) →
      M.versionPublishedAtPath selection before owner path version ≡ true → M.versionPublishedAtPath selection after owner path version ≡ true
    publishedPositive before after owner path version support registered positive
      with Observations.anyWitness (M.checkoutVersionValue selection before owner path version) before positive
    ... | (key , value) , present , selected = Observations.anyPresent (M.checkoutVersionValue selection after owner path version) after key value
      (Observations.lookupMember after key value (M.Safety.metadata (Support.Support.safe support) key value
        (Muninn.CleanupOrder.memberLookup before key value (Support.Support.uniqueBefore support) present)
        (publishedMetadata before owner path version key value selected)))
      (publishedForward before after owner path version key value support registered selected)

    symbolNonSnapshot : ∀ world selected value → M.symbolObservation selection world (E.targetOwner selection) selected (just value) ≡ true → O.kind (O.body value) ≢ O.structuralSnapshotK
    symbolNonSnapshot world selected value positive with Observations.snapshotView value
    ... | Observations.plain nonSnapshot = nonSnapshot
    ... | Observations.snapshot owner checkout nodes edges payload with positive
    ...   | ()

    symbolForward : ∀ before after selected key value → Support.Support selection before after → DB.lookup key before ≡ just value →
      M.Needed selection before key → M.symbolObservation selection before (E.targetOwner selection) selected (just value) ≡ true →
      M.symbolObservation selection after (E.targetOwner selection) selected (just value) ≡ true

    symbolForward before after selected key (O.recordOf storedOwner (O.registration _)) support found needed ()
    symbolForward before after selected key (O.recordOf storedOwner (O.checkout _)) support found needed ()
    symbolForward before after selected key (O.recordOf storedOwner (O.creationIntent _)) support found needed ()
    symbolForward before after selected key (O.recordOf storedOwner (O.defaults _)) support found needed ()
    symbolForward before after selected key (O.recordOf storedOwner (O.policyVersion _ _)) support found needed ()
    symbolForward before after selected key (O.recordOf storedOwner (O.currentPolicy _)) support found needed ()
    symbolForward before after selected key (O.recordOf storedOwner (O.note _)) support found needed ()
    symbolForward before after selected key (O.recordOf storedOwner (O.notePosting _ _)) support found needed ()
    symbolForward before after selected key (O.recordOf storedOwner (O.noteVector _ _)) support found needed ()
    symbolForward before after selected key (O.recordOf storedOwner (O.fileVersion _)) support found needed ()
    symbolForward before after selected key (O.recordOf storedOwner (O.baseBinding _ _)) support found needed ()
    symbolForward before after selected key (O.recordOf storedOwner (O.deltaBinding _ _ _)) support found needed ()
    symbolForward before after selected key (O.recordOf storedOwner (O.basePointer _)) support found needed ()
    symbolForward before after selected key (O.recordOf storedOwner (O.chunk _ _)) support found needed ()
    symbolForward before after selected key (O.recordOf storedOwner (O.posting _ _)) support found needed ()
    symbolForward before after selected key (O.recordOf storedOwner (O.vector _ _)) support found needed ()
    symbolForward before after selected key (O.recordOf storedOwner (O.symbol version path payload)) support found needed positive =
      andBoth ((Scope.andLeft (E.sameOwner (E.targetOwner selection) storedOwner) (M.versionAtPath selection before (E.targetOwner selection) selected path version) (positive)))
        (versionPositive before after (E.targetOwner selection) selected path version support (λ owned → registered) ((Scope.andRight (E.sameOwner (E.targetOwner selection) storedOwner) (M.versionAtPath selection before (E.targetOwner selection) selected path version) (positive))))
      where
      registered : M.familyRegistered selection before ≡ true
      registered = Scope.Model.neededRegistration excluded selection before key (O.recordOf storedOwner (O.symbol version path payload)) found
        (sym (Completion.decisionWitness (E.ownerEqual (E.targetOwner selection) storedOwner) ((Scope.andLeft (E.sameOwner (E.targetOwner selection) storedOwner) (M.versionAtPath selection before (E.targetOwner selection) selected path version) (positive))))) refl needed
    symbolForward before after selected key (O.recordOf storedOwner (O.edge _ _ _)) support found needed ()
    symbolForward before after selected key (O.recordOf storedOwner (O.structuralSnapshot _ _ _ _)) support found needed ()
    symbolForward before after selected key (O.recordOf storedOwner (O.legacy _ _)) support found needed ()
    symbolForward before after selected key (O.recordOf storedOwner (O.staging _ _)) support found needed ()
    symbolForward before after selected key (O.recordOf storedOwner (O.acceptedWork _ _)) support found needed ()
    symbolForward before after selected key (O.recordOf storedOwner (O.cleanupWork _ _ _)) support found needed ()
    symbolForward before after selected key (O.recordOf storedOwner (O.activeReader _ _)) support found needed ()
    symbolForward before after selected key (O.recordOf storedOwner (O.continuation _ _)) support found needed ()
    symbolForward before after selected key (O.recordOf storedOwner (O.receipt _)) support found needed ()
    symbolForward before after selected key (O.recordOf storedOwner (O.migration _)) support found needed ()
    symbolForward before after selected key (O.recordOf storedOwner (O.usage _)) support found needed ()
    symbolForward before after selected key (O.recordOf storedOwner (O.bootstrap _)) support found needed ()
    symbolForward before after selected key (O.recordOf storedOwner (O.modelCache _)) support found needed ()
    symbolForward before after selected key (O.recordOf storedOwner (O.coordination _)) support found needed ()
    symbolForward before after selected key (O.recordOf storedOwner (O.schemaResource _)) support found needed ()
    symbolForward before after selected key (O.recordOf storedOwner (O.graphResource _ _ _)) support found needed ()
    symbolForward before after selected key (O.recordOf storedOwner (O.logFile _)) support found needed ()
    symbolForward before after selected key (O.recordOf storedOwner (O.bootstrapStage _)) support found needed ()

    symbolPositive : ∀ before after selected key → Support.Support selection before after → M.Needed selection before key →
      M.symbolVisible selection before (E.targetOwner selection) selected key ≡ true → M.symbolVisible selection after (E.targetOwner selection) selected key ≡ true
    symbolPositive before after selected key support needed positive with DB.lookup key before in found
    ... | nothing with positive
    ...   | ()
    symbolPositive before after selected key support needed positive | just value = trans
      (cong (M.symbolObservation selection after (E.targetOwner selection) selected)
        (Support.neededSame selection before after key value (Support.Support.safe support) found needed (symbolNonSnapshot before selected value positive)))
      (symbolForward before after selected key value support found needed positive)

    edgeNonSnapshot : ∀ world selected value → M.edgeObservation selection world (E.targetOwner selection) selected (just value) ≡ true → O.kind (O.body value) ≢ O.structuralSnapshotK
    edgeNonSnapshot world selected value positive with Observations.snapshotView value
    ... | Observations.plain nonSnapshot = nonSnapshot
    ... | Observations.snapshot owner checkout nodes edges payload with positive
    ...   | ()

    edgeForward : ∀ before after selected key value → O.Admissible before → Support.Support selection before after → DB.lookup key before ≡ just value →
      M.Needed selection before key → M.edgeObservation selection before (E.targetOwner selection) selected (just value) ≡ true →
      M.edgeObservation selection after (E.targetOwner selection) selected (just value) ≡ true

    edgeForward before after selected key (O.recordOf storedOwner (O.registration _)) valid support found needed ()
    edgeForward before after selected key (O.recordOf storedOwner (O.checkout _)) valid support found needed ()
    edgeForward before after selected key (O.recordOf storedOwner (O.creationIntent _)) valid support found needed ()
    edgeForward before after selected key (O.recordOf storedOwner (O.defaults _)) valid support found needed ()
    edgeForward before after selected key (O.recordOf storedOwner (O.policyVersion _ _)) valid support found needed ()
    edgeForward before after selected key (O.recordOf storedOwner (O.currentPolicy _)) valid support found needed ()
    edgeForward before after selected key (O.recordOf storedOwner (O.note _)) valid support found needed ()
    edgeForward before after selected key (O.recordOf storedOwner (O.notePosting _ _)) valid support found needed ()
    edgeForward before after selected key (O.recordOf storedOwner (O.noteVector _ _)) valid support found needed ()
    edgeForward before after selected key (O.recordOf storedOwner (O.fileVersion _)) valid support found needed ()
    edgeForward before after selected key (O.recordOf storedOwner (O.baseBinding _ _)) valid support found needed ()
    edgeForward before after selected key (O.recordOf storedOwner (O.deltaBinding _ _ _)) valid support found needed ()
    edgeForward before after selected key (O.recordOf storedOwner (O.basePointer _)) valid support found needed ()
    edgeForward before after selected key (O.recordOf storedOwner (O.chunk _ _)) valid support found needed ()
    edgeForward before after selected key (O.recordOf storedOwner (O.posting _ _)) valid support found needed ()
    edgeForward before after selected key (O.recordOf storedOwner (O.vector _ _)) valid support found needed ()
    edgeForward before after selected key (O.recordOf storedOwner (O.symbol _ _ _)) valid support found needed ()
    edgeForward before after selected key value@(O.recordOf storedOwner (O.edge source target payload)) valid support found needed positive =
      andBoth ((Scope.andLeft (E.sameOwner (E.targetOwner selection) storedOwner) ((M.symbolVisible selection before (E.targetOwner selection) selected source) ∧ (M.symbolVisible selection before (E.targetOwner selection) selected target)) (positive)))
        (andBoth (symbolPositive before after selected source support sourceNeeded ((Scope.andLeft (M.symbolVisible selection before (E.targetOwner selection) selected source) (M.symbolVisible selection before (E.targetOwner selection) selected target) (Scope.andRight (E.sameOwner (E.targetOwner selection) storedOwner) ((M.symbolVisible selection before (E.targetOwner selection) selected source) ∧ (M.symbolVisible selection before (E.targetOwner selection) selected target)) (positive)))))
          (symbolPositive before after selected target support targetNeeded ((Scope.andRight (M.symbolVisible selection before (E.targetOwner selection) selected source) (M.symbolVisible selection before (E.targetOwner selection) selected target) (Scope.andRight (E.sameOwner (E.targetOwner selection) storedOwner) ((M.symbolVisible selection before (E.targetOwner selection) selected source) ∧ (M.symbolVisible selection before (E.targetOwner selection) selected target)) (positive))))))
      where
      refs : O.SoundReferences before (key , value)
      refs = Storage.lookupAll before key value (O.Admissible.sound valid) found
      sourceNeeded : M.Needed selection before source
      sourceNeeded = M.required needed (M.reference key value (O.reference source O.symbolK) found (here refl) (All.lookup refs (here refl)))
      targetNeeded : M.Needed selection before target
      targetNeeded = M.required needed (M.reference key value (O.reference target O.symbolK) found (there (here refl)) (All.lookup refs (there (here refl))))
    edgeForward before after selected key (O.recordOf storedOwner (O.structuralSnapshot _ _ _ _)) valid support found needed ()
    edgeForward before after selected key (O.recordOf storedOwner (O.legacy _ _)) valid support found needed ()
    edgeForward before after selected key (O.recordOf storedOwner (O.staging _ _)) valid support found needed ()
    edgeForward before after selected key (O.recordOf storedOwner (O.acceptedWork _ _)) valid support found needed ()
    edgeForward before after selected key (O.recordOf storedOwner (O.cleanupWork _ _ _)) valid support found needed ()
    edgeForward before after selected key (O.recordOf storedOwner (O.activeReader _ _)) valid support found needed ()
    edgeForward before after selected key (O.recordOf storedOwner (O.continuation _ _)) valid support found needed ()
    edgeForward before after selected key (O.recordOf storedOwner (O.receipt _)) valid support found needed ()
    edgeForward before after selected key (O.recordOf storedOwner (O.migration _)) valid support found needed ()
    edgeForward before after selected key (O.recordOf storedOwner (O.usage _)) valid support found needed ()
    edgeForward before after selected key (O.recordOf storedOwner (O.bootstrap _)) valid support found needed ()
    edgeForward before after selected key (O.recordOf storedOwner (O.modelCache _)) valid support found needed ()
    edgeForward before after selected key (O.recordOf storedOwner (O.coordination _)) valid support found needed ()
    edgeForward before after selected key (O.recordOf storedOwner (O.schemaResource _)) valid support found needed ()
    edgeForward before after selected key (O.recordOf storedOwner (O.graphResource _ _ _)) valid support found needed ()
    edgeForward before after selected key (O.recordOf storedOwner (O.logFile _)) valid support found needed ()
    edgeForward before after selected key (O.recordOf storedOwner (O.bootstrapStage _)) valid support found needed ()

    edgePositive : ∀ before after selected key → O.Admissible before → Support.Support selection before after → M.Needed selection before key →
      M.edgeVisible selection before (E.targetOwner selection) selected key ≡ true → M.edgeVisible selection after (E.targetOwner selection) selected key ≡ true
    edgePositive before after selected key valid support needed positive with DB.lookup key before in found
    ... | nothing with positive
    ...   | ()
    edgePositive before after selected key valid support needed positive | just value = trans
      (cong (M.edgeObservation selection after (E.targetOwner selection) selected)
        (Support.neededSame selection before after key value (Support.Support.safe support) found needed (edgeNonSnapshot before selected value positive)))
      (edgeForward before after selected key value valid support found needed positive)

    parentPositive : ∀ before after key value ref → Support.Support selection before after →
      DB.lookup key before ≡ just value → M.Needed selection before key →
      M.parentOf M.permanent selection before value ≡ just ref → M.parentOf M.permanent selection after value ≡ just ref
    parentPositive before after key (O.recordOf owner (O.registration _)) ref support found needed ()
    parentPositive before after key (O.recordOf owner (O.checkout _)) ref support found needed ()
    parentPositive before after key (O.recordOf owner (O.creationIntent _)) ref support found needed ()
    parentPositive before after key (O.recordOf owner (O.defaults _)) ref support found needed ()
    parentPositive before after key (O.recordOf owner (O.policyVersion _ _)) ref support found needed ()
    parentPositive before after key (O.recordOf owner (O.currentPolicy _)) ref support found needed ()
    parentPositive before after key (O.recordOf owner (O.note _)) ref support found needed ()
    parentPositive before after key (O.recordOf owner (O.notePosting _ _)) ref support found needed ()
    parentPositive before after key (O.recordOf owner (O.noteVector _ _)) ref support found needed ()
    parentPositive before after key (O.recordOf owner (O.fileVersion _)) ref support found needed ()
    parentPositive before after key (O.recordOf owner (O.baseBinding _ _)) ref support found needed ()
    parentPositive before after key (O.recordOf owner (O.deltaBinding _ _ _)) ref support found needed ()
    parentPositive before after key (O.recordOf owner (O.basePointer _)) ref support found needed ()
    parentPositive before after key (O.recordOf owner (O.chunk _ _)) ref support found needed parent = parent
    parentPositive before after key (O.recordOf owner (O.posting _ _)) ref support found needed parent = parent
    parentPositive before after key (O.recordOf owner (O.vector _ _)) ref support found needed parent = parent
    parentPositive before after key value@(O.recordOf owner (O.symbol version path payload)) ref support found needed parent
      with M.versionPublishedAtPath selection before owner path version in published
    ... | false with parent
    ...   | ()
    parentPositive before after key value@(O.recordOf owner (O.symbol version path payload)) ref support found needed parent | true =
      Relation.Binary.PropositionalEquality.subst
        (λ ready → (if ready then just (O.reference version O.fileVersionK) else nothing) ≡ just ref)
        (sym (publishedPositive before after owner path version support
          (λ owned → Scope.Model.neededRegistration excluded selection before key value found owned refl needed) published)) parent
    parentPositive before after key (O.recordOf owner (O.edge _ _ _)) ref support found needed ()
    parentPositive before after key (O.recordOf owner (O.structuralSnapshot _ _ _ _)) ref support found needed ()
    parentPositive before after key (O.recordOf owner (O.legacy _ _)) ref support found needed ()
    parentPositive before after key (O.recordOf owner (O.staging _ _)) ref support found needed ()
    parentPositive before after key (O.recordOf owner (O.acceptedWork _ _)) ref support found needed ()
    parentPositive before after key (O.recordOf owner (O.cleanupWork _ _ _)) ref support found needed ()
    parentPositive before after key (O.recordOf owner (O.activeReader _ _)) ref support found needed ()
    parentPositive before after key (O.recordOf owner (O.continuation _ _)) ref support found needed ()
    parentPositive before after key (O.recordOf owner (O.receipt (Receipt.entry id (Receipt.active input names work)))) ref support found needed ()
    parentPositive before after key (O.recordOf owner (O.receipt (Receipt.entry id (Receipt.finished input names reply)))) ref support found needed ()
    parentPositive before after key (O.recordOf owner (O.receipt (Receipt.entry id (Receipt.used)))) ref support found needed ()
    parentPositive before after key (O.recordOf owner (O.migration _)) ref support found needed ()
    parentPositive before after key (O.recordOf owner (O.usage _)) ref support found needed ()
    parentPositive before after key (O.recordOf owner (O.bootstrap _)) ref support found needed ()
    parentPositive before after key (O.recordOf owner (O.modelCache _)) ref support found needed ()
    parentPositive before after key (O.recordOf owner (O.coordination _)) ref support found needed ()
    parentPositive before after key (O.recordOf owner (O.schemaResource _)) ref support found needed ()
    parentPositive before after key (O.recordOf owner (O.graphResource _ _ _)) ref support found needed ()
    parentPositive before after key (O.recordOf owner (O.logFile _)) ref support found needed ()
    parentPositive before after key (O.recordOf owner (O.bootstrapStage _)) ref support found needed ()
