{-# OPTIONS --safe #-}
module Muninn.CleanupReverseViews where

import Muninn.OwnedState as O
import Muninn.ReceiptTypes as Receipt
import Muninn.ExclusionOutcomes as E
import Muninn.CleanupObservations as Observations
import Muninn.CleanupViews as Views
import Muninn.CleanupNeedScope as Scope
import Muninn.CleanupCompletion as Completion
import Muninn.CleanupOrder as Order
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false; not; _∧_)
open import Data.String using (String)
import Data.String as String
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
module DB = O.DB

parts : ∀ a b → a ∧ b ≡ true → (a ≡ true) × (b ≡ true)
parts a b positive = Scope.andLeft a b positive , Scope.andRight a b positive

module Model (excluded : List String → String → Bool) where
  module M = E.Model excluded
  module Obs = Observations.Model excluded
  module View = Views.Model excluded

  module Reverse (selection : E.Rule) (before after : O.World) (support : Obs.Support selection before after) where
    anyBackward : ∀ test →
      (∀ key owner selected nodes edges payload → test key (O.recordOf owner (O.structuralSnapshot selected nodes edges payload)) ≡ false) →
      E.anyRow test after ≡ true → E.anyRow test before ≡ true
    anyBackward test ignore positive with Observations.anyWitness test after positive
    ... | (key , value) , present , selected with Observations.snapshotView value
    ...   | Observations.snapshot owner checkout nodes edges payload = ⊥-elim
        (Observations.falseNotTrue (trans (sym (ignore key owner checkout nodes edges payload)) selected))
    ...   | Observations.plain nonSnapshot = Observations.anyPresent test before key value
        (Observations.lookupMember before key value (Obs.Support.backwardPlain support key value
          (Order.memberLookup after key value (Obs.Support.uniqueAfter support) present) nonSnapshot)) selected

    registrationBackward : M.familyRegistered selection after ≡ true → M.familyRegistered selection before ≡ true
    registrationBackward = anyBackward (λ key value → M.registeredValue selection value) (λ key owner selected nodes edges payload → refl)

    legacyBackward : M.legacyReadable selection after ≡ true → M.legacyReadable selection before ≡ true
    legacyBackward = anyBackward (λ key value → M.legacyValue selection value) (λ key owner selected nodes edges payload → refl)

    anyCheckoutBackward : M.anyCheckoutLive selection after ≡ true → M.anyCheckoutLive selection before ≡ true
    anyCheckoutBackward = anyBackward (λ key value → M.liveValue selection value) (λ key owner selected nodes edges payload → refl)

    checkoutBackward : ∀ key → M.checkoutLive selection after key ≡ true → M.checkoutLive selection before key ≡ true
    checkoutBackward key positive with DB.lookup key after in found
    ... | nothing with positive
    ...   | ()
    checkoutBackward key positive | just value with Observations.snapshotView value
    ... | Observations.plain nonSnapshot = trans
        (cong (M.checkoutObservation selection) (Obs.Support.backwardPlain support key value found nonSnapshot)) positive
    ... | Observations.snapshot owner selected nodes edges payload with positive
    ...   | ()

    deltaRoot : ∀ owner selected path value → M.familyRegistered selection before ≡ true →
      M.checkoutLive selection before selected ≡ true → M.included selection owner path ≡ true →
      M.deltaValue owner selected path value ≡ true → M.rooted selection before value ≡ true
    deltaRoot owner selected path (O.recordOf storedOwner (O.registration _)) registered live included ()
    deltaRoot owner selected path (O.recordOf storedOwner (O.checkout _)) registered live included ()
    deltaRoot owner selected path (O.recordOf storedOwner (O.creationIntent _)) registered live included ()
    deltaRoot owner selected path (O.recordOf storedOwner (O.defaults _)) registered live included ()
    deltaRoot owner selected path (O.recordOf storedOwner (O.policyVersion _ _)) registered live included ()
    deltaRoot owner selected path (O.recordOf storedOwner (O.currentPolicy _)) registered live included ()
    deltaRoot owner selected path (O.recordOf storedOwner (O.note _)) registered live included ()
    deltaRoot owner selected path (O.recordOf storedOwner (O.notePosting _ _)) registered live included ()
    deltaRoot owner selected path (O.recordOf storedOwner (O.noteVector _ _)) registered live included ()
    deltaRoot owner selected path (O.recordOf storedOwner (O.fileVersion _)) registered live included ()
    deltaRoot owner selected path (O.recordOf storedOwner (O.baseBinding _ _)) registered live included ()
    deltaRoot owner selected path (O.recordOf storedOwner (O.basePointer _)) registered live included ()
    deltaRoot owner selected path (O.recordOf storedOwner (O.chunk _ _)) registered live included ()
    deltaRoot owner selected path (O.recordOf storedOwner (O.posting _ _)) registered live included ()
    deltaRoot owner selected path (O.recordOf storedOwner (O.vector _ _)) registered live included ()
    deltaRoot owner selected path (O.recordOf storedOwner (O.symbol _ _ _)) registered live included ()
    deltaRoot owner selected path (O.recordOf storedOwner (O.edge _ _ _)) registered live included ()
    deltaRoot owner selected path (O.recordOf storedOwner (O.structuralSnapshot _ _ _ _)) registered live included ()
    deltaRoot owner selected path (O.recordOf storedOwner (O.legacy _ _)) registered live included ()
    deltaRoot owner selected path (O.recordOf storedOwner (O.staging _ _)) registered live included ()
    deltaRoot owner selected path (O.recordOf storedOwner (O.acceptedWork _ _)) registered live included ()
    deltaRoot owner selected path (O.recordOf storedOwner (O.cleanupWork _ _ _)) registered live included ()
    deltaRoot owner selected path (O.recordOf storedOwner (O.activeReader _ _)) registered live included ()
    deltaRoot owner selected path (O.recordOf storedOwner (O.continuation _ _)) registered live included ()
    deltaRoot owner selected path (O.recordOf storedOwner (O.receipt (Receipt.entry id (Receipt.active input names work)))) registered live included ()
    deltaRoot owner selected path (O.recordOf storedOwner (O.receipt (Receipt.entry id (Receipt.finished input names reply)))) registered live included ()
    deltaRoot owner selected path (O.recordOf storedOwner (O.receipt (Receipt.entry id (Receipt.used)))) registered live included ()
    deltaRoot owner selected path (O.recordOf storedOwner (O.migration _)) registered live included ()
    deltaRoot owner selected path (O.recordOf storedOwner (O.usage _)) registered live included ()
    deltaRoot owner selected path (O.recordOf storedOwner (O.bootstrap _)) registered live included ()
    deltaRoot owner selected path (O.recordOf storedOwner (O.modelCache _)) registered live included ()
    deltaRoot owner selected path (O.recordOf storedOwner (O.coordination _)) registered live included ()
    deltaRoot owner selected path (O.recordOf storedOwner (O.schemaResource _)) registered live included ()
    deltaRoot owner selected path (O.recordOf storedOwner (O.graphResource _ _ _)) registered live included ()
    deltaRoot owner selected path (O.recordOf storedOwner (O.logFile _)) registered live included ()
    deltaRoot owner selected path (O.recordOf storedOwner (O.bootstrapStage _)) registered live included ()
    deltaRoot owner selected path (O.recordOf storedOwner (O.deltaBinding checkout version storedPath)) registered live included positive
      with parts (E.sameOwner owner storedOwner) (E.sameNat selected checkout ∧ Relation.Nullary.does (path String.≟ storedPath)) positive
    ... | owners , rest with parts (E.sameNat selected checkout) (Relation.Nullary.does (path String.≟ storedPath)) rest
    ... | checkouts , paths with Completion.decisionWitness (E.ownerEqual owner storedOwner) owners
      | Completion.decisionWitness (Data.Nat._≟_ selected checkout) checkouts | Completion.decisionWitness (path String.≟ storedPath) paths
    ... | refl | refl | refl with E.ownerEqual storedOwner (E.targetOwner selection)
    ... | no different = refl
    ... | yes same = Views.andBoth registered (Views.andBoth live (trans (View.View.includedAtTarget selection storedPath) included))

    deltaRetained : ∀ owner selected path key value → M.familyRegistered selection before ≡ true →
      M.checkoutLive selection before selected ≡ true → M.included selection owner path ≡ true →
      DB.lookup key before ≡ just value → M.deltaValue owner selected path value ≡ true → DB.lookup key after ≡ just value
    deltaRetained owner selected path key value registered live included found positive with Observations.snapshotView value
    ... | Observations.plain nonSnapshot = Obs.neededSame selection before after key value (Obs.Support.safe support) found
        (M.root key value found (deltaRoot owner selected path value registered live included positive)) nonSnapshot
    ... | Observations.snapshot storedOwner checkout nodes edges payload with positive
    ...   | ()

    deltaAbsenceBackward : ∀ owner selected path → M.familyRegistered selection before ≡ true →
      M.checkoutLive selection before selected ≡ true → M.included selection owner path ≡ true →
      M.hasDelta owner selected path after ≡ false → M.hasDelta owner selected path before ≡ false
    deltaAbsenceBackward owner selected path registered live included absent with M.hasDelta owner selected path before in observed
    ... | false = refl
    ... | true with Observations.anyWitness (λ key value → M.deltaValue owner selected path value) before observed
    ...   | (key , value) , present , positive = ⊥-elim (Observations.falseNotTrue (trans (sym absent)
        (Observations.anyPresent (λ key value → M.deltaValue owner selected path value) after key value
          (Observations.lookupMember after key value (deltaRetained owner selected path key value registered live included
            (Order.memberLookup before key value (Obs.Support.uniqueBefore support) present) positive)) positive)))

    bindingBackward : ∀ owner selected path version value → M.familyRegistered selection before ≡ true →
      M.checkoutLive selection before selected ≡ true → M.included selection owner path ≡ true →
      M.bindingValue selection after owner selected path version value ≡ true → M.bindingValue selection before owner selected path version value ≡ true
    bindingBackward owner selected path version (O.recordOf storedOwner (O.registration _)) registered live included ()
    bindingBackward owner selected path version (O.recordOf storedOwner (O.checkout _)) registered live included ()
    bindingBackward owner selected path version (O.recordOf storedOwner (O.creationIntent _)) registered live included ()
    bindingBackward owner selected path version (O.recordOf storedOwner (O.defaults _)) registered live included ()
    bindingBackward owner selected path version (O.recordOf storedOwner (O.policyVersion _ _)) registered live included ()
    bindingBackward owner selected path version (O.recordOf storedOwner (O.currentPolicy _)) registered live included ()
    bindingBackward owner selected path version (O.recordOf storedOwner (O.note _)) registered live included ()
    bindingBackward owner selected path version (O.recordOf storedOwner (O.notePosting _ _)) registered live included ()
    bindingBackward owner selected path version (O.recordOf storedOwner (O.noteVector _ _)) registered live included ()
    bindingBackward owner selected path version (O.recordOf storedOwner (O.fileVersion _)) registered live included ()
    bindingBackward owner selected path version (O.recordOf storedOwner (O.basePointer _)) registered live included ()
    bindingBackward owner selected path version (O.recordOf storedOwner (O.chunk _ _)) registered live included ()
    bindingBackward owner selected path version (O.recordOf storedOwner (O.posting _ _)) registered live included ()
    bindingBackward owner selected path version (O.recordOf storedOwner (O.vector _ _)) registered live included ()
    bindingBackward owner selected path version (O.recordOf storedOwner (O.symbol _ _ _)) registered live included ()
    bindingBackward owner selected path version (O.recordOf storedOwner (O.edge _ _ _)) registered live included ()
    bindingBackward owner selected path version (O.recordOf storedOwner (O.structuralSnapshot _ _ _ _)) registered live included ()
    bindingBackward owner selected path version (O.recordOf storedOwner (O.legacy _ _)) registered live included ()
    bindingBackward owner selected path version (O.recordOf storedOwner (O.staging _ _)) registered live included ()
    bindingBackward owner selected path version (O.recordOf storedOwner (O.acceptedWork _ _)) registered live included ()
    bindingBackward owner selected path version (O.recordOf storedOwner (O.cleanupWork _ _ _)) registered live included ()
    bindingBackward owner selected path version (O.recordOf storedOwner (O.activeReader _ _)) registered live included ()
    bindingBackward owner selected path version (O.recordOf storedOwner (O.continuation _ _)) registered live included ()
    bindingBackward owner selected path version (O.recordOf storedOwner (O.receipt (Receipt.entry id (Receipt.active input names work)))) registered live included ()
    bindingBackward owner selected path version (O.recordOf storedOwner (O.receipt (Receipt.entry id (Receipt.finished input names reply)))) registered live included ()
    bindingBackward owner selected path version (O.recordOf storedOwner (O.receipt (Receipt.entry id (Receipt.used)))) registered live included ()
    bindingBackward owner selected path version (O.recordOf storedOwner (O.migration _)) registered live included ()
    bindingBackward owner selected path version (O.recordOf storedOwner (O.usage _)) registered live included ()
    bindingBackward owner selected path version (O.recordOf storedOwner (O.bootstrap _)) registered live included ()
    bindingBackward owner selected path version (O.recordOf storedOwner (O.modelCache _)) registered live included ()
    bindingBackward owner selected path version (O.recordOf storedOwner (O.coordination _)) registered live included ()
    bindingBackward owner selected path version (O.recordOf storedOwner (O.schemaResource _)) registered live included ()
    bindingBackward owner selected path version (O.recordOf storedOwner (O.graphResource _ _ _)) registered live included ()
    bindingBackward owner selected path version (O.recordOf storedOwner (O.logFile _)) registered live included ()
    bindingBackward owner selected path version (O.recordOf storedOwner (O.bootstrapStage _)) registered live included ()
    bindingBackward owner selected path version (O.recordOf storedOwner (O.baseBinding storedVersion storedPath)) registered live included positive
      with parts (E.sameOwner owner storedOwner) (Relation.Nullary.does (path String.≟ storedPath) ∧ (E.sameNat version storedVersion ∧ not (M.hasDelta owner selected path after))) positive
    ... | owners , rest with parts (Relation.Nullary.does (path String.≟ storedPath)) (E.sameNat version storedVersion ∧ not (M.hasDelta owner selected path after)) rest
    ... | paths , last with parts (E.sameNat version storedVersion) (not (M.hasDelta owner selected path after)) last
    ... | versions , absent = Views.andBoth owners (Views.andBoth paths (Views.andBoth versions
      (cong not (deltaAbsenceBackward owner selected path registered live included (Views.notTrueFalse _ absent)))))
    bindingBackward owner selected path version (O.recordOf storedOwner (O.deltaBinding checkout nothing storedPath)) registered live included ()
    bindingBackward owner selected path version (O.recordOf storedOwner (O.deltaBinding checkout (just storedVersion) storedPath)) registered live included positive = positive

    versionBackward : ∀ owner selected path version → M.familyRegistered selection before ≡ true →
      M.versionAtPath selection after owner selected path version ≡ true → M.versionAtPath selection before owner selected path version ≡ true
    versionBackward owner selected path version registered positive with parts (M.checkoutLive selection after selected)
      (M.included selection owner path ∧ E.anyRow (λ key value → M.bindingValue selection after owner selected path version value) after) positive
    ... | live , remaining with parts (M.included selection owner path)
      (E.anyRow (λ key value → M.bindingValue selection after owner selected path version value) after) remaining
    ... | included , bindings with Observations.anyWitness (λ key value → M.bindingValue selection after owner selected path version value) after bindings
    ... | (key , value) , present , selectedBinding = Views.andBoth (checkoutBackward selected live)
      (Views.andBoth included (Observations.anyPresent (λ key value → M.bindingValue selection before owner selected path version value) before key value
        (Observations.lookupMember before key value (Obs.Support.backwardPlain support key value
          (Order.memberLookup after key value (Obs.Support.uniqueAfter support) present)
          (proj₂ (View.View.bindingIdentity selection after owner selected path version value selectedBinding))))
        (bindingBackward owner selected path version value registered (checkoutBackward selected live) included selectedBinding)))

    checkoutVersionBackward : ∀ owner path version key value → M.familyRegistered selection before ≡ true →
      M.checkoutVersionValue selection after owner path version key value ≡ true → M.checkoutVersionValue selection before owner path version key value ≡ true
    checkoutVersionBackward owner path version key (O.recordOf storedOwner (O.registration _)) registered ()
    checkoutVersionBackward owner path version key (O.recordOf storedOwner (O.creationIntent _)) registered ()
    checkoutVersionBackward owner path version key (O.recordOf storedOwner (O.defaults _)) registered ()
    checkoutVersionBackward owner path version key (O.recordOf storedOwner (O.policyVersion _ _)) registered ()
    checkoutVersionBackward owner path version key (O.recordOf storedOwner (O.currentPolicy _)) registered ()
    checkoutVersionBackward owner path version key (O.recordOf storedOwner (O.note _)) registered ()
    checkoutVersionBackward owner path version key (O.recordOf storedOwner (O.notePosting _ _)) registered ()
    checkoutVersionBackward owner path version key (O.recordOf storedOwner (O.noteVector _ _)) registered ()
    checkoutVersionBackward owner path version key (O.recordOf storedOwner (O.fileVersion _)) registered ()
    checkoutVersionBackward owner path version key (O.recordOf storedOwner (O.baseBinding _ _)) registered ()
    checkoutVersionBackward owner path version key (O.recordOf storedOwner (O.deltaBinding _ _ _)) registered ()
    checkoutVersionBackward owner path version key (O.recordOf storedOwner (O.basePointer _)) registered ()
    checkoutVersionBackward owner path version key (O.recordOf storedOwner (O.chunk _ _)) registered ()
    checkoutVersionBackward owner path version key (O.recordOf storedOwner (O.posting _ _)) registered ()
    checkoutVersionBackward owner path version key (O.recordOf storedOwner (O.vector _ _)) registered ()
    checkoutVersionBackward owner path version key (O.recordOf storedOwner (O.symbol _ _ _)) registered ()
    checkoutVersionBackward owner path version key (O.recordOf storedOwner (O.edge _ _ _)) registered ()
    checkoutVersionBackward owner path version key (O.recordOf storedOwner (O.structuralSnapshot _ _ _ _)) registered ()
    checkoutVersionBackward owner path version key (O.recordOf storedOwner (O.legacy _ _)) registered ()
    checkoutVersionBackward owner path version key (O.recordOf storedOwner (O.staging _ _)) registered ()
    checkoutVersionBackward owner path version key (O.recordOf storedOwner (O.acceptedWork _ _)) registered ()
    checkoutVersionBackward owner path version key (O.recordOf storedOwner (O.cleanupWork _ _ _)) registered ()
    checkoutVersionBackward owner path version key (O.recordOf storedOwner (O.activeReader _ _)) registered ()
    checkoutVersionBackward owner path version key (O.recordOf storedOwner (O.continuation _ _)) registered ()
    checkoutVersionBackward owner path version key (O.recordOf storedOwner (O.receipt (Receipt.entry id (Receipt.active input names work)))) registered ()
    checkoutVersionBackward owner path version key (O.recordOf storedOwner (O.receipt (Receipt.entry id (Receipt.finished input names reply)))) registered ()
    checkoutVersionBackward owner path version key (O.recordOf storedOwner (O.receipt (Receipt.entry id (Receipt.used)))) registered ()
    checkoutVersionBackward owner path version key (O.recordOf storedOwner (O.migration _)) registered ()
    checkoutVersionBackward owner path version key (O.recordOf storedOwner (O.usage _)) registered ()
    checkoutVersionBackward owner path version key (O.recordOf storedOwner (O.bootstrap _)) registered ()
    checkoutVersionBackward owner path version key (O.recordOf storedOwner (O.modelCache _)) registered ()
    checkoutVersionBackward owner path version key (O.recordOf storedOwner (O.coordination _)) registered ()
    checkoutVersionBackward owner path version key (O.recordOf storedOwner (O.schemaResource _)) registered ()
    checkoutVersionBackward owner path version key (O.recordOf storedOwner (O.graphResource _ _ _)) registered ()
    checkoutVersionBackward owner path version key (O.recordOf storedOwner (O.logFile _)) registered ()
    checkoutVersionBackward owner path version key (O.recordOf storedOwner (O.bootstrapStage _)) registered ()
    checkoutVersionBackward owner path version key (O.recordOf storedOwner (O.checkout info)) registered positive
      with parts (E.sameOwner owner storedOwner) (M.versionAtPath selection after owner key path version) positive
    ... | owners , visible = Views.andBoth owners (versionBackward owner key path version registered visible)

    publishedBackward : ∀ owner path version → M.familyRegistered selection before ≡ true →
      M.versionPublishedAtPath selection after owner path version ≡ true → M.versionPublishedAtPath selection before owner path version ≡ true
    publishedBackward owner path version registered positive with Observations.anyWitness (M.checkoutVersionValue selection after owner path version) after positive
    ... | (key , value) , present , selected = Observations.anyPresent (M.checkoutVersionValue selection before owner path version) before key value
      (Observations.lookupMember before key value (Obs.Support.backwardPlain support key value
        (Order.memberLookup after key value (Obs.Support.uniqueAfter support) present) nonSnapshot))
      (checkoutVersionBackward owner path version key value registered selected)
      where
      nonSnapshot : O.kind (O.body value) ≢ O.structuralSnapshotK
      nonSnapshot with Observations.snapshotView value
      ... | Observations.plain proof = proof
      ... | Observations.snapshot owner checkout nodes edges payload = ⊥-elim (Observations.falseNotTrue selected)

    symbolObservationBackward : ∀ owner selected value → M.familyRegistered selection before ≡ true →
      M.symbolObservation selection after owner selected (just value) ≡ true → M.symbolObservation selection before owner selected (just value) ≡ true
    symbolObservationBackward owner selected (O.recordOf storedOwner (O.registration _)) registered ()
    symbolObservationBackward owner selected (O.recordOf storedOwner (O.checkout _)) registered ()
    symbolObservationBackward owner selected (O.recordOf storedOwner (O.creationIntent _)) registered ()
    symbolObservationBackward owner selected (O.recordOf storedOwner (O.defaults _)) registered ()
    symbolObservationBackward owner selected (O.recordOf storedOwner (O.policyVersion _ _)) registered ()
    symbolObservationBackward owner selected (O.recordOf storedOwner (O.currentPolicy _)) registered ()
    symbolObservationBackward owner selected (O.recordOf storedOwner (O.note _)) registered ()
    symbolObservationBackward owner selected (O.recordOf storedOwner (O.notePosting _ _)) registered ()
    symbolObservationBackward owner selected (O.recordOf storedOwner (O.noteVector _ _)) registered ()
    symbolObservationBackward owner selected (O.recordOf storedOwner (O.fileVersion _)) registered ()
    symbolObservationBackward owner selected (O.recordOf storedOwner (O.baseBinding _ _)) registered ()
    symbolObservationBackward owner selected (O.recordOf storedOwner (O.deltaBinding _ _ _)) registered ()
    symbolObservationBackward owner selected (O.recordOf storedOwner (O.basePointer _)) registered ()
    symbolObservationBackward owner selected (O.recordOf storedOwner (O.chunk _ _)) registered ()
    symbolObservationBackward owner selected (O.recordOf storedOwner (O.posting _ _)) registered ()
    symbolObservationBackward owner selected (O.recordOf storedOwner (O.vector _ _)) registered ()
    symbolObservationBackward owner selected (O.recordOf storedOwner (O.edge _ _ _)) registered ()
    symbolObservationBackward owner selected (O.recordOf storedOwner (O.structuralSnapshot _ _ _ _)) registered ()
    symbolObservationBackward owner selected (O.recordOf storedOwner (O.legacy _ _)) registered ()
    symbolObservationBackward owner selected (O.recordOf storedOwner (O.staging _ _)) registered ()
    symbolObservationBackward owner selected (O.recordOf storedOwner (O.acceptedWork _ _)) registered ()
    symbolObservationBackward owner selected (O.recordOf storedOwner (O.cleanupWork _ _ _)) registered ()
    symbolObservationBackward owner selected (O.recordOf storedOwner (O.activeReader _ _)) registered ()
    symbolObservationBackward owner selected (O.recordOf storedOwner (O.continuation _ _)) registered ()
    symbolObservationBackward owner selected (O.recordOf storedOwner (O.receipt (Receipt.entry id (Receipt.active input names work)))) registered ()
    symbolObservationBackward owner selected (O.recordOf storedOwner (O.receipt (Receipt.entry id (Receipt.finished input names reply)))) registered ()
    symbolObservationBackward owner selected (O.recordOf storedOwner (O.receipt (Receipt.entry id (Receipt.used)))) registered ()
    symbolObservationBackward owner selected (O.recordOf storedOwner (O.migration _)) registered ()
    symbolObservationBackward owner selected (O.recordOf storedOwner (O.usage _)) registered ()
    symbolObservationBackward owner selected (O.recordOf storedOwner (O.bootstrap _)) registered ()
    symbolObservationBackward owner selected (O.recordOf storedOwner (O.modelCache _)) registered ()
    symbolObservationBackward owner selected (O.recordOf storedOwner (O.coordination _)) registered ()
    symbolObservationBackward owner selected (O.recordOf storedOwner (O.schemaResource _)) registered ()
    symbolObservationBackward owner selected (O.recordOf storedOwner (O.graphResource _ _ _)) registered ()
    symbolObservationBackward owner selected (O.recordOf storedOwner (O.logFile _)) registered ()
    symbolObservationBackward owner selected (O.recordOf storedOwner (O.bootstrapStage _)) registered ()
    symbolObservationBackward owner selected (O.recordOf storedOwner (O.symbol version path payload)) registered positive
      with parts (E.sameOwner owner storedOwner) (M.versionAtPath selection after owner selected path version) positive
    ... | owners , visible = Views.andBoth owners (versionBackward owner selected path version registered visible)

    symbolBackward : ∀ owner selected key → M.familyRegistered selection before ≡ true →
      M.symbolVisible selection after owner selected key ≡ true → M.symbolVisible selection before owner selected key ≡ true
    symbolBackward owner selected key registered positive with DB.lookup key after in found
    ... | nothing with positive
    ...   | ()
    symbolBackward owner selected key registered positive | just value with Observations.snapshotView value
    ... | Observations.plain nonSnapshot = trans
      (cong (M.symbolObservation selection before owner selected) (Obs.Support.backwardPlain support key value found nonSnapshot))
      (symbolObservationBackward owner selected value registered positive)
    ... | Observations.snapshot storedOwner checkout nodes edges payload with positive
    ...   | ()

    edgeObservationBackward : ∀ owner selected value → M.familyRegistered selection before ≡ true →
      M.edgeObservation selection after owner selected (just value) ≡ true → M.edgeObservation selection before owner selected (just value) ≡ true
    edgeObservationBackward owner selected (O.recordOf storedOwner (O.registration _)) registered ()
    edgeObservationBackward owner selected (O.recordOf storedOwner (O.checkout _)) registered ()
    edgeObservationBackward owner selected (O.recordOf storedOwner (O.creationIntent _)) registered ()
    edgeObservationBackward owner selected (O.recordOf storedOwner (O.defaults _)) registered ()
    edgeObservationBackward owner selected (O.recordOf storedOwner (O.policyVersion _ _)) registered ()
    edgeObservationBackward owner selected (O.recordOf storedOwner (O.currentPolicy _)) registered ()
    edgeObservationBackward owner selected (O.recordOf storedOwner (O.note _)) registered ()
    edgeObservationBackward owner selected (O.recordOf storedOwner (O.notePosting _ _)) registered ()
    edgeObservationBackward owner selected (O.recordOf storedOwner (O.noteVector _ _)) registered ()
    edgeObservationBackward owner selected (O.recordOf storedOwner (O.fileVersion _)) registered ()
    edgeObservationBackward owner selected (O.recordOf storedOwner (O.baseBinding _ _)) registered ()
    edgeObservationBackward owner selected (O.recordOf storedOwner (O.deltaBinding _ _ _)) registered ()
    edgeObservationBackward owner selected (O.recordOf storedOwner (O.basePointer _)) registered ()
    edgeObservationBackward owner selected (O.recordOf storedOwner (O.chunk _ _)) registered ()
    edgeObservationBackward owner selected (O.recordOf storedOwner (O.posting _ _)) registered ()
    edgeObservationBackward owner selected (O.recordOf storedOwner (O.vector _ _)) registered ()
    edgeObservationBackward owner selected (O.recordOf storedOwner (O.symbol _ _ _)) registered ()
    edgeObservationBackward owner selected (O.recordOf storedOwner (O.structuralSnapshot _ _ _ _)) registered ()
    edgeObservationBackward owner selected (O.recordOf storedOwner (O.legacy _ _)) registered ()
    edgeObservationBackward owner selected (O.recordOf storedOwner (O.staging _ _)) registered ()
    edgeObservationBackward owner selected (O.recordOf storedOwner (O.acceptedWork _ _)) registered ()
    edgeObservationBackward owner selected (O.recordOf storedOwner (O.cleanupWork _ _ _)) registered ()
    edgeObservationBackward owner selected (O.recordOf storedOwner (O.activeReader _ _)) registered ()
    edgeObservationBackward owner selected (O.recordOf storedOwner (O.continuation _ _)) registered ()
    edgeObservationBackward owner selected (O.recordOf storedOwner (O.receipt (Receipt.entry id (Receipt.active input names work)))) registered ()
    edgeObservationBackward owner selected (O.recordOf storedOwner (O.receipt (Receipt.entry id (Receipt.finished input names reply)))) registered ()
    edgeObservationBackward owner selected (O.recordOf storedOwner (O.receipt (Receipt.entry id (Receipt.used)))) registered ()
    edgeObservationBackward owner selected (O.recordOf storedOwner (O.migration _)) registered ()
    edgeObservationBackward owner selected (O.recordOf storedOwner (O.usage _)) registered ()
    edgeObservationBackward owner selected (O.recordOf storedOwner (O.bootstrap _)) registered ()
    edgeObservationBackward owner selected (O.recordOf storedOwner (O.modelCache _)) registered ()
    edgeObservationBackward owner selected (O.recordOf storedOwner (O.coordination _)) registered ()
    edgeObservationBackward owner selected (O.recordOf storedOwner (O.schemaResource _)) registered ()
    edgeObservationBackward owner selected (O.recordOf storedOwner (O.graphResource _ _ _)) registered ()
    edgeObservationBackward owner selected (O.recordOf storedOwner (O.logFile _)) registered ()
    edgeObservationBackward owner selected (O.recordOf storedOwner (O.bootstrapStage _)) registered ()
    edgeObservationBackward owner selected (O.recordOf storedOwner (O.edge source target payload)) registered positive
      with parts (E.sameOwner owner storedOwner) (M.symbolVisible selection after owner selected source ∧ M.symbolVisible selection after owner selected target) positive
    ... | owners , rest with parts (M.symbolVisible selection after owner selected source) (M.symbolVisible selection after owner selected target) rest
    ... | sourceVisible , targetVisible = Views.andBoth owners (Views.andBoth
      (symbolBackward owner selected source registered sourceVisible) (symbolBackward owner selected target registered targetVisible))

    edgeBackward : ∀ owner selected key → M.familyRegistered selection before ≡ true →
      M.edgeVisible selection after owner selected key ≡ true → M.edgeVisible selection before owner selected key ≡ true
    edgeBackward owner selected key registered positive with DB.lookup key after in found
    ... | nothing with positive
    ...   | ()
    edgeBackward owner selected key registered positive | just value with Observations.snapshotView value
    ... | Observations.plain nonSnapshot = trans
      (cong (M.edgeObservation selection before owner selected) (Obs.Support.backwardPlain support key value found nonSnapshot))
      (edgeObservationBackward owner selected value registered positive)
    ... | Observations.snapshot storedOwner checkout nodes edges payload with positive
    ...   | ()
