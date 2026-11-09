{-# OPTIONS --safe #-}
module Muninn.CleanupObservations where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.ExclusionClassifier as C
import Muninn.CleanupEffects as Effects
import Muninn.CleanupStorage as Storage
import Muninn.CleanupOrder as Order
import Muninn.ReceiptTypes as Receipt
open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_)
open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
module DB = O.DB

lookupMember : ∀ world key value → DB.lookup key world ≡ just value → (key , value) ∈ world
lookupMember [] key value ()
lookupMember ((other , stored) ∷ rest) key value found with key ≟ other
... | yes refl with just-injective found
...   | refl = here refl
lookupMember ((other , stored) ∷ rest) key value found | no _ = there (lookupMember rest key value found)

anyWitness : ∀ test world → E.anyRow test world ≡ true → Σ (ℕ × O.Record) (λ row → row ∈ world × test (proj₁ row) (proj₂ row) ≡ true)
anyWitness test [] ()
anyWitness test ((key , value) ∷ rest) proof with test key value in selected
... | true = (key , value) , here refl , selected
... | false with anyWitness test rest proof
...   | row , present , selected = row , there present , selected

anyPresent : ∀ test world key value → (key , value) ∈ world → test key value ≡ true → E.anyRow test world ≡ true
anyPresent test ((key , value) ∷ rest) .key .value (here refl) selected rewrite selected = refl
anyPresent test ((other , stored) ∷ rest) key value (there present) selected with test other stored
... | true = refl
... | false = anyPresent test rest key value present selected

falseNotTrue : false ≢ true
falseNotTrue ()

data SnapshotView : O.Record → Set where
  snapshot : ∀ owner selected nodes edges payload → SnapshotView (O.recordOf owner (O.structuralSnapshot selected nodes edges payload))
  plain : ∀ {value} → O.kind (O.body value) ≢ O.structuralSnapshotK → SnapshotView value

snapshotView : ∀ value → SnapshotView value

snapshotView (O.recordOf owner (O.registration _)) = plain (λ ())
snapshotView (O.recordOf owner (O.checkout _)) = plain (λ ())
snapshotView (O.recordOf owner (O.creationIntent _)) = plain (λ ())
snapshotView (O.recordOf owner (O.defaults _)) = plain (λ ())
snapshotView (O.recordOf owner (O.policyVersion _ _)) = plain (λ ())
snapshotView (O.recordOf owner (O.currentPolicy _)) = plain (λ ())
snapshotView (O.recordOf owner (O.note _)) = plain (λ ())
snapshotView (O.recordOf owner (O.notePosting _ _)) = plain (λ ())
snapshotView (O.recordOf owner (O.noteVector _ _)) = plain (λ ())
snapshotView (O.recordOf owner (O.fileVersion _)) = plain (λ ())
snapshotView (O.recordOf owner (O.baseBinding _ _)) = plain (λ ())
snapshotView (O.recordOf owner (O.deltaBinding _ _ _)) = plain (λ ())
snapshotView (O.recordOf owner (O.basePointer _)) = plain (λ ())
snapshotView (O.recordOf owner (O.chunk _ _)) = plain (λ ())
snapshotView (O.recordOf owner (O.posting _ _)) = plain (λ ())
snapshotView (O.recordOf owner (O.vector _ _)) = plain (λ ())
snapshotView (O.recordOf owner (O.symbol _ _ _)) = plain (λ ())
snapshotView (O.recordOf owner (O.edge _ _ _)) = plain (λ ())
snapshotView (O.recordOf owner (O.structuralSnapshot selected nodes edges payload)) = snapshot owner selected nodes edges payload
snapshotView (O.recordOf owner (O.legacy _ _)) = plain (λ ())
snapshotView (O.recordOf owner (O.staging _ _)) = plain (λ ())
snapshotView (O.recordOf owner (O.acceptedWork _ _)) = plain (λ ())
snapshotView (O.recordOf owner (O.cleanupWork _ _ _)) = plain (λ ())
snapshotView (O.recordOf owner (O.activeReader _ _)) = plain (λ ())
snapshotView (O.recordOf owner (O.continuation _ _)) = plain (λ ())
snapshotView (O.recordOf owner (O.receipt _)) = plain (λ ())
snapshotView (O.recordOf owner (O.migration _)) = plain (λ ())
snapshotView (O.recordOf owner (O.usage _)) = plain (λ ())
snapshotView (O.recordOf owner (O.bootstrap _)) = plain (λ ())
snapshotView (O.recordOf owner (O.modelCache _)) = plain (λ ())
snapshotView (O.recordOf owner (O.coordination _)) = plain (λ ())
snapshotView (O.recordOf owner (O.schemaResource _)) = plain (λ ())
snapshotView (O.recordOf owner (O.graphResource _ _ _)) = plain (λ ())
snapshotView (O.recordOf owner (O.logFile _)) = plain (λ ())
snapshotView (O.recordOf owner (O.bootstrapStage _)) = plain (λ ())

module Model (excluded : List String → String → Bool) where
  module M = E.Model excluded
  module Store = Storage.Model excluded

  indexedIgnoresControls : ∀ selection value → E.indexed value ≡ true →
    (M.registeredValue selection value ≡ false) × ((M.legacyValue selection value ≡ false) × (M.liveValue selection value ≡ false))

  indexedIgnoresControls selection (O.recordOf owner (O.registration _)) ()
  indexedIgnoresControls selection (O.recordOf owner (O.checkout _)) ()
  indexedIgnoresControls selection (O.recordOf owner (O.creationIntent _)) ()
  indexedIgnoresControls selection (O.recordOf owner (O.defaults _)) ()
  indexedIgnoresControls selection (O.recordOf owner (O.policyVersion _ _)) ()
  indexedIgnoresControls selection (O.recordOf owner (O.currentPolicy _)) ()
  indexedIgnoresControls selection (O.recordOf owner (O.note _)) ()
  indexedIgnoresControls selection (O.recordOf owner (O.notePosting _ _)) ()
  indexedIgnoresControls selection (O.recordOf owner (O.noteVector _ _)) ()
  indexedIgnoresControls selection (O.recordOf owner (O.fileVersion _)) indexed = refl , refl , refl
  indexedIgnoresControls selection (O.recordOf owner (O.baseBinding _ _)) indexed = refl , refl , refl
  indexedIgnoresControls selection (O.recordOf owner (O.deltaBinding _ _ _)) indexed = refl , refl , refl
  indexedIgnoresControls selection (O.recordOf owner (O.basePointer _)) indexed = refl , refl , refl
  indexedIgnoresControls selection (O.recordOf owner (O.chunk _ _)) indexed = refl , refl , refl
  indexedIgnoresControls selection (O.recordOf owner (O.posting _ _)) indexed = refl , refl , refl
  indexedIgnoresControls selection (O.recordOf owner (O.vector _ _)) indexed = refl , refl , refl
  indexedIgnoresControls selection (O.recordOf owner (O.symbol _ _ _)) indexed = refl , refl , refl
  indexedIgnoresControls selection (O.recordOf owner (O.edge _ _ _)) indexed = refl , refl , refl
  indexedIgnoresControls selection (O.recordOf owner (O.structuralSnapshot _ _ _ _)) indexed = refl , refl , refl
  indexedIgnoresControls selection (O.recordOf owner (O.legacy _ _)) indexed = refl , refl , refl
  indexedIgnoresControls selection (O.recordOf owner (O.staging _ _)) indexed = refl , refl , refl
  indexedIgnoresControls selection (O.recordOf owner (O.acceptedWork _ _)) ()
  indexedIgnoresControls selection (O.recordOf owner (O.cleanupWork _ _ _)) ()
  indexedIgnoresControls selection (O.recordOf owner (O.activeReader _ _)) ()
  indexedIgnoresControls selection (O.recordOf owner (O.continuation _ _)) ()
  indexedIgnoresControls selection (O.recordOf owner (O.receipt (Receipt.entry id (Receipt.active input names work)))) ()
  indexedIgnoresControls selection (O.recordOf owner (O.receipt (Receipt.entry id (Receipt.finished input names reply)))) ()
  indexedIgnoresControls selection (O.recordOf owner (O.receipt (Receipt.entry id (Receipt.used)))) ()
  indexedIgnoresControls selection (O.recordOf owner (O.migration _)) ()
  indexedIgnoresControls selection (O.recordOf owner (O.usage _)) ()
  indexedIgnoresControls selection (O.recordOf owner (O.bootstrap _)) ()
  indexedIgnoresControls selection (O.recordOf owner (O.modelCache _)) ()
  indexedIgnoresControls selection (O.recordOf owner (O.coordination _)) ()
  indexedIgnoresControls selection (O.recordOf owner (O.schemaResource _)) ()
  indexedIgnoresControls selection (O.recordOf owner (O.graphResource _ _ _)) indexed = refl , refl , refl
  indexedIgnoresControls selection (O.recordOf owner (O.logFile _)) ()
  indexedIgnoresControls selection (O.recordOf owner (O.bootstrapStage _)) ()

  projectionPlain : ∀ selection world value → O.kind (O.body value) ≢ O.structuralSnapshotK → M.project selection world value ≡ value
  projectionPlain selection world value nonSnapshot with Store.shape selection world value
  ... | Store.plain exact = exact
  ... | Store.snapshot owner selected nodes edges payload = ⊥-elim (nonSnapshot refl)

  neededSame : ∀ selection before after key value → M.Safety selection before after →
    DB.lookup key before ≡ just value → M.Needed selection before key → O.kind (O.body value) ≢ O.structuralSnapshotK →
    DB.lookup key after ≡ just value
  neededSame selection before after key value safe found needed nonSnapshot with M.Safety.needed safe key value found needed
  ... | retained , present , projected , nodes , edges = trans present (cong just
      (trans (sym (projectionPlain selection before retained retainedNonSnapshot))
        (trans projected (projectionPlain selection before value nonSnapshot))))
    where
    sameKind : O.kind (O.body retained) ≡ O.kind (O.body value)
    sameKind = trans (sym (Store.projectKind selection before retained))
      (trans (cong (λ v → O.kind (O.body v)) projected) (Store.projectKind selection before value))
    retainedNonSnapshot : O.kind (O.body retained) ≢ O.structuralSnapshotK
    retainedNonSnapshot equal = nonSnapshot (trans (sym sameKind) equal)

  record Support (selection : E.Rule) (before after : O.World) : Set where
    field safe : M.Safety selection before after
          uniqueBefore : O.Unique before
          uniqueAfter : O.Unique after
          backwardPlain : ∀ key value → DB.lookup key after ≡ just value → O.kind (O.body value) ≢ O.structuralSnapshotK → DB.lookup key before ≡ just value

  metadataIndex : ∀ (test : O.Record → Bool) value → (E.indexed value ≡ true → test value ≡ false) → test value ≡ true → E.indexed value ≡ false
  metadataIndex test value ignored positive with E.indexed value in indexed
  ... | false = refl
  ... | true = ⊥-elim (falseNotTrue (trans (sym (ignored refl)) positive))

  anyMetadataPositive : ∀ selection before after (test : O.Record → Bool) → Support selection before after →
    (∀ value → E.indexed value ≡ true → test value ≡ false) →
    E.anyRow (λ key value → test value) before ≡ true → E.anyRow (λ key value → test value) after ≡ true
  anyMetadataPositive selection before after test support ignored positive with anyWitness (λ key value → test value) before positive
  ... | (key , value) , present , selected = anyPresent (λ key value → test value) after key value
      (lookupMember after key value (M.Safety.metadata (Support.safe support) key value
        (Order.memberLookup before key value (Support.uniqueBefore support) present) (metadataIndex test value (ignored value) selected))) selected

  registrationPositive : ∀ selection before after → Support selection before after → M.familyRegistered selection before ≡ true → M.familyRegistered selection after ≡ true
  registrationPositive selection before after support = anyMetadataPositive selection before after (M.registeredValue selection) support
    (λ value indexed → proj₁ (indexedIgnoresControls selection value indexed))

  legacyPositive : ∀ selection before after → Support selection before after → M.legacyReadable selection before ≡ true → M.legacyReadable selection after ≡ true
  legacyPositive selection before after support = anyMetadataPositive selection before after (M.legacyValue selection) support
    (λ value indexed → proj₁ (proj₂ (indexedIgnoresControls selection value indexed)))

  anyCheckoutPositive : ∀ selection before after → Support selection before after → M.anyCheckoutLive selection before ≡ true → M.anyCheckoutLive selection after ≡ true
  anyCheckoutPositive selection before after support = anyMetadataPositive selection before after (M.liveValue selection) support
    (λ value indexed → proj₂ (proj₂ (indexedIgnoresControls selection value indexed)))

  checkoutPositive : ∀ selection before after key → Support selection before after → M.checkoutLive selection before key ≡ true → M.checkoutLive selection after key ≡ true
  checkoutPositive selection before after key support positive with DB.lookup key before in found
  ... | nothing with positive
  ...   | ()
  checkoutPositive selection before after key support positive | just value = trans
    (cong (M.checkoutObservation selection) (M.Safety.metadata (Support.safe support) key value found
      (metadataIndex (M.liveValue selection) value (λ indexed → proj₂ (proj₂ (indexedIgnoresControls selection value indexed))) positive))) positive

  checkoutImpliesAny : ∀ selection world key → M.checkoutLive selection world key ≡ true → M.anyCheckoutLive selection world ≡ true
  checkoutImpliesAny selection world key positive with DB.lookup key world in found
  ... | nothing with positive
  ...   | ()
  checkoutImpliesAny selection world key positive | just value = anyPresent (λ key value → M.liveValue selection value) world key value (lookupMember world key value found) positive

  falseObservation : ∀ selection before after test → Support selection before after →
    (∀ key owner selected nodes edges payload → test key (O.recordOf owner (O.structuralSnapshot selected nodes edges payload)) ≡ false) →
    E.anyRow test before ≡ false → E.anyRow test after ≡ false
  falseObservation selection before after test support ignore negative with E.anyRow test after in result
  ... | false = refl
  ... | true with anyWitness test after result
  ...   | (key , value) , present , positive with snapshotView value
  ...     | snapshot owner selected nodes edges payload = ⊥-elim (falseNotTrue (trans (sym (ignore key owner selected nodes edges payload)) positive))
  ...     | plain nonSnapshot = ⊥-elim (Effects.trueIsNotFalse (trans (sym
        (anyPresent test before key value (lookupMember before key value
          (Support.backwardPlain support key value (Order.memberLookup after key value (Support.uniqueAfter support) present) nonSnapshot)) positive)) negative))

  deltaAbsence : ∀ selection before after owner selected path → Support selection before after →
    M.hasDelta owner selected path before ≡ false → M.hasDelta owner selected path after ≡ false
  deltaAbsence selection before after owner selected path support = falseObservation selection before after
    (λ key value → M.deltaValue owner selected path value) support (λ key o s ns es payload → refl)

  module Step (selection : E.Rule) (accepted : O.World) (intent : M.Intent selection accepted) where
    module Core = Effects.Model.Core excluded selection accepted intent

    changedSnapshot : ∀ world value → Core.Changed world value → O.kind (O.body value) ≡ O.structuralSnapshotK
    changedSnapshot world value changed with Store.shape selection world value
    ... | Store.plain exact = ⊥-elim (Core.changedIsActual world value changed exact)
    ... | Store.snapshot owner selected nodes edges payload = refl

    backwardPlan : ∀ key world (plan : Core.Plan key world) other value →
      DB.lookup other (proj₂ (DB.execute (Core.compile key world plan) world)) ≡ just value →
      O.kind (O.body value) ≢ O.structuralSnapshotK → DB.lookup other world ≡ just value
    backwardPlan key world (Core.retain denied) other value found nonSnapshot = found
    backwardPlan key world (Core.erase ready) other value found nonSnapshot with key ≟ other
    ... | yes refl with trans (sym (DB.deleteAbsent key world)) found
    ...   | ()
    backwardPlan key world (Core.erase ready) other value found nonSnapshot | no distinct = trans (sym (DB.deletePreservesOther key other world distinct)) found
    backwardPlan key world (Core.trim (stored , present , captured , owned , indexed , needed , unprotected , changed)) other value found nonSnapshot with key ≟ other
    ... | no distinct = trans (sym (DB.writePreservesOther key other (M.project selection world stored) world distinct)) found
    ... | yes refl = ⊥-elim (nonSnapshot (trans (sym (cong (λ v → O.kind (O.body v)) sameValue))
        (trans (Store.projectKind selection world stored) (changedSnapshot world stored changed))))
      where
      sameValue : M.project selection world stored ≡ value
      sameValue = just-injective (trans (sym (DB.writeVisible key (M.project selection world stored) world)) found)

    stepSupport : ∀ key world → O.Admissible world → Support selection world (proj₂ (DB.execute (Core.transaction key) world))
    stepSupport key world valid = record
      { safe = Core.transactionSafety key world
      ; uniqueBefore = O.Admissible.unique valid
      ; uniqueAfter = O.Admissible.unique (Core.transactionAdmissible key world valid)
      ; backwardPlain = backwardPlan key world (Core.decide key world) }
