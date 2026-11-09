{-# OPTIONS --safe #-}
-- Retirement disables new serving roots; reclamation uses the existing worker.
module Muninn.RetirementCleanup where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.CleanupOrder as Order
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (just; nothing)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; cong)
module DB = O.DB
module M = E.Model

-- This is request availability, distinct from projecting retained data for an
-- already-running reader. Pausing/Git suspension retain a view; retirement
-- removes availability and its permanent roots.
available : E.Rule → O.World → ℕ → Bool
available selection world checkout = M.familyRegistered selection world ∧ M.checkoutLive selection world checkout

retiredFamilyUnavailable : ∀ selection world checkout → M.familyRegistered selection world ≡ false → available selection world checkout ≡ false
retiredFamilyUnavailable selection world checkout retired rewrite retired = refl

retiredCheckoutUnavailable : ∀ selection world checkout → M.checkoutLive selection world checkout ≡ false → available selection world checkout ≡ false
retiredCheckoutUnavailable selection world checkout retired rewrite retired with M.familyRegistered selection world
... | true = refl
... | false = refl

checkoutUnavailable : ∀ selection world checkout info →
  DB.lookup checkout world ≡ just (O.recordOf (E.targetOwner selection) (O.checkout info)) →
  O.CheckoutInfo.retired info ≡ true → M.checkoutLive selection world checkout ≡ false
checkoutUnavailable selection world checkout info found retired rewrite found | retired
  with E.sameOwner (E.targetOwner selection) (E.targetOwner selection)
... | true = refl
... | false = refl

allFalse : ∀ test world → All.All (λ row → test (Data.Product.proj₁ row) (Data.Product.proj₂ row) ≡ false) world → E.anyRow test world ≡ false
allFalse test [] All.[] = refl
allFalse test ((key , value) ∷ rows) (proof All.∷ rest) rewrite proof | allFalse test rows rest = refl

-- A registry has one family record. This helper turns actual lookup evidence
-- into the family availability fact used by query admission and cleanup roots.
allRegistrationsRetired : ∀ selection world → O.Unique world →
  (∀ key info → DB.lookup key world ≡ just (O.recordOf (E.targetOwner selection) (O.registration info)) → O.RegistrationInfo.retired info ≡ true) →
  M.familyRegistered selection world ≡ false
allRegistrationsRetired selection world unique retired = allFalse _ world (All.tabulate rowFalse)
  where
  rowFalse : ∀ {row} → row ∈ world → M.registeredValue selection (Data.Product.proj₂ row) ≡ false
  rowFalse {key , O.recordOf owner (O.registration info)} present with E.ownerEqual owner (E.targetOwner selection)
  ... | yes refl rewrite retired key info (Order.memberLookup world key _ unique present) = refl
  ... | no other = refl
  rowFalse {key , O.recordOf owner (O.checkout info)} present = refl
  rowFalse {key , O.recordOf owner (O.creationIntent x)} present = refl
  rowFalse {key , O.recordOf owner (O.defaults x)} present = refl
  rowFalse {key , O.recordOf owner (O.policyVersion x x₁)} present = refl
  rowFalse {key , O.recordOf owner (O.currentPolicy x)} present = refl
  rowFalse {key , O.recordOf owner (O.note x)} present = refl
  rowFalse {key , O.recordOf owner (O.notePosting x x₁)} present = refl
  rowFalse {key , O.recordOf owner (O.noteVector x x₁)} present = refl
  rowFalse {key , O.recordOf owner (O.fileVersion x)} present = refl
  rowFalse {key , O.recordOf owner (O.baseBinding version path x)} present = refl
  rowFalse {key , O.recordOf owner (O.deltaBinding selected version path x)} present = refl
  rowFalse {key , O.recordOf owner (O.basePointer x)} present = refl
  rowFalse {key , O.recordOf owner (O.chunk x x₁)} present = refl
  rowFalse {key , O.recordOf owner (O.posting x x₁)} present = refl
  rowFalse {key , O.recordOf owner (O.vector x x₁)} present = refl
  rowFalse {key , O.recordOf owner (O.symbol x x₁ x₂)} present = refl
  rowFalse {key , O.recordOf owner (O.edge x x₁ x₂)} present = refl
  rowFalse {key , O.recordOf owner (O.publishedView x x₁)} present = refl
  rowFalse {key , O.recordOf owner (O.structuralSnapshot x x₁ x₂ x₃)} present = refl
  rowFalse {key , O.recordOf owner (O.legacy path x x₁)} present = refl
  rowFalse {key , O.recordOf owner (O.staging x x₁)} present = refl
  rowFalse {key , O.recordOf owner (O.acceptedWork x x₁)} present = refl
  rowFalse {key , O.recordOf owner (O.cleanupWork x x₁ x₂)} present = refl
  rowFalse {key , O.recordOf owner (O.activeReader x x₁)} present = refl
  rowFalse {key , O.recordOf owner (O.continuation x x₁)} present = refl
  rowFalse {key , O.recordOf owner (O.receipt x)} present = refl
  rowFalse {key , O.recordOf owner (O.graphResource x x₁ x₂)} present = refl
  rowFalse {key , O.recordOf owner (O.migration x)} present = refl
  rowFalse {key , O.recordOf owner (O.usage x)} present = refl
  rowFalse {key , O.recordOf owner (O.bootstrap x)} present = refl
  rowFalse {key , O.recordOf owner (O.modelCache x)} present = refl
  rowFalse {key , O.recordOf owner (O.coordination x)} present = refl
  rowFalse {key , O.recordOf owner (O.schemaResource x)} present = refl
  rowFalse {key , O.recordOf owner (O.logFile x)} present = refl
  rowFalse {key , O.recordOf owner (O.bootstrapStage x)} present = refl

-- No age/TTL input is added here. Completed cleanup must remove each captured
-- unused derived record; still-needed data, readers and metadata are protected
-- by the SAME complete-world contract used for exclusions.
module Cleanup (selection : E.Rule) (accepted : O.World) (intent : M.Intent selection accepted) where
  removesUnused : ∀ before after key value → M.Complete selection accepted intent before after →
    key ∈ M.Intent.keys intent → DB.lookup key before ≡ just value → O.owner value ≡ E.targetOwner selection →
    E.indexed value ≡ true → ¬ M.Needed selection before key → DB.lookup key after ≡ nothing
  removesUnused = M.completeRemovesUnneeded selection accepted intent

  preservesShared : ∀ before after key value → M.Complete selection accepted intent before after →
    key ∈ M.Intent.keys intent → DB.lookup key before ≡ just value → M.Needed selection before key →
    DB.lookup key after ≡ just (M.project selection before value)
  preservesShared = M.completePreservesNeeded selection accepted intent

  preservesReader : ∀ before after key value → M.Complete selection accepted intent before after →
    DB.lookup key before ≡ just value → M.Protected selection before key → DB.lookup key after ≡ just value
  preservesReader before after key value completed = M.Safety.protected (M.Complete.safety completed) key value

  preservesOtherFamily : ∀ before after key value → M.Complete selection accepted intent before after →
    DB.lookup key before ≡ just value → O.owner value ≢ E.targetOwner selection → DB.lookup key after ≡ just value
  preservesOtherFamily = M.completePreservesUnrelated selection accepted intent

  preservesNotesAndSettings : ∀ before after key value → M.Complete selection accepted intent before after →
    DB.lookup key before ≡ just value → E.indexed value ≡ false → DB.lookup key after ≡ just value
  preservesNotesAndSettings = M.completePreservesMetadata selection accepted intent

