{-# OPTIONS --safe #-}
-- Canonical snapshot filtering survives publication bookkeeping writes.
module Muninn.PublicationVisibility where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.CleanupStorage as Storage
import Muninn.CleanupObservations as Observations
import Muninn.CleanupOrder as Order
import Muninn.CleanupEffects as Effects
import Muninn.CleanupAdmissionStorage as Allocation
open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
module DB = O.DB

boolSame : ∀ first second → (first ≡ true → second ≡ true) → (second ≡ true → first ≡ true) → first ≡ second
boolSame true second forward backward = sym (forward refl)
boolSame false false forward backward = refl
boolSame false true forward backward with backward refl
... | ()

observedWrite : ∀ {A : Set} (observe : Maybe O.Record → A) world key old new →
  DB.lookup key world ≡ just old → observe (just old) ≡ observe (just new) →
  ∀ target → observe (DB.lookup target world) ≡ observe (DB.lookup target (DB.write key new world))
observedWrite observe world key old new found same target with key ≟ target
... | yes refl = trans (cong observe found) (trans same (sym (cong observe (DB.writeVisible key new world))))
... | no different = sym (cong observe (DB.writePreservesOther key target new world different))

anyCong : ∀ first second world → (∀ key value → first key value ≡ second key value) →
  E.anyRow first world ≡ E.anyRow second world
anyCong first second [] same = refl
anyCong first second ((key , value) ∷ rows) same =
  cong₂ _∨_ (same key value) (anyCong first second rows same)

deleteMissing : ∀ world key → DB.lookup key world ≡ nothing → DB.delete key world ≡ world
deleteMissing [] key missing = refl
deleteMissing ((stored , value) ∷ rows) key missing with key ≟ stored
... | yes same with missing
...   | ()
deleteMissing ((stored , value) ∷ rows) key missing | no different = cong ((stored , value) ∷_) (deleteMissing rows key missing)

anyInsert : ∀ test world key new → Allocation.Fresh world key → test key new ≡ false →
  E.anyRow test (DB.write key new world) ≡ E.anyRow test world
anyInsert test world key new fresh ignored rewrite deleteMissing world key (Allocation.freshAbsent world key fresh) | ignored = refl

observedInsert : ∀ {A : Set} (observe : Maybe O.Record → A) world key new → Allocation.Fresh world key →
  observe (just new) ≡ observe nothing → ∀ target →
  observe (DB.lookup target world) ≡ observe (DB.lookup target (DB.write key new world))
observedInsert observe world key new fresh ignored target with key ≟ target
... | yes refl = trans (cong observe (Allocation.freshAbsent world key fresh))
  (trans (sym ignored) (sym (cong observe (DB.writeVisible key new world))))
... | no different = sym (cong observe (DB.writePreservesOther key target new world different))

anyWrite : ∀ test world key old new → O.Unique world →
  DB.lookup key world ≡ just old → test key old ≡ false → test key new ≡ false →
  E.anyRow test (DB.write key new world) ≡ E.anyRow test world
anyWrite test world key old new unique found ignoredOld ignoredNew =
  boolSame (E.anyRow test after) (E.anyRow test world) backward forward
  where
  after = DB.write key new world
  afterUnique = Storage.writeUnique key new world unique

  forward : E.anyRow test world ≡ true → E.anyRow test after ≡ true
  forward positive with Observations.anyWitness test world positive
  ... | (target , value) , present , seen with key ≟ target
  ...   | yes refl = ⊥-elim (Effects.trueIsNotFalse (trans (sym seen)
    (trans (cong (test key) (just-injective (trans (sym (Order.memberLookup world key value unique present)) found))) ignoredOld)))
  ...   | no different = Observations.anyPresent test after target value
    (Observations.lookupMember after target value
      (trans (DB.writePreservesOther key target new world different) (Order.memberLookup world target value unique present))) seen

  backward : E.anyRow test after ≡ true → E.anyRow test world ≡ true
  backward positive with Observations.anyWitness test after positive
  ... | (target , value) , present , seen with key ≟ target
  ...   | yes refl = ⊥-elim (Effects.trueIsNotFalse (trans (sym seen)
    (trans (cong (test key) (just-injective (trans (sym (Order.memberLookup after key value afterUnique present))
      (DB.writeVisible key new world)))) ignoredNew)))
  ...   | no different = Observations.anyPresent test world target value
    (Observations.lookupMember world target value
      (trans (sym (DB.writePreservesOther key target new world different)) (Order.memberLookup after target value afterUnique present))) seen

filterCong : ∀ first second keys → (∀ key → first key ≡ second key) →
  E.filterKeys first keys ≡ E.filterKeys second keys
filterCong first second [] same = refl
filterCong first second (key ∷ keys) same with first key | second key | same key
... | true | true | equal = cong (key ∷_) (filterCong first second keys same)
... | true | false | ()
... | false | true | ()
... | false | false | equal = filterCong first second keys same

-- These actual body kinds do not supply registration, path-binding or symbol facts.
data Quiet : O.Record → Set where
  snapshot : ∀ owner selected nodes edges payload →
    Quiet (O.recordOf owner (O.structuralSnapshot selected nodes edges payload))
  selector : ∀ owner selected target → Quiet (O.recordOf owner (O.publishedView selected target))
  receipt : ∀ owner receiptData → Quiet (O.recordOf owner (O.receipt receiptData))
  reader : ∀ owner refs payload → Quiet (O.recordOf owner (O.activeReader refs payload))

module Model where
  module M = E.Model
  module Obs = Observations.Model

  quietRegistered : ∀ selection value → Quiet value → M.registeredValue selection value ≡ false
  quietRegistered selection ._ (snapshot owner selected nodes edges payload) = refl
  quietRegistered selection ._ (selector owner selected target) = refl
  quietRegistered selection ._ (receipt owner receiptData) = refl
  quietRegistered selection ._ (reader owner refs payload) = refl

  quietCheckout : ∀ selection value → Quiet value → M.checkoutObservation selection (just value) ≡ false
  quietCheckout selection ._ (snapshot owner selected nodes edges payload) = refl
  quietCheckout selection ._ (selector owner selected target) = refl
  quietCheckout selection ._ (receipt owner receiptData) = refl
  quietCheckout selection ._ (reader owner refs payload) = refl

  quietDelta : ∀ owner selected path value → Quiet value → M.deltaValue owner selected path value ≡ false
  quietDelta owner selected path ._ (snapshot storedOwner checkout nodes edges payload) = refl
  quietDelta owner selected path ._ (selector storedOwner checkout target) = refl
  quietDelta owner selected path ._ (receipt storedOwner receiptData) = refl
  quietDelta owner selected path ._ (reader storedOwner refs payload) = refl

  quietBinding : ∀ selection world owner selected path version value → Quiet value →
    M.bindingValue selection world owner selected path version value ≡ false
  quietBinding selection world owner selected path version ._ (snapshot storedOwner checkout nodes edges payload) = refl
  quietBinding selection world owner selected path version ._ (selector storedOwner checkout target) = refl
  quietBinding selection world owner selected path version ._ (receipt storedOwner receiptData) = refl
  quietBinding selection world owner selected path version ._ (reader storedOwner refs payload) = refl

  quietSymbol : ∀ value → Quiet value → M.symbolFacts (just value) ≡ nothing
  quietSymbol ._ (snapshot owner selected nodes edges payload) = refl
  quietSymbol ._ (selector owner selected target) = refl
  quietSymbol ._ (receipt owner receiptData) = refl
  quietSymbol ._ (reader owner refs payload) = refl

  quietEdge : ∀ value → Quiet value → M.edgeFacts (just value) ≡ nothing
  quietEdge ._ (snapshot owner selected nodes edges payload) = refl
  quietEdge ._ (selector owner selected target) = refl
  quietEdge ._ (receipt owner receiptData) = refl
  quietEdge ._ (reader owner refs payload) = refl

  module StableFacts (selection : E.Rule) (before after : O.World)
    (checkoutSame : ∀ selected → M.checkoutLive selection before selected ≡ M.checkoutLive selection after selected)
    (bindingRowsSame : ∀ owner selected path version →
      E.anyRow (λ key value → M.bindingValue selection before owner selected path version value) before ≡
      E.anyRow (λ key value → M.bindingValue selection after owner selected path version value) after)
    (symbolFactsSame : ∀ key → M.symbolFacts (DB.lookup key before) ≡ M.symbolFacts (DB.lookup key after))
    (edgeFactsSame : ∀ key → M.edgeFacts (DB.lookup key before) ≡ M.edgeFacts (DB.lookup key after)) where
    versionSame : ∀ owner selected path version →
      M.versionAtPath selection before owner selected path version ≡ M.versionAtPath selection after owner selected path version
    versionSame owner selected path version = cong₂ _∧_ (checkoutSame selected)
      (cong (M.included selection owner path ∧_) (bindingRowsSame owner selected path version))

    symbolValueSame : ∀ owner selected value →
      M.symbolObservation selection before owner selected value ≡ M.symbolObservation selection after owner selected value
    symbolValueSame owner selected value with M.symbolFacts value
    ... | nothing = refl
    ... | just (storedOwner , version , path) = cong (E.sameOwner owner storedOwner ∧_) (versionSame owner selected path version)

    symbolSame : ∀ owner selected symbol →
      M.symbolVisible selection before owner selected symbol ≡ M.symbolVisible selection after owner selected symbol
    symbolSame owner selected symbol = trans (symbolValueSame owner selected (DB.lookup symbol before))
      (cong (M.symbolFromFacts selection after owner selected)
        (symbolFactsSame symbol))

    edgeValueSame : ∀ owner selected value →
      M.edgeObservation selection before owner selected value ≡ M.edgeObservation selection after owner selected value
    edgeValueSame owner selected value with M.edgeFacts value
    ... | nothing = refl
    ... | just (storedOwner , source , target) = cong (E.sameOwner owner storedOwner ∧_)
      (cong₂ _∧_ (symbolSame owner selected source) (symbolSame owner selected target))

    edgeSame : ∀ owner selected edge →
      M.edgeVisible selection before owner selected edge ≡ M.edgeVisible selection after owner selected edge
    edgeSame owner selected edge = trans (edgeValueSame owner selected (DB.lookup edge before))
      (cong (M.edgeFromFacts selection after owner selected)
        (edgeFactsSame edge))

    projectSame : ∀ value → M.project selection before value ≡ M.project selection after value
    projectSame value with Observations.snapshotView value
    ... | Observations.plain nonSnapshot = trans (Obs.projectionPlain selection before value nonSnapshot)
      (sym (Obs.projectionPlain selection after value nonSnapshot))
    ... | Observations.snapshot owner selected nodes edges payload with E.ownerEqual owner (E.targetOwner selection)
    ...   | no different = refl
    ...   | yes same = cong₂ (λ ns es → O.recordOf owner (O.structuralSnapshot selected ns es payload))
      (filterCong (M.symbolVisible selection before owner selected) (M.symbolVisible selection after owner selected) nodes
        (symbolSame owner selected))
      (filterCong (M.edgeVisible selection before owner selected) (M.edgeVisible selection after owner selected) edges
        (edgeSame owner selected))

    projectSame value | Observations.delta owner selected version path answer =
      Storage.Model.projectWorldIndependent selection before after value (λ ())

    canonicalPersists : ∀ value → M.project selection before value ≡ value → M.project selection after value ≡ value
    canonicalPersists value canonical = trans (sym (projectSame value)) canonical

  module Write (selection : E.Rule) (before : O.World) (key : ℕ) (old new : O.Record)
    (unique : O.Unique before) (found : DB.lookup key before ≡ just old)
    (oldQuiet : Quiet old) (newQuiet : Quiet new) where
    after = DB.write key new before

    registeredSame : M.familyRegistered selection before ≡ M.familyRegistered selection after
    registeredSame = sym (anyWrite (λ key value → M.registeredValue selection value) before key old new unique found
      (quietRegistered selection old oldQuiet) (quietRegistered selection new newQuiet))

    checkoutSame : ∀ selected → M.checkoutLive selection before selected ≡ M.checkoutLive selection after selected
    checkoutSame = observedWrite (M.checkoutObservation selection) before key old new found
      (trans (quietCheckout selection old oldQuiet) (sym (quietCheckout selection new newQuiet)))

    deltaSame : ∀ owner selected path → M.hasDelta owner selected path before ≡ M.hasDelta owner selected path after
    deltaSame owner selected path = sym (anyWrite (λ key value → M.deltaValue owner selected path value)
      before key old new unique found (quietDelta owner selected path old oldQuiet) (quietDelta owner selected path new newQuiet))

    bindingSame : ∀ owner selected path version value →
      M.bindingValue selection before owner selected path version value ≡ M.bindingValue selection after owner selected path version value
    bindingSame owner selected path version value =
      cong (λ overridden → M.bindingSelected selection value ∧ M.bindingWithDelta overridden owner selected path version value) (deltaSame owner selected path)

    bindingRowsSame : ∀ owner selected path version →
      E.anyRow (λ key value → M.bindingValue selection before owner selected path version value) before ≡
      E.anyRow (λ key value → M.bindingValue selection after owner selected path version value) after
    bindingRowsSame owner selected path version = trans
      (sym (anyWrite (λ key value → M.bindingValue selection before owner selected path version value)
        before key old new unique found
        (quietBinding selection before owner selected path version old oldQuiet)
        (quietBinding selection before owner selected path version new newQuiet)))
      (anyCong (λ key value → M.bindingValue selection before owner selected path version value)
        (λ key value → M.bindingValue selection after owner selected path version value) after
        (λ key value → bindingSame owner selected path version value))

    module Stable = StableFacts selection before after checkoutSame bindingRowsSame
      (observedWrite M.symbolFacts before key old new found
        (trans (quietSymbol old oldQuiet) (sym (quietSymbol new newQuiet))))
      (observedWrite M.edgeFacts before key old new found
        (trans (quietEdge old oldQuiet) (sym (quietEdge new newQuiet))))
    open Stable public

  module Insert (selection : E.Rule) (before : O.World) (key : ℕ) (new : O.Record)
    (fresh : Allocation.Fresh before key) (quiet : Quiet new) where
    after = DB.write key new before

    registeredSame : M.familyRegistered selection before ≡ M.familyRegistered selection after
    registeredSame = sym (anyInsert (λ key value → M.registeredValue selection value) before key new fresh
      (quietRegistered selection new quiet))

    checkoutSame : ∀ selected → M.checkoutLive selection before selected ≡ M.checkoutLive selection after selected
    checkoutSame = observedInsert (M.checkoutObservation selection) before key new fresh (quietCheckout selection new quiet)

    deltaSame : ∀ owner selected path → M.hasDelta owner selected path before ≡ M.hasDelta owner selected path after
    deltaSame owner selected path = sym (anyInsert (λ key value → M.deltaValue owner selected path value)
      before key new fresh (quietDelta owner selected path new quiet))

    bindingSame : ∀ owner selected path version value →
      M.bindingValue selection before owner selected path version value ≡ M.bindingValue selection after owner selected path version value
    bindingSame owner selected path version value =
      cong (λ overridden → M.bindingSelected selection value ∧ M.bindingWithDelta overridden owner selected path version value) (deltaSame owner selected path)

    bindingRowsSame : ∀ owner selected path version →
      E.anyRow (λ key value → M.bindingValue selection before owner selected path version value) before ≡
      E.anyRow (λ key value → M.bindingValue selection after owner selected path version value) after
    bindingRowsSame owner selected path version = trans
      (sym (anyInsert (λ key value → M.bindingValue selection before owner selected path version value)
        before key new fresh (quietBinding selection before owner selected path version new quiet)))
      (anyCong (λ key value → M.bindingValue selection before owner selected path version value)
        (λ key value → M.bindingValue selection after owner selected path version value) after
        (λ key value → bindingSame owner selected path version value))

    module Stable = StableFacts selection before after checkoutSame bindingRowsSame
      (observedInsert M.symbolFacts before key new fresh (quietSymbol new quiet))
      (observedInsert M.edgeFacts before key new fresh (quietEdge new quiet))
    open Stable public
