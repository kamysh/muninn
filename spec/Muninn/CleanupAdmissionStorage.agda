{-# OPTIONS --safe #-}
module Muninn.CleanupAdmissionStorage where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.CleanupObservations as Observations
import Muninn.CleanupStorage as Storage
import Muninn.CleanupProtection as Protection
import Muninn.ReceiptTypes as Receipt
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool)
open import Data.String using (String)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.All as All
open All using (All; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
module DB = O.DB

-- Weak references remain reserved even after their indexed rows are gone.
weakIds : O.Body → List ℕ
weakIds (O.registration _) = []
weakIds (O.checkout _) = []
weakIds (O.creationIntent _) = []
weakIds (O.defaults _) = []
weakIds (O.policyVersion _ _) = []
weakIds (O.currentPolicy _) = []
weakIds (O.note _) = []
weakIds (O.notePosting _ _) = []
weakIds (O.noteVector _ _) = []
weakIds (O.fileVersion _) = []
weakIds (O.baseBinding _ _ _) = []
weakIds (O.deltaBinding _ _ _ _) = []
weakIds (O.basePointer _) = []
weakIds (O.chunk _ _) = []
weakIds (O.posting _ _) = []
weakIds (O.vector _ _) = []
weakIds (O.symbol _ _ _) = []
weakIds (O.edge _ _ _) = []
weakIds (O.structuralSnapshot _ _ _ _) = []
weakIds (O.legacy _ _ _) = []
weakIds (O.staging _ _) = []
weakIds (O.acceptedWork _ _) = []
weakIds (O.cleanupWork _ ids payload) = ids
weakIds (O.activeReader _ _) = []
weakIds (O.continuation ids payload) = ids
weakIds (O.receipt (Receipt.entry id (Receipt.active input names work))) = []
weakIds (O.receipt (Receipt.entry id (Receipt.finished input names reply))) = []
weakIds (O.receipt (Receipt.entry id (Receipt.used))) = []
weakIds (O.migration _) = []
weakIds (O.usage _) = []
weakIds (O.bootstrap _) = []
weakIds (O.modelCache _) = []
weakIds (O.coordination _) = []
weakIds (O.schemaResource _) = []
weakIds (O.graphResource _ _ _) = []
weakIds (O.publishedView _ _) = []
weakIds (O.logFile _) = []
weakIds (O.bootstrapStage _) = []

reserved : O.World → List ℕ
reserved [] = []
reserved ((slot , value) ∷ rows) = slot ∷ (weakIds (O.body value) ++ reserved rows)

rowReserved : ∀ world key value → (key , value) ∈ world → key ∈ reserved world
rowReserved ((key , value) ∷ rows) .key .value (here refl) = here refl
rowReserved ((slot , stored) ∷ rows) key value (there present) = there (∈-++⁺ʳ (weakIds (O.body stored)) (rowReserved rows key value present))

weakReserved : ∀ world slot value key → (slot , value) ∈ world → key ∈ weakIds (O.body value) → key ∈ reserved world
weakReserved ((slot , value) ∷ rows) .slot .value key (here refl) tracked = there (∈-++⁺ˡ tracked)
weakReserved ((other , stored) ∷ rows) slot value key (there present) tracked =
  there (∈-++⁺ʳ (weakIds (O.body stored)) (weakReserved rows slot value key present tracked))

Fresh : O.World → ℕ → Set
Fresh world slot = ¬ (slot ∈ reserved world)

storedReserved : ∀ world key value → DB.lookup key world ≡ just value → key ∈ reserved world
storedReserved world key value found = rowReserved world key value (Observations.lookupMember world key value found)

freshAbsent : ∀ world slot → Fresh world slot → DB.lookup slot world ≡ nothing
freshAbsent world slot fresh with DB.lookup slot world in found
... | nothing = refl
... | just value = ⊥-elim (fresh (storedReserved world slot value found))

oldLookup : ∀ world slot added → Fresh world slot → ∀ key value → DB.lookup key world ≡ just value → DB.lookup key (DB.write slot added world) ≡ just value
oldLookup world slot added fresh key value found = trans (DB.writePreservesOther slot key added world
  (λ { refl → fresh (storedReserved world key value found) })) found

oldResolve : ∀ world slot added → Fresh world slot → ∀ source ref → O.Resolves world source ref → O.Resolves (DB.write slot added world) source ref
oldResolve world slot added fresh source ref resolved = record
  { value = O.Resolves.value resolved
  ; found = oldLookup world slot added fresh (O.target ref) (O.Resolves.value resolved) (O.Resolves.found resolved)
  ; rightKind = O.Resolves.rightKind resolved; rightOwner = O.Resolves.rightOwner resolved }

insertAdmissible : ∀ world slot added → O.Admissible world → Fresh world slot → O.Placed added →
  All (O.Resolves world (O.owner added)) (O.references (O.body added)) → O.PrivateBookkeepingReferences added → O.Admissible (DB.write slot added world)
insertAdmissible world slot added valid fresh placed resolved privateRefs = record
  { unique = Storage.writeUnique slot added world (O.Admissible.unique valid)
  ; placed = placed ∷ O.deleteAll slot world (O.Admissible.placed valid)
  ; sound = All.map (λ {ref} proof → oldResolve world slot added fresh (O.owner added) ref proof) resolved ∷ O.deleteAll slot world shifted
  ; privateBookkeeping = privateRefs ∷ O.deleteAll slot world (O.Admissible.privateBookkeeping valid) }
  where
  shifted : All (O.SoundReferences (DB.write slot added world)) world
  shifted = All.map (λ {row} refs → All.map (λ {ref} proof → oldResolve world slot added fresh (O.owner (proj₂ row)) ref proof) refs) (O.Admissible.sound valid)

module Model where
  module M = E.Model
  module Pins = Protection.Model

  insertionSafety : ∀ selection world slot added → Fresh world slot → M.Safety selection world (DB.write slot added world)
  insertionSafety selection world slot added fresh = record
    { unrelated = λ key value found owner → oldLookup world slot added fresh key value found
    ; metadata = λ key value found metadata → oldLookup world slot added fresh key value found
    ; needed = λ key value found needed → value , oldLookup world slot added fresh key value found , refl , (λ key present → present) , (λ key present → present)
    ; protected = λ key value found protected → oldLookup world slot added fresh key value found }

  existingUsePreserved : ∀ selection world slot added → Fresh world slot → ∀ key → M.Protected selection world key → M.Protected selection (DB.write slot added world) key
  existingUsePreserved selection world slot added fresh key = Pins.protectedSurvives selection world (DB.write slot added world) key
    (insertionSafety selection world slot added fresh)
