{-# OPTIONS --safe #-}
-- Replacing private bookkeeping cannot invalidate references from other rows.
module Muninn.PrivateReceipt where

import Muninn.OwnedState as O
import Muninn.CleanupStorage as Storage
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
import Data.List.Relation.Unary.All as All
open All using (All; []; _∷_)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Bool using (true)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst)
module DB = O.DB

writeOther : ∀ world key new source ref → O.target ref ≢ key →
  O.Resolves world source ref → O.Resolves (DB.write key new world) source ref
writeOther world key new source ref distinct resolved = record
  { value = O.Resolves.value resolved
  ; found = trans (DB.writePreservesOther key (O.target ref) new world (λ same → distinct (sym same))) (O.Resolves.found resolved)
  ; rightKind = O.Resolves.rightKind resolved
  ; rightOwner = O.Resolves.rightOwner resolved }

shiftRefs : ∀ world key new source refs → All (O.Resolves world source) refs →
  All (λ ref → O.target ref ≢ key) refs → All (O.Resolves (DB.write key new world) source) refs
shiftRefs world key new source [] [] [] = []
shiftRefs world key new source (ref ∷ refs) (resolved ∷ rest) (distinct ∷ others) =
  writeOther world key new source ref distinct resolved ∷ shiftRefs world key new source refs rest others

shiftSound : ∀ world key new rows → All (O.SoundReferences world) rows → All (O.NoIncomingTo key) rows →
  All (O.SoundReferences (DB.write key new world)) rows
shiftSound world key new [] [] [] = []
shiftSound world key new ((slot , value) ∷ rows) (resolved ∷ rest) (distinct ∷ others) =
  shiftRefs world key new (O.owner value) (O.references (O.body value)) resolved distinct ∷
    shiftSound world key new rows rest others

replacePrivate : ∀ world key old new → O.Admissible world → DB.lookup key world ≡ just old →
  O.privateTarget (O.kind (O.body old)) ≡ true → O.Placed new →
  O.references (O.body new) ≡ [] → O.Admissible (DB.write key new world)
replacePrivate world key old new valid found hidden placed refs = record
  { unique = Storage.writeUnique key new world (O.Admissible.unique valid)
  ; placed = placed ∷ O.deleteAll key world (O.Admissible.placed valid)
  ; sound = subst (All (O.Resolves (DB.write key new world) (O.owner new))) (sym refs) [] ∷ O.deleteAll key world (shiftSound world key new world (O.Admissible.sound valid)
      (O.privateUnreferenced key world old valid found hidden))
  ; privateBookkeeping = subst (All O.PublicReference) (sym refs) [] ∷ O.deleteAll key world (O.Admissible.privateBookkeeping valid) }
