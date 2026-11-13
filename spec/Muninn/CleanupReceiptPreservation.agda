{-# OPTIONS --safe #-}
-- Indexed cleanup updates preserve the existing operation-receipt lookup.
module Muninn.CleanupReceiptPreservation where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.ReceiptLedger as Ledger
import Muninn.ReceiptTypes as Receipt
import Muninn.CatalogInputs as Input
import Muninn.CleanupEffects as Effects
import Muninn.CleanupNeed as Need
open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.String using (String)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
module DB = O.DB

indexedNotReceipt : ∀ id slot value → E.indexed value ≡ true → Ledger.inRecord id slot value ≡ nothing
indexedNotReceipt id slot (O.recordOf owner (O.fileVersion x)) proof = refl
indexedNotReceipt id slot (O.recordOf owner (O.baseBinding x y)) proof = refl
indexedNotReceipt id slot (O.recordOf owner (O.deltaBinding x y z)) proof = refl
indexedNotReceipt id slot (O.recordOf owner (O.basePointer x)) proof = refl
indexedNotReceipt id slot (O.recordOf owner (O.chunk x y)) proof = refl
indexedNotReceipt id slot (O.recordOf owner (O.posting x y)) proof = refl
indexedNotReceipt id slot (O.recordOf owner (O.vector x y)) proof = refl
indexedNotReceipt id slot (O.recordOf owner (O.symbol x y z)) proof = refl
indexedNotReceipt id slot (O.recordOf owner (O.edge x y z)) proof = refl
indexedNotReceipt id slot (O.recordOf owner (O.publishedView x y)) proof = refl
indexedNotReceipt id slot (O.recordOf owner (O.structuralSnapshot w x y z)) proof = refl
indexedNotReceipt id slot (O.recordOf owner (O.legacy x y)) proof = refl
indexedNotReceipt id slot (O.recordOf owner (O.staging x y)) proof = refl
indexedNotReceipt id slot (O.recordOf owner (O.graphResource x y z)) proof = refl
indexedNotReceipt id slot (O.recordOf owner (O.registration x)) ()
indexedNotReceipt id slot (O.recordOf owner (O.creationIntent x)) ()
indexedNotReceipt id slot (O.recordOf owner (O.defaults x)) ()
indexedNotReceipt id slot (O.recordOf owner (O.checkout x)) ()
indexedNotReceipt id slot (O.recordOf owner (O.policyVersion x y)) ()
indexedNotReceipt id slot (O.recordOf owner (O.currentPolicy x)) ()
indexedNotReceipt id slot (O.recordOf owner (O.note x)) ()
indexedNotReceipt id slot (O.recordOf owner (O.notePosting x y)) ()
indexedNotReceipt id slot (O.recordOf owner (O.noteVector x y)) ()
indexedNotReceipt id slot (O.recordOf owner (O.acceptedWork x y)) ()
indexedNotReceipt id slot (O.recordOf owner (O.cleanupWork x y z)) ()
indexedNotReceipt id slot (O.recordOf owner (O.activeReader x y)) ()
indexedNotReceipt id slot (O.recordOf owner (O.continuation x y)) ()
indexedNotReceipt id slot (O.recordOf owner (O.migration x)) ()
indexedNotReceipt id slot (O.recordOf owner (O.usage x)) ()
indexedNotReceipt id slot (O.recordOf owner (O.logFile x)) ()
indexedNotReceipt id slot (O.recordOf owner (O.bootstrap x)) ()
indexedNotReceipt id slot (O.recordOf owner (O.modelCache x)) ()
indexedNotReceipt id slot (O.recordOf owner (O.coordination x)) ()
indexedNotReceipt id slot (O.recordOf owner (O.schemaResource x)) ()
indexedNotReceipt id slot (O.recordOf owner (O.bootstrapStage x)) ()
indexedNotReceipt id slot (O.recordOf owner (O.receipt (Receipt.entry rid (Receipt.active meaning names work)))) ()
indexedNotReceipt id slot (O.recordOf owner (O.receipt (Receipt.entry rid (Receipt.finished meaning names result)))) ()
indexedNotReceipt id slot (O.recordOf owner (O.receipt (Receipt.entry rid Receipt.used))) ()

missingDelete : ∀ key world → DB.lookup key world ≡ nothing → DB.delete key world ≡ world
missingDelete key [] absent = refl
missingDelete key ((other , value) ∷ rest) absent with key ≟ other
... | yes refl = ⊥-elim (impossible absent)
  where
  impossible : just value ≡ nothing → ⊥
  impossible ()
... | no distinct = cong (λ tail → (other , value) ∷ tail) (missingDelete key rest absent)

findDelete : ∀ id key world value → O.Unique world → DB.lookup key world ≡ just value →
  E.indexed value ≡ true → Ledger.find id (DB.delete key world) ≡ Ledger.find id world
findDelete id key [] value unique () indexed
findDelete id key ((other , stored) ∷ rest) value (absent , unique) found indexed with key ≟ other
... | yes refl with key ≟ key
...   | no different = ⊥-elim (different refl)
...   | yes same rewrite missingDelete key rest absent |
      indexedNotReceipt id key stored (subst (λ v → E.indexed v ≡ true) (sym (just-injective found)) indexed) = refl
findDelete id key ((other , stored) ∷ rest) value (absent , unique) found indexed | no different
  with Ledger.inRecord id other stored
... | just receipt = refl
... | nothing = findDelete id key rest value unique found indexed

findWrite : ∀ id key world old new → O.Unique world → DB.lookup key world ≡ just old →
  E.indexed old ≡ true → E.indexed new ≡ true →
  Ledger.find id (DB.write key new world) ≡ Ledger.find id world
findWrite id key world old new unique found indexedOld indexedNew
  rewrite indexedNotReceipt id key new indexedNew = findDelete id key world old unique found indexedOld

module Model (excluded : List String → String → Bool) where
  module M = E.Model excluded
  module Needs = Need.Model excluded
  module Core (selection : E.Rule) (accepted : O.World) (intent : M.Intent selection accepted) where
    module Work = Effects.Model.Core excluded selection accepted intent

    preserves : ∀ id key world → O.Admissible world →
      Ledger.find id (Data.Product.proj₂ (DB.execute (Work.transaction key) world)) ≡ Ledger.find id world
    preserves id key world valid with Work.decide key world
    ... | Work.retain denied = refl
    ... | Work.erase (value , found , captured , owned , indexed , unneeded , unprotected , unreferenced) =
      findDelete id key world value (O.Admissible.unique valid) found indexed
    ... | Work.trim (value , found , captured , owned , indexed , needed , unprotected , changed) =
      findWrite id key world value (M.project selection world value) (O.Admissible.unique valid) found indexed
        (trans (cong E.indexedRole (Needs.projectClass selection world value)) indexed)
