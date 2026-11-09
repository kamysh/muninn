{-# OPTIONS --safe #-}
-- Mandatory reuse of completed values. No retry, lease or failure framework.
module Muninn.CompletedWork where

import Muninn.Database as Database
open import Data.Bool using (Bool; true; false)
open import Data.List using ([]; _∷_)
import Data.List.Relation.Unary.All as All
open All using (All; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

module For (Key Value : Set) (equal : (first second : Key) → Dec (first ≡ second)) where
  module Store = Database.Store Key Value equal

  -- A caller cannot select calculation while a completed value is present.
  data Action (key : Key) (rows : Store.Rows) : Set where
    reuse : (value : Value) → Store.lookup key rows ≡ just value → Action key rows
    calculate : Store.lookup key rows ≡ nothing → Action key rows

  next : ∀ key rows → Action key rows
  next key rows with Store.lookup key rows in found
  ... | just value = reuse value found
  ... | nothing = calculate found

  invokesProvider : ∀ {key rows} → Action key rows → Bool
  invokesProvider (reuse value found) = false
  invokesProvider (calculate absent) = true

  hitCannotCalculate : ∀ key rows value → Store.lookup key rows ≡ just value →
    (action : Action key rows) → invokesProvider action ≡ false
  hitCannotCalculate key rows value found (reuse cached present) = refl
  hitCannotCalculate key rows value found (calculate absent) with trans (sym found) absent
  ... | ()

  reusesExactValue : ∀ key rows value cached → Store.lookup key rows ≡ just value →
    Store.lookup key rows ≡ just cached → cached ≡ value
  reusesExactValue key rows value cached found reused = just-injective (trans (sym reused) found)

  lookupValid : ∀ (Valid : Key → Value → Set) key rows value →
    All (λ row → Valid (proj₁ row) (proj₂ row)) rows → Store.lookup key rows ≡ just value → Valid key value
  lookupValid Valid key [] value proofs ()
  lookupValid Valid key ((other , stored) ∷ rest) value (proof ∷ proofs) found with equal key other
  ... | yes refl with just-injective found
  ...   | refl = proof
  lookupValid Valid key ((other , stored) ∷ rest) value (proof ∷ proofs) found | no different =
    lookupValid Valid key rest value proofs found

  -- The first completed value is immutable. A repeat records no new work.
  remember : Key → Value → Store.Rows → Store.Rows
  remember key value rows with Store.lookup key rows
  ... | just cached = rows
  ... | nothing = Store.write key value rows

  keepsCompleted : ∀ key value rows cached → Store.lookup key rows ≡ just cached → remember key value rows ≡ rows
  keepsCompleted key value rows cached found with Store.lookup key rows
  ... | just stored = refl
  ... | nothing with found
  ...   | ()

  saved : ∀ key value rows → Σ Value (λ cached → Store.lookup key (remember key value rows) ≡ just cached)
  saved key value rows with Store.lookup key rows in found
  ... | just cached = cached , found
  ... | nothing = value , Store.writeVisible key value rows

  checkpointReuses : ∀ key value rows → invokesProvider (next key (remember key value rows)) ≡ false
  checkpointReuses key value rows with saved key value rows
  ... | cached , found = hitCannotCalculate key (remember key value rows) cached found (next key (remember key value rows))

  repeatIsIdempotent : ∀ key first second rows → remember key second (remember key first rows) ≡ remember key first rows
  repeatIsIdempotent key first second rows with saved key first rows
  ... | cached , found = keepsCompleted key second (remember key first rows) cached found

  -- Reconnection/yield may change other work. If the durable entry survives,
  -- every subsequent legal action still has to reuse it.
  survivingCheckpointReuses : ∀ key before after value → Store.lookup key before ≡ just value →
    Store.lookup key after ≡ Store.lookup key before → (action : Action key after) → invokesProvider action ≡ false
  survivingCheckpointReuses key before after value found preserved action = hitCannotCalculate key after value
    (trans preserved found) action

  otherWriteKeepsReuse : ∀ key other rows value stored → ¬ (other ≡ key) → Store.lookup key rows ≡ just value →
    (action : Action key (Store.write other stored rows)) → invokesProvider action ≡ false
  otherWriteKeepsReuse key other rows value stored distinct found action = hitCannotCalculate key (Store.write other stored rows) value
    (trans (Store.writePreservesOther other key stored rows distinct) found) action

  Unique : Store.Rows → Set
  Unique [] = ⊤
  Unique ((key , value) ∷ rows) = Store.lookup key rows ≡ nothing × Unique rows

  deleteUnique : ∀ key rows → Unique rows → Unique (Store.delete key rows)
  deleteUnique key [] valid = tt
  deleteUnique key ((other , value) ∷ rows) (absent , valid) with equal key other
  ... | yes same = deleteUnique key rows valid
  ... | no distinct = trans (Store.deletePreservesOther key other rows distinct) absent , deleteUnique key rows valid

  rememberUnique : ∀ key value rows → Unique rows → Unique (remember key value rows)
  rememberUnique key value rows unique with Store.lookup key rows
  ... | just cached = unique
  ... | nothing = Store.deleteAbsent key rows , deleteUnique key rows unique

  module Certified (Valid : Key → Value → Set) where
    record Cache : Set where
      constructor cache
      field rows : Store.Rows
            unique : Unique rows
            values : All (λ row → Valid (proj₁ row) (proj₂ row)) rows

    empty : Cache
    empty = cache [] tt []

    deleteValid : ∀ key rows → All (λ row → Valid (proj₁ row) (proj₂ row)) rows →
      All (λ row → Valid (proj₁ row) (proj₂ row)) (Store.delete key rows)
    deleteValid key [] proofs = []
    deleteValid key ((other , value) ∷ rows) (proof ∷ proofs) with equal key other
    ... | yes same = deleteValid key rows proofs
    ... | no distinct = proof ∷ deleteValid key rows proofs

    rememberValid : ∀ key value rows → All (λ row → Valid (proj₁ row) (proj₂ row)) rows → Valid key value →
      All (λ row → Valid (proj₁ row) (proj₂ row)) (remember key value rows)
    rememberValid key value rows proofs valid with Store.lookup key rows
    ... | just cached = proofs
    ... | nothing = valid ∷ deleteValid key rows proofs

    checkpoint : (key : Key) → (value : Value) → Valid key value → Cache → Cache
    checkpoint key value valid before = cache (remember key value (Cache.rows before))
      (rememberUnique key value (Cache.rows before) (Cache.unique before))
      (rememberValid key value (Cache.rows before) (Cache.values before) valid)

    nextAction : ∀ key before → Action key (Cache.rows before)
    nextAction key before = next key (Cache.rows before)

    reusedValueValid : ∀ key before value → Store.lookup key (Cache.rows before) ≡ just value → Valid key value
    reusedValueValid key before value found = lookupValid Valid key (Cache.rows before) value (Cache.values before) found
