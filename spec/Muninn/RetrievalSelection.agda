{-# OPTIONS --safe #-}
-- Executable ordering and bounded pages; exact lookup owes global completeness.
module Muninn.RetrievalSelection where
import Muninn.RetrievalNumerics as N
import Muninn.Types as T
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _*_; _≟_; _≤?_; z≤n; s≤s)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Char using (toℕ)
open import Data.String using (String; toList)
import Data.String as String
open import Data.List using (List; []; _∷_; length; take)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

-- Ties use immutable chunk identity, then path, never hash-map iteration order.
lexical : List Data.Char.Char → List Data.Char.Char → Bool
lexical [] ys = true
lexical (x ∷ xs) [] = false
lexical (x ∷ xs) (y ∷ ys) with toℕ x ≟ toℕ y
... | yes _ = lexical xs ys
... | no _ = does (toℕ x ≤? toℕ y)

module By (Candidate : Set) (key : Candidate → ℕ) (path : Candidate → T.FilePath)
  (numerator denominator : Candidate → ℕ) where
  same : Candidate → Candidate → Bool
  same first second = does (key first ≟ key second) ∧ does (T.FilePath.value (path first) String.≟ T.FilePath.value (path second))
  tie : Candidate → Candidate → Bool
  tie first second with key first ≟ key second
  ... | yes _ = lexical (toList (T.FilePath.value (path first))) (toList (T.FilePath.value (path second)))
  ... | no _ = does (key first ≤? key second)
  before : Candidate → Candidate → Bool
  before first second with (numerator first * denominator second) ≟
    (numerator second * denominator first)
  ... | yes _ = tie first second
  ... | no _ = does ((numerator second * denominator first) ≤? (numerator first * denominator second))
  insert : Candidate → List Candidate → List Candidate
  insert first [] = first ∷ []
  insert first (second ∷ rest) with before first second
  ... | true = first ∷ second ∷ rest
  ... | false = second ∷ insert first rest
  ordered : List Candidate → List Candidate
  ordered [] = []
  ordered (first ∷ rest) = insert first (ordered rest)
  page : ℕ → List Candidate → List Candidate
  page limit candidates = take limit (ordered candidates)

  insertSound : ∀ first rows result → result ∈ insert first rows → result ≡ first ⊎ result ∈ rows
  insertSound first [] .first (here refl) = inj₁ refl
  insertSound first (second ∷ rows) result member with before first second
  ... | true with member
  ...   | here refl = inj₁ refl
  ...   | there later = inj₂ later
  insertSound first (second ∷ rows) .second (here refl) | false = inj₂ (here refl)
  insertSound first (second ∷ rows) result (there later) | false with insertSound first rows result later
  ... | inj₁ same = inj₁ same
  ... | inj₂ included = inj₂ (there included)
  orderedSound : ∀ rows result → result ∈ ordered rows → result ∈ rows
  orderedSound (first ∷ rows) result member with insertSound first (ordered rows) result member
  ... | inj₁ refl = here refl
  ... | inj₂ included = there (orderedSound rows result included)
  takeSound : ∀ limit (rows : List Candidate) result → result ∈ take limit rows → result ∈ rows
  takeSound (suc limit) (first ∷ rows) .first (here refl) = here refl
  takeSound (suc limit) (first ∷ rows) result (there later) = there (takeSound limit rows result later)
  pageSound : ∀ limit rows result → result ∈ page limit rows → result ∈ rows
  pageSound limit rows result member = orderedSound rows result (takeSound limit (ordered rows) result member)
  takeBound : ∀ limit (rows : List Candidate) → length (take limit rows) ≤ limit
  takeBound zero rows = z≤n
  takeBound (suc limit) [] = z≤n
  takeBound (suc limit) (first ∷ rows) = s≤s (takeBound limit rows)
  pageBound : ∀ limit rows → length (page limit rows) ≤ limit
  pageBound limit rows = takeBound limit (ordered rows)

  insertFirst : ∀ first rows → first ∈ insert first rows
  insertFirst first [] = here refl
  insertFirst first (second ∷ rows) with before first second
  ... | true = here refl
  ... | false = there (insertFirst first rows)
  insertOld : ∀ first rows result → result ∈ rows → result ∈ insert first rows
  insertOld first (second ∷ rows) result present with before first second
  ... | true = there present
  ... | false with present
  ...   | here refl = here refl
  ...   | there later = there (insertOld first rows result later)
  orderedComplete : ∀ rows result → result ∈ rows → result ∈ ordered rows
  orderedComplete (first ∷ rows) .first (here refl) = insertFirst first (ordered rows)
  orderedComplete (first ∷ rows) result (there later) = insertOld first (ordered rows) result (orderedComplete rows result later)


  Present : Candidate → List Candidate → Set
  Present candidate rows = Data.List.Relation.Unary.Any.Any (λ row → same candidate row ≡ true) rows
  count : Candidate → List Candidate → ℕ
  count candidate [] = 0
  count candidate (row ∷ rows) with same candidate row
  ... | true = suc (count candidate rows)
  ... | false = count candidate rows
  -- This is the user outcome over *all* matching eligible candidates, not a
  -- script's candidate subset. Missing nearer results cannot satisfy it.
  record Top (limit : ℕ) (universe results : List Candidate) : Set where
    field bounded : length results ≤ limit
          eligible : ∀ result → result ∈ results → Present result universe
          noBetterOmitted : ∀ candidate result → candidate ∈ universe → result ∈ results →
            before candidate result ≡ true → Present candidate results
          fills : length results < limit → ∀ candidate → candidate ∈ universe → Present candidate results
          unique : ∀ candidate → count candidate results ≤ 1

module For (Candidate : Set) (key : Candidate → ℕ) (path : Candidate → T.FilePath) (score : Candidate → N.Rank) where
  open By Candidate key path (λ c → N.Rank.numerator (score c)) (λ c → N.Rank.denominator (score c)) public
