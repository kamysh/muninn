{-# OPTIONS --safe #-}
-- Installation-wide usage rows and log entries are retained individually.
module Muninn.RepositoryHistory where

open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.String using (String)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

-- Owners describe the repositories actually mentioned by the record. An
-- entry shared by several repositories is removed as a whole.
record Entry : Set where
  constructor entry
  field owners : List ℕ
        content : String
open Entry public

record History : Set where
  constructor history
  field usage logs buffered : List Entry
open History public

mentions : ℕ → List ℕ → Bool
mentions family [] = false
mentions family (first ∷ rest) with family ≟ first
... | yes _ = true
... | no _ = mentions family rest

cleanRows : ℕ → List Entry → List Entry
cleanRows family [] = []
cleanRows family (item ∷ rest) with mentions family (owners item)
... | true = cleanRows family rest
... | false = item ∷ cleanRows family rest

clean : ℕ → History → History
clean family before = history (cleanRows family (usage before)) (cleanRows family (logs before)) (cleanRows family (buffered before))

cleanRowsNoFamily : ∀ family rows → All (λ item → mentions family (owners item) ≡ false) (cleanRows family rows)
cleanRowsNoFamily family [] = []
cleanRowsNoFamily family (item ∷ rows) with mentions family (owners item) in observed
... | true = cleanRowsNoFamily family rows
... | false = observed ∷ cleanRowsNoFamily family rows

cleanRowsPreservesOther : ∀ family rows item → item ∈ rows → mentions family (owners item) ≡ false → item ∈ cleanRows family rows
cleanRowsPreservesOther family (item ∷ rows) .item (here refl) keep rewrite keep = here refl
cleanRowsPreservesOther family (first ∷ rows) item (there later) keep with mentions family (owners first)
... | true = cleanRowsPreservesOther family rows item later keep
... | false = there (cleanRowsPreservesOther family rows item later keep)

cleanRowsRetry : ∀ family rows → cleanRows family (cleanRows family rows) ≡ cleanRows family rows
cleanRowsRetry family [] = refl
cleanRowsRetry family (item ∷ rows) with mentions family (owners item) in observed
... | true = cleanRowsRetry family rows
... | false rewrite observed = cong (item ∷_) (cleanRowsRetry family rows)

cleanRetry : ∀ family before → clean family (clean family before) ≡ clean family before
cleanRetry family (history usage logs buffered) rewrite cleanRowsRetry family usage | cleanRowsRetry family logs | cleanRowsRetry family buffered = refl

contains : ℕ → List Entry → Bool
contains family [] = false
contains family (item ∷ rows) with mentions family (owners item)
... | true = true
... | false = contains family rows

containsClean : ∀ family rows → contains family (cleanRows family rows) ≡ false
containsClean family [] = refl
containsClean family (item ∷ rows) with mentions family (owners item) in observed
... | true = containsClean family rows
... | false rewrite observed = containsClean family rows

emptyOf : ℕ → History → Bool
emptyOf family before with contains family (usage before) | contains family (logs before) | contains family (buffered before)
... | false | false | false = true
... | _ | _ | _ = false

cleanIsEmpty : ∀ family before → emptyOf family (clean family before) ≡ true
cleanIsEmpty family (history usage logs buffered) rewrite containsClean family usage | containsClean family logs | containsClean family buffered = refl
