{-# OPTIONS --safe #-}
-- Git is the ignore authority; Muninn consumes complete scoped observations.
module Muninn.GitIgnore where

open import Data.Nat using (ℕ; _≟_)
open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Bool using (Bool; true; T)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no; does)
open import Relation.Nullary.Decidable using (map′; _×-dec_; toWitness; isYes≗does; dec-true)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

-- Logical incarnations, not a prescribed filesystem or database encoding.
-- Generation covers relevant Git/index/ignore inputs, not just HEAD.
record Context : Set where
  constructor context
  field family checkout generation : ℕ

context? : ∀ (first second : Context) → Dec (first ≡ second)
context? (context family checkout generation) (context otherFamily otherCheckout otherGeneration) = map′
  (λ { (refl , refl , refl) → refl })
  (λ { refl → refl , refl , refl })
  ((family ≟ otherFamily) ×-dec ((checkout ≟ otherCheckout) ×-dec (generation ≟ otherGeneration)))

record Query : Set where
  constructor query
  field at : Context
        paths : List String
        unique : Unique paths

-- Reply is a provider input from one complete batch. Decoding a partial stream
-- cannot construct it. This specifies the adapter contract, not Git internals.
data Answers : List String → Set where
  none : Answers []
  more : ∀ {path paths} → Bool → Answers paths → Answers (path ∷ paths)

read : ∀ {path paths} → Answers paths → path ∈ paths → Bool
read (more ignored rest) (here refl) = ignored
read (more ignored rest) (there later) = read rest later

record Reply (request : Query) : Set where
  constructor reply
  field answers : Answers (Query.paths request)

record Answer (path : String) : Set where
  constructor observed
  field request : Query
        response : Reply request
        requested : path ∈ Query.paths request

at : ∀ {path} → Answer path → Context
at answer = Query.at (Answer.request answer)

ignored : ∀ {path} → Answer path → Bool
ignored answer = read (Reply.answers (Answer.response answer)) (Answer.requested answer)

fresh : ∀ {path} → Context → Answer path → Bool
fresh current answer = does (context? current (at answer))

freshSound : ∀ {path} current (answer : Answer path) → fresh current answer ≡ true → current ≡ at answer
freshSound current answer accepted = toWitness {a? = context? current (at answer)}
  (subst T (sym (trans (isYes≗does (context? current (at answer))) accepted)) tt)

freshComplete : ∀ {path} current (answer : Answer path) → current ≡ at answer → fresh current answer ≡ true
freshComplete current answer same = dec-true (context? current (at answer)) same

accept : ∀ current request → Reply request → ∀ {path} → path ∈ Query.paths request → Maybe (Answer path)
accept current request response requested with context? current (Query.at request)
... | yes same = just (observed request response requested)
... | no stale = nothing

acceptedFresh : ∀ current request response {path} (requested : path ∈ Query.paths request) answer →
  accept current request response requested ≡ just answer → current ≡ at answer
acceptedFresh current request response requested answer accepted with context? current (Query.at request)
... | no stale = impossible accepted
  where
  impossible : nothing ≡ just answer → current ≡ at answer
  impossible ()
... | yes same with accepted
...   | refl = same

-- A saved answer belongs to published data. Later policy edits reuse its Git
-- default; fresh indexing must obtain a fresh-context answer. Repacking preserved
-- entries retains the original query context rather than inventing a new one.
-- Paused/Git-suspended views therefore need no unsafe query of conflicted input.
