{-# OPTIONS --safe #-}
-- PostgreSQL English analysis is a fixed provider, never a handler goal or LLM.
module Muninn.RetrievalText where
import Muninn.RetrievalNumerics as Numeric
open import Muninn.Float using (Float)
open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (ℕ)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

-- The source adapter binds this independent environment to PostgreSQL's actual
-- versioned English dictionary and ts_rank; execution cannot supply another.
record Engine : Set where
  field dictionaryVersion : String
        versionPresent : dictionaryVersion ≢ ""
        normalize : String → List String
        rank64 : String → String → Float

module Using (engine : Engine) where
  record Match (query content : String) : Set where
    field meaningful : Engine.normalize engine query ≢ []
          allWords : ∀ word → word ∈ Engine.normalize engine query → word ∈ Engine.normalize engine content
  record Score (query content : String) : Set where
    field rank : Numeric.Rank
          actualRank : Numeric.Rank.value rank ≡ Engine.rank64 engine query content
  emptyQueryCannotMatch : ∀ query content → Engine.normalize engine query ≡ [] → Match query content → ⊥
  emptyQueryCannotMatch query content empty matched = Match.meaningful matched empty
