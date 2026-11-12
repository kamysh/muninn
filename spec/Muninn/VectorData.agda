{-# OPTIONS --safe #-}
-- Typed derived vector data, independent of transport and physical tables.
module Muninn.VectorData where
import Muninn.Worktree as W
open import Muninn.Float using (Float; fromℕF)
open import Agda.Builtin.Float using (primFloatIsNaN; primFloatIsInfinite; primFloatEquality)
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_)
open import Data.List using (List; []; _∷_; length)
open import Data.String using (String)
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

finite : List Float → Bool
finite [] = true
finite (value ∷ rest) = not (primFloatIsNaN value) ∧ (not (primFloatIsInfinite value) ∧ finite rest)

nonzero : List Float → Bool
nonzero [] = false
nonzero (value ∷ rest) = not (primFloatEquality value (fromℕF 0)) ∨ nonzero rest

-- A dimension-only check is insufficient for a usable cosine-search vector.
Valid : ℕ → List Float → Set
Valid dimension values = 0 < dimension × (length values ≡ dimension ×
  (finite values ≡ true × nonzero values ≡ true))

record Value : Set where
  constructor value
  field profile : W.EmbeddingKey
        source : String -- exact normalized text submitted to the provider
        values : List Float
        valid : Valid (W.EmbeddingKey.dimension profile) values

record Guidance : Set where
  field reason nextAction : String
        reasonPresent : reason ≢ ""
        actionPresent : nextAction ≢ ""

-- Pending means that valid vectors are still needed, not that a worker is
-- currently running. Accepted-job liveness is reported by WorkQueue separately.
data State : Set where
  pending : W.EmbeddingKey → String → State
  waiting : W.EmbeddingKey → String → Guidance → State
  usable : Value → State

profile : State → W.EmbeddingKey
profile (pending selected source) = selected
profile (waiting selected source guidance) = selected
profile (usable saved) = Value.profile saved

source : State → String
source (pending selected text) = text
source (waiting selected text guidance) = text
source (usable saved) = Value.source saved
