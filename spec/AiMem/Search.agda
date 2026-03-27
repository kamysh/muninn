-- AiMem/Search.agda
-- Query semantics: similarity, RRF scoring, and result bounds.
module AiMem.Search where

open import AiMem.Float
open import AiMem.Types
open import Data.Nat  using (ℕ; _≤_)
open import Data.List using (List; length)

-- Cosine similarity: a Float known to lie in [0, 1].
record Similarity : Set where
  field value : Float

-- Reciprocal Rank Fusion score at position rank (0-based).
--   rrfScore(rank) = 1 / (60 + rank)
-- k = 60 is the standard RRF constant that dampens the influence of high ranks.
private
  k   : Float
  k   = fromℕF 60
  one : Float
  one = fromℕF 1

rrfScore : ℕ → Float
rrfScore rank = one /F (k +F fromℕF rank)

-- The hybrid search result list must contain no more entries than the limit.
HybridResultBound : (limit : ℕ) → List SearchResult → Set
HybridResultBound limit results = length results ≤ limit