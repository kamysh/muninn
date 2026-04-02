-- Muninn/Search.agda
-- Query semantics: similarity, RRF scoring, and result bounds.
module Muninn.Search where

open import Muninn.Float
open import Muninn.Types
open import Data.Nat  using (ℕ; _≤_; suc; zero)
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

-- ─── Query Limit Validity ─────────────────────────────────────────────────────

-- Upper bound on query limits.  Without this, a caller supplying limit=10⁹
-- would cause the search layer to attempt a billion-row fetch, exhausting
-- memory.  1 000 is the server-enforced ceiling.
MAX_LIMIT : ℕ
MAX_LIMIT = 1000

-- A limit value is valid when it is at least 1 (non-empty result set expected)
-- and at most MAX_LIMIT (prevents unbounded memory allocation).
record ValidLimit (n : ℕ) : Set where
  field positive : 1 ≤ n
        bounded  : n ≤ MAX_LIMIT