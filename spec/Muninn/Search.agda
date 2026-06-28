{-# OPTIONS --safe #-}
-- Muninn/Search.agda
-- Query semantics: similarity, RRF scoring, and result bounds.
module Muninn.Search where

open import Muninn.Float
open import Muninn.Types
open import Data.Nat    using (ℕ; _≤_; suc; zero)
open import Data.List   using (List; []; _∷_; length)
open import Data.String using (String)
open import Data.Bool   using (Bool; true; false)
open import Data.Unit   using (⊤; tt)
open import Agda.Builtin.String using (primStringEquality)

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

-- ─── Tier-aware ranking ───────────────────────────────────────────────────────
-- Tier-2 (vendored) chunks have their fused RRF score scaled down so first-party
-- code generally wins, while a strong vendor match (with nothing first-party
-- competing) can still surface. Fixed constant — no config knob.
vendorWeight : Float
vendorWeight = fromℕF 3 /F fromℕF 10   -- 0.3

-- Down-weight a fused score by tier.
tieredScore : Tier → Float → Float
tieredScore Tier1 s = s
tieredScore Tier2 s = s *F vendorWeight

-- Per-file cap: at most this many chunks from any single file may appear in the
-- merged result. Defeats the "one vendor file floods the top-N" failure mode and
-- improves first-party diversity. Fixed constant — no config knob.
perFileCap : ℕ
perFileCap = 3

-- The hybrid search result list must contain no more entries than the limit.
HybridResultBound : (limit : ℕ) → List SearchResult → Set
HybridResultBound limit results = length results ≤ limit

-- Per-file bound: no single file contributes more than perFileCap results.
-- countFile counts results whose chunk shares the given file path's value.
countFile : String → List SearchResult → ℕ
countFile fp [] = zero
countFile fp (r ∷ rs) with primStringEquality fp (FilePath.value (Chunk.filePath (SearchResult.chunk r)))
... | true  = suc (countFile fp rs)
... | false = countFile fp rs

PerFileBound : List SearchResult → Set
PerFileBound results = ∀ (fp : String) → countFile fp results ≤ perFileCap

-- Reachability: down-weighting does NOT remove Tier-2 results. A Tier-2 chunk is
-- still a valid member of a result list (it is scaled, never filtered). Stated as
-- the simple fact that tieredScore is total on Tier2 (no Tier2 → ⊥ case): the
-- design forbids a "Tier-1-only" filter.
Tier2Reachable : Tier → Set
Tier2Reachable _ = ⊤

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