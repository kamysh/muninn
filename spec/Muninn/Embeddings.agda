-- Muninn/Embeddings.agda
-- Embedding backend types, canonical dimensions, and the RepoDimMatchesBackend
-- invariant that ties each repo's stored dimension to its registration backend.
module Muninn.Embeddings where

open import Muninn.Types
open import Muninn.Float                                       using (Float)
open import Data.Nat  using (ℕ)
open import Data.List using (List; length)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Unit using (⊤; tt)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_)

data EmbeddingBackend : Set where
  Voyage : EmbeddingBackend   -- voyage-code-3       (1024 dims)
  OpenAI : EmbeddingBackend   -- text-embedding-3-small (1536 dims)
  Local  : EmbeddingBackend   -- potion-base-32M model2vec static embeddings (512 dims)

-- Each backend produces vectors of a fixed, well-known dimension.
EmbeddingDimension : EmbeddingBackend → ℕ
EmbeddingDimension Voyage = 1024
EmbeddingDimension OpenAI = 1536
EmbeddingDimension Local  = 512

-- The dimension stored on a Repo must equal the canonical dimension for the
-- backend active at registration time.  Set once, never changes, so the
-- per-repo VECTOR(n) column stays consistent even if config is later switched.
RepoDimMatchesBackend : Repo → EmbeddingBackend → Set
RepoDimMatchesBackend repo backend =
  Repo.embeddingDim repo ≡ EmbeddingDimension backend

-- ─── Stored Embedding Validity ────────────────────────────────────────────────

-- If a chunk carries an embedding vector its length must exactly equal the
-- repo's registered dimension.  This closes two bugs:
--   1. Empty embeddings (length 0) silently stored and later causing vector
--      distance failures — the repo dim is always ≥ 384, so length 0 ≢ dim.
--   2. Dimension mismatch from a backend switch being silently accepted by the
--      incremental watcher but rejected at query time.
-- Helper: dispatch on presence/absence of an embedding.
-- Pattern matching on the LHS avoids the NoParseForLHS restriction on `with`
-- inside type-valued functions.
private
  EmbeddingConstraint : Maybe (List Float) → Repo → Set
  EmbeddingConstraint nothing    _    = ⊤
  EmbeddingConstraint (just emb) repo = length emb ≡ Repo.embeddingDim repo

ValidStoredEmbedding : Chunk → Repo → Set
ValidStoredEmbedding c repo = EmbeddingConstraint (Chunk.embedding c) repo

-- Every chunk in a repo's store satisfies ValidStoredEmbedding.
-- Enforced at write time by both the full index path and the watcher.
ConsistentRepoEmbeddings : List Chunk → Repo → Set
ConsistentRepoEmbeddings chunks repo =
  ∀ (c : Chunk) → c ∈ chunks → ValidStoredEmbedding c repo
