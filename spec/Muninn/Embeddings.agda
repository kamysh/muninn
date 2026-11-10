{-# OPTIONS --safe #-}
-- Muninn/Embeddings.agda
-- Embedding backend types, canonical dimensions, and the RepoDimMatchesBackend
-- invariant that ties each repo's stored dimension to its registration backend.
module Muninn.Embeddings where

open import Muninn.Types
import Muninn.VectorData as Vector
open import Muninn.Float                                       using (Float)
open import Data.Nat  using (ℕ)
open import Data.List using (List; length)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

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
-- backend active for this derived-index incarnation. Changing the profile
-- requires explicit recreation, including its dimensioned vector storage.
RepoDimMatchesBackend : Repo → EmbeddingBackend → Set
RepoDimMatchesBackend repo backend =
  Repo.embeddingDim repo ≡ EmbeddingDimension backend

-- ─── Stored Embedding Validity ────────────────────────────────────────────────

-- State and payload must agree. Text remains valid while vectors are pending
-- or need attention. Usable vectors are nonempty, finite, nonzero and match
-- the registered dimension; family/profile association is checked on owned rows.
private
  EmbeddingConstraint : EmbeddingState → Maybe (List Float) → Repo → Set
  EmbeddingConstraint Pending nothing repo = ⊤
  EmbeddingConstraint Absent nothing repo = ⊤
  EmbeddingConstraint Embedded (just values) repo = Vector.Valid (Repo.embeddingDim repo) values
  EmbeddingConstraint _ _ _ = ⊥

ValidStoredEmbedding : Chunk → Repo → Set
ValidStoredEmbedding c repo = EmbeddingConstraint (Chunk.embeddingState c) (Chunk.embedding c) repo

ConsistentRepoEmbeddings : List Chunk → Repo → Set
ConsistentRepoEmbeddings chunks repo = ∀ c → c ∈ chunks → ValidStoredEmbedding c repo
