-- AiMem/Embeddings.agda
-- Embedding backend types, canonical dimensions, and the RepoDimMatchesBackend
-- invariant that ties each repo's stored dimension to its registration backend.
module AiMem.Embeddings where

open import AiMem.Types
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

data EmbeddingBackend : Set where
  Voyage : EmbeddingBackend   -- voyage-code-3       (1024 dims)
  OpenAI : EmbeddingBackend   -- text-embedding-3-small (1536 dims)
  Local  : EmbeddingBackend   -- default fastembed model (768 dims)

-- Each backend produces vectors of a fixed, well-known dimension.
EmbeddingDimension : EmbeddingBackend → ℕ
EmbeddingDimension Voyage = 1024
EmbeddingDimension OpenAI = 1536
EmbeddingDimension Local  = 768

-- The dimension stored on a Repo must equal the canonical dimension for the
-- backend active at registration time.  Set once, never changes, so the
-- per-repo VECTOR(n) column stays consistent even if config is later switched.
RepoDimMatchesBackend : Repo → EmbeddingBackend → Set
RepoDimMatchesBackend repo backend =
  Repo.embeddingDim repo ≡ EmbeddingDimension backend