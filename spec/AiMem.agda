-- spec/AiMem.agda
-- Formal specification for the ai-mem indexed code search MCP server.
-- This top-level module re-exports all sub-specifications so that importers
-- get the full specification in one open.
--
-- Sub-modules:
--   AiMem.Float      — postulated IEEE 754 Float operations
--   AiMem.Types      — core domain types (Chunk, Repo, SearchResult, …)
--   AiMem.Graph      — symbol kinds, structural edges, and per-repo graph
--   AiMem.Storage    — RepoStorage, UniqueRepoPaths, isolation invariants
--   AiMem.Index      — IndexState machine, ValidRange, ValidChunk
--   AiMem.Search     — Similarity, RRF scoring, HybridResultBound
--   AiMem.Embeddings — EmbeddingBackend, EmbeddingDimension, RepoDimMatchesBackend
module AiMem where

open import AiMem.Float      public
open import AiMem.Types      public
open import AiMem.Graph      public
open import AiMem.Storage    public
open import AiMem.Index      public
open import AiMem.Search     public
open import AiMem.Embeddings public