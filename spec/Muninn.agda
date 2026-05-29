-- spec/Muninn.agda
-- Formal specification for the Muninn indexed code search MCP server.
-- This top-level module re-exports all sub-specifications so that importers
-- get the full specification in one open.
--
-- Sub-modules:
--   Muninn.Float      — postulated IEEE 754 Float operations
--   Muninn.IndexFsm   — (--safe) indexing FSM: holder kinds, preemption, configure decision
--   Muninn.Types      — core domain types (Chunk, Repo, SearchResult, …)
--   Muninn.Graph      — symbol kinds, structural edges, and per-repo graph
--   Muninn.Storage    — RepoStorage, UniqueRepoPaths, isolation invariants
--   Muninn.Index      — daemon dispatch, ValidRange, ValidChunk (re-exports IndexFsm)
--   Muninn.Search     — Similarity, RRF scoring, HybridResultBound
--   Muninn.Embeddings — EmbeddingBackend, EmbeddingDimension, RepoDimMatchesBackend
--   Muninn.Config     — GlobalConfig, RepoConfig, EffectiveConfig, merge, DimFrozen, discovery
--   Muninn.Cli        — CLI command AST, argument constraints, pre/postconditions
--   Muninn.Knowledge     — KnowledgeItem, validity invariants, repo scoping, search bounds
--   Muninn.Concurrency   — heartbeat-based distributed mutex, lock acquisition, watcher eviction
module Muninn where

open import Muninn.Float        public
open import Muninn.IndexFsm     public
open import Muninn.Types        public
open import Muninn.Graph        public
open import Muninn.Storage      public
open import Muninn.Index        public
open import Muninn.Search       public
open import Muninn.Embeddings   public
open import Muninn.Config       public
open import Muninn.Cli          public
open import Muninn.Knowledge    public
open import Muninn.Concurrency  public
