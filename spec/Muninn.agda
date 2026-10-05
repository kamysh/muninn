{-# OPTIONS --safe #-}
-- spec/Muninn.agda
-- Formal specification for the Muninn indexed code search MCP server.
-- This top-level module re-exports all sub-specifications so that importers
-- get the full specification in one open.
--
-- Sub-modules:
--   Muninn.Float        — postulated IEEE 754 Float operations
--   Muninn.AdvisoryLock — (--safe) the index mutex: advisory lock + preempt signal
--   Muninn.IndexFsm     — (--safe) index lifecycle FSM + configure decision
--   Muninn.Types        — core domain types (Chunk, Repo, SearchResult, …)
--   Muninn.Graph        — symbol kinds, structural edges, and per-repo graph
--   Muninn.Worktree     — immutable baselines, sparse overrides, file reuse
--   Muninn.FileMap      — file updates and minimal-overlay normalization laws
--   Muninn.Schema       — family pairs, application migrations and independent AGE readiness
--   Muninn.GraphMembership — explicit selected-edge membership and visibility
--   Muninn.Storage      — pair ownership, checkout isolation, artifact lifetime
--   Muninn.Index        — legacy/proposed daemon dispatch, validity (re-exports IndexFsm)
--   Muninn.Search     — Similarity, RRF scoring, HybridResultBound
--   Muninn.Embeddings — EmbeddingBackend, EmbeddingDimension, RepoDimMatchesBackend
--   Muninn.Config     — bootstrap, database family policy, DimFrozen, resolution
--   Muninn.Cli        — CLI command AST, argument constraints, pre/postconditions
--   Muninn.Knowledge     — KnowledgeItem, validity invariants, family scoping, search bounds
--   Muninn.Concurrency   — advisory-lock mutex (re-exports AdvisoryLock), watcher eviction
module Muninn where

open import Muninn.Float        public
open import Muninn.AdvisoryLock public
open import Muninn.IndexFsm     public
open import Muninn.Types        public
open import Muninn.Worktree     public
open import Muninn.FileMap      public
open import Muninn.Graph        public
open import Muninn.Schema       public
open import Muninn.GraphMembership public
open import Muninn.Storage      public
open import Muninn.Index        public
open import Muninn.Search       public
open import Muninn.Embeddings   public
open import Muninn.Config       public
open import Muninn.Policy       public
open import Muninn.Registration public
open import Muninn.Cli          public
open import Muninn.Knowledge    public
open import Muninn.Concurrency  public
