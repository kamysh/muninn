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

import Muninn.Connection
import Muninn.DatabaseResumption
import Muninn.Database
import Muninn.Recovery
import Muninn.PublicationVisibility
import Muninn.ViewPublication
import Muninn.CurrentReader
import Muninn.StoredPolicy
import Muninn.PolicyCleanupBatch
import Muninn.GlobMatching
import Muninn.GlobLexing
import Muninn.GlobRanges
import Muninn.GlobTokens
import Muninn.GlobBody
import Muninn.RulePatterns
import Muninn.RuleScope
import Muninn.OrderedSelection
import Muninn.StrictGlob
import Muninn.PolicyRuleAdmission
import Muninn.ContentViews
import Muninn.ContentPublication
import Muninn.GenericFileMap
import Muninn.ArtifactIdentity
import Muninn.CanonicalChunks
import Muninn.CompletedWork
import Muninn.ArtifactReuse
import Muninn.IndexFileLimits
import Muninn.FileLimits
import Muninn.GitIgnore
import Muninn.GitDiscovery
import Muninn.InclusionTraversal
import Muninn.IndexSelection
import Muninn.AdmittedSelection
import Muninn.ViewReplacement
import Muninn.SnapshotPreparation
import Muninn.PublishedViews
import Muninn.OwnedState
import Muninn.Catalog
import Muninn.CatalogSources
import Muninn.Dialogue
import Muninn.RequestIdentity
import Muninn.ReceiptLedger
import Muninn.RequestAdmission
import Muninn.CleanupAdmission
import Muninn.CleanupResumption
import Muninn.ReaderRelease
import Muninn.ReaderReleaseCleanup
import Muninn.CleanupLoop
import Muninn.CleanupFinalization
import Muninn.CleanupScheduling
import Muninn.RecordAllocation
import Muninn.CleanupAlignment
import Muninn.CleanupHistory
import Muninn.CleanupCompletion
import Muninn.CleanupProgress
import Muninn.CleanupEffects
import Muninn.ExclusionClassifier
import Muninn.ExclusionOutcomes

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

import Muninn.CheckoutReconciliation

import Muninn.Retirement
import Muninn.RetirementControl
import Muninn.RetirementCleanup

-- Stable database identities and request-bound discovery dialogue (#32).
import Muninn.RepositoryIdentity
import Muninn.RepositoryDiscovery
import Muninn.IdentityCheckpoint
import Muninn.RegistryCreation
import Muninn.RepositoryRegistry
import Muninn.TransactionSequence
import Muninn.DirectoryConversion

-- Existing unregistration and complete forget-all outcomes (#34).
import Muninn.RemovalStore
import Muninn.RepositoryRemoval

-- Explicit start and durable work controls (#35).
import Muninn.WorkQueue
import Muninn.IndexControl
import Muninn.WorkControlStore
import Muninn.FirstStart

-- Text/symbol availability independent of vector preparation (#36).
import Muninn.VectorData
import Muninn.StagedVectors
import Muninn.TextPublication
import Muninn.VectorPublication

-- Explicit profile recreation preserves identity, notes and settings (#37).
import Muninn.RecreationStore
import Muninn.RepositoryProfile
import Muninn.ProfileRecreation

-- First search retains its intent and arranges authorized selected-checkout work (#38).
import Muninn.SearchTarget
import Muninn.SearchView
import Muninn.FirstSearch
import Muninn.SearchResumption
import Muninn.SearchReadiness

import Muninn.RetrievalNumerics

import Muninn.RetrievalCorpus

import Muninn.RetrievalText

import Muninn.RetrievalSelection

import Muninn.Retrieval

-- Complete selected-view hybrid fusion without per-file suppression (#40).
import Muninn.HybridNumbers
import Muninn.HybridRanking

-- Stable pagination and private typed continuation state (#41).
import Muninn.PaginationData
import Muninn.Pagination
import Muninn.PaginationStore

import Muninn.PaginationSource

import Muninn.PaginationTraversal

import Muninn.PaginationCommit

import Muninn.PaginationRanking

import Muninn.PaginationCodeCall

import Muninn.PaginationAdvance
