{-# OPTIONS --safe #-}
-- Muninn/Storage.agda
-- Per-repo storage model and isolation invariants.
-- Each repo owns a dedicated chunk store and symbol graph; both are created
-- at registration and dropped at unregistration.
module Muninn.Storage where

open import Muninn.Types
open import Muninn.Graph
open import Data.List   using (List)
open import Data.Product using (Σ; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary                      using (¬_)
open import Data.List.Membership.Propositional    using (_∈_)

record RepoStorage : Set where
  field repo   : Repo
        chunks : List Chunk
        graph  : SymbolGraph

-- ─── Repo Registration Invariant ───────────────────────────────────────────────
-- No two repos in a well-formed registry may share the same file-system path.

UniqueRepoPaths : List Repo → Set
UniqueRepoPaths repos =
  ∀ (r1 r2 : Repo) →
    Repo.path r1 ≡ Repo.path r2 →
    Repo.id  r1 ≡ Repo.id  r2

-- ─── Storage Isolation Invariants ──────────────────────────────────────────────

-- All chunks in a repo's store must belong to that repo.
IsolatedChunks : RepoStorage → Set
IsolatedChunks s =
  ∀ (c : Chunk) →
    c ∈ RepoStorage.chunks s →
    Chunk.repoId c ≡ Repo.id (RepoStorage.repo s)

-- Helper: a ChunkId resolves to a chunk in the given list.
ChunkExists : ChunkId → List Chunk → Set
ChunkExists cid cs = Σ Chunk (λ c → (c ∈ cs) × (Chunk.id c ≡ cid))

-- Every symbol in the graph must reference a chunk that exists in the store.
IsolatedGraph : RepoStorage → Set
IsolatedGraph s =
  ∀ (sym : Symbol) →
    sym ∈ SymbolGraph.symbols (RepoStorage.graph s) →
    ChunkExists (Symbol.chunkId sym) (RepoStorage.chunks s)

-- GRAPH-WRITE TIMEOUT (Tier 2 safety net in the Rust pipeline)
-- ------------------------------------------------------------
-- Each call to the `muninn_cypher` SQL wrapper runs inside a transaction with
-- `SET LOCAL statement_timeout = graph_timeout_secs` (default 60 s). On
-- Postgres error 57014 (canceling statement due to statement timeout) the Rust
-- side rolls back, logs a structured warning naming the file, and continues
-- without propagating the error. The file's CHUNKS remain indexed (text and
-- semantic search keep working); the SYMBOL graph for that file is partial or
-- empty. The defence-in-depth motivation is that the AGE engine has been
-- observed to take 40+ minutes on a single MERGE/MATCH against an unindexed
-- per-label table at scale; the per-statement timeout prevents any future
-- regression from silently hanging an end-user's index.
--
-- IsolatedGraph IS PRESERVED unconditionally under any partial write. The
-- predicate quantifies over `SymbolGraph.symbols (RepoStorage.graph s)` — the
-- symbols actually stored in the graph — not over the symbols the pipeline
-- intended to write. Since the pipeline writes chunks BEFORE symbols (the
-- existing ordering discipline `index_file` follows), any symbol that lands in
-- the graph references a chunk that was persisted in a prior step. The set of
-- symbols that did NOT land for a timed-out file is simply absent from
-- `SymbolGraph.symbols`, so the ∀ never visits them. The reverse direction —
-- chunks without all their intended symbols — is the new accepted reality and
-- is NOT an invariant violation: there is no spec-level claim that every chunk
-- has corresponding graph nodes (structural search degrades gracefully for
-- those files, returning fewer results; full-text and semantic search are
-- unaffected). This is captured trivially below: any subset of a graph that
-- satisfies IsolatedGraph still satisfies the predicate over that subset.

IsolatedGraph-subset :
  ∀ (s : RepoStorage) (subset : List Symbol) →
  (∀ sym → sym ∈ subset →
    sym ∈ SymbolGraph.symbols (RepoStorage.graph s)) →
  IsolatedGraph s →
  ∀ (sym : Symbol) → sym ∈ subset →
  ChunkExists (Symbol.chunkId sym) (RepoStorage.chunks s)
IsolatedGraph-subset s subset subset⊆ iso sym sym∈subset =
  iso sym (subset⊆ sym sym∈subset)

-- PER-FILE INDEX TIMEOUT (file-level safety net in `pipeline::index_repo`)
-- ------------------------------------------------------------------------
-- Above and beyond the per-cypher GRAPH-WRITE timeout, `index_repo` wraps the
-- entire per-file pipeline (`index_file`) in `tokio::time::timeout(
-- FILE_INDEX_TIMEOUT_SECS, …)`. If any single file's parse + edge-extract +
-- chunking + embed + DB writes together exceed the watchdog, the loop records
-- a `SkipRecord` with reason "file timed out", emits a structured warning, and
-- moves to the next file. This addresses any failure mode that lives entirely
-- outside the AGE-cypher path — most notably the tree-sitter `collect_callees_rec`
-- recursion hangs observed on dense TypeScript .d.ts files (see issue #6).
--
-- IsolatedGraph IS PRESERVED, again unconditionally. The per-file timeout
-- fires BEFORE the file's chunks are written (the pipeline writes chunks then
-- symbols, so an early timeout means neither was written). The set of symbols
-- in the graph is therefore unchanged for that file — there is nothing new to
-- check the predicate against. Same argument as the per-cypher timeout above,
-- a degree more conservative.

-- ─── File Path Validity ───────────────────────────────────────────────────────

-- A file path used in chunk storage or deletion must not be the empty string.
-- Passing "" to delete_file_chunks executes vacuously; passing "" to
-- upsert_chunk would store an unaddressable chunk.
NonEmptyFilePath : FilePath → Set
NonEmptyFilePath fp = ¬ (FilePath.value fp ≡ "")