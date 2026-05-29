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

-- ─── File Path Validity ───────────────────────────────────────────────────────

-- A file path used in chunk storage or deletion must not be the empty string.
-- Passing "" to delete_file_chunks executes vacuously; passing "" to
-- upsert_chunk would store an unaddressable chunk.
NonEmptyFilePath : FilePath → Set
NonEmptyFilePath fp = ¬ (FilePath.value fp ≡ "")