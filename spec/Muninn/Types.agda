{-# OPTIONS --safe #-}
-- Muninn/Types.agda
-- Core domain types: identifiers, chunks, repos, and search results.
module Muninn.Types where

open import Muninn.Float
open import Data.String using (String)
open import Data.List   using (List)
open import Data.Bool   using (Bool; true; false)
open import Data.Maybe  using (Maybe)
open import Data.Nat    using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

record UUID : Set where
  field value : String

record FilePath : Set where
  field value : String

record RepoId : Set where
  field value : UUID

record ChunkId : Set where
  field value : UUID

record LineRange : Set where
  field start : ℕ
        end   : ℕ

-- The tier a chunk belongs to. First-party source is indexed at full weight and
-- embedded eagerly; vendored dependency code is down-weighted in search and
-- embedded lazily by the daemon. See Muninn.Config.classify.
data Tier : Set where
  Tier1 : Tier   -- first-party source
  Tier2 : Tier   -- vendored dependency

-- A chunk's embedding lifecycle state.
data EmbeddingState : Set where
  Embedded : EmbeddingState   -- vector present
  Pending  : EmbeddingState   -- Tier-2 chunk awaiting daemon backfill (full-text only)
  Absent   : EmbeddingState   -- embedder returned empty (distinct from Pending)

-- A contiguous slice of a source file with an optional embedding vector.
record Chunk : Set where
  field id             : ChunkId
        repoId         : RepoId
        filePath       : FilePath
        range          : LineRange
        content        : String
        embedding      : Maybe (List Float)   -- absent until the chunk is embedded
        tier           : Tier
        embeddingState : EmbeddingState

-- A registered repository.
record Repo : Set where
  field id                : RepoId
        path              : FilePath
        name              : String
        indexedAt         : Maybe String       -- ISO-8601 timestamp; nothing = never indexed
        everIndexed       : Bool               -- true after the first successful index; survives reindex reset
        embeddingDim      : ℕ                 -- VECTOR(n) dimension recorded at registration time
        preemptRequested  : Bool               -- a foreground job is waiting for the index lock
                                               -- (the lock itself is a session advisory lock, not a column)
        paused            : Bool               -- `muninn pause` set this; the daemon skips paused
                                               -- repos (no reindex, no watcher) without dropping data

-- A single result returned by a search query.
record SearchResult : Set where
  field chunk : Chunk
        score : Float

-- A Tier-1 chunk is always eagerly embedded: only Tier 2 may defer (Pending).
-- The foreground indexer must uphold this — it never leaves a first-party chunk
-- awaiting backfill.
Tier1NeverPending : Chunk → Set
Tier1NeverPending c = Chunk.tier c ≡ Tier1 → Chunk.embeddingState c ≢ Pending