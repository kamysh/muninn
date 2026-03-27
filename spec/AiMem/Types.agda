-- AiMem/Types.agda
-- Core domain types: identifiers, chunks, repos, and search results.
module AiMem.Types where

open import AiMem.Float
open import Data.String using (String)
open import Data.List   using (List)
open import Data.Maybe  using (Maybe)
open import Data.Nat    using (ℕ)

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

-- A contiguous slice of a source file with an optional embedding vector.
record Chunk : Set where
  field id        : ChunkId
        repoId    : RepoId
        filePath  : FilePath
        range     : LineRange
        content   : String
        embedding : Maybe (List Float)   -- absent until the chunk is embedded

-- A registered repository.
record Repo : Set where
  field id           : RepoId
        path         : FilePath
        name         : String
        indexedAt    : Maybe String   -- ISO-8601 timestamp; nothing = never indexed
        config       : Maybe String   -- JSON configuration blob
        embeddingDim : ℕ             -- VECTOR(n) dimension recorded at registration time

-- A single result returned by a search query.
record SearchResult : Set where
  field chunk : Chunk
        score : Float