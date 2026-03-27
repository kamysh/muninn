-- spec/AiMem.agda
-- Formal specification for the ai-mem indexed code search MCP server.
-- Float arithmetic is postulated throughout; holes (?) mark proof obligations
-- that are acceptable at the specification stage.
module AiMem where

open import Data.String  using (String)
open import Data.List    using (List; length)
open import Data.Maybe   using (Maybe; nothing; just; map)
open import Data.Nat     using (ℕ; _≤_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)

-- ─── Postulated Float support ──────────────────────────────────────────────────
-- Agda's built-in Float does not expose ordered arithmetic in a convenient way,
-- so we postulate the operations we need.  These are realised by IEEE 754
-- doubles in every concrete backend.

postulate
  Float    : Set
  _+F_     : Float → Float → Float
  _/F_     : Float → Float → Float
  fromℕF   : ℕ → Float

infixl 6 _+F_
infixl 7 _/F_

-- ─── Core Types ────────────────────────────────────────────────────────────────

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

-- A chunk is a contiguous slice of a source file with an optional embedding.
record Chunk : Set where
  field id        : ChunkId
        repoId    : RepoId
        filePath  : FilePath
        range     : LineRange
        content   : String
        embedding : Maybe (List Float)   -- absent until the chunk is embedded

-- A registered repository.
record Repo : Set where
  field id        : RepoId
        path      : FilePath
        name      : String
        indexedAt : Maybe String          -- ISO-8601 timestamp; nothing = never indexed
        config    : Maybe String          -- JSON configuration blob

-- A single result returned by a search query.
record SearchResult : Set where
  field chunk  : Chunk
        score  : Float

-- ─── Symbol Types ──────────────────────────────────────────────────────────────

data SymbolKind : Set where
  Function : SymbolKind
  Class    : SymbolKind
  Module   : SymbolKind
  Import   : SymbolKind

record Symbol : Set where
  field name     : String
        kind     : SymbolKind
        filePath : FilePath
        range    : LineRange
        chunkId  : ChunkId

-- ─── Structural Graph Types ────────────────────────────────────────────────────

data Relation : Set where
  Calls        : Relation
  Imports      : Relation
  Defines      : Relation
  InheritsFrom : Relation

record StructuralEdge : Set where
  field from     : ChunkId
        to       : ChunkId
        relation : Relation

-- ─── Repo Registration Invariant ───────────────────────────────────────────────
-- No two repos in a well-formed registry may share the same file-system path.
-- Expressed as: equal paths imply equal identities.

UniqueRepoPaths : List Repo → Set
UniqueRepoPaths repos =
  ∀ (r1 r2 : Repo) →
    Repo.path r1 ≡ Repo.path r2 →
    Repo.id  r1 ≡ Repo.id  r2

-- ─── Indexing State Machine ────────────────────────────────────────────────────

data IndexState : Set where
  Unindexed : IndexState   -- repo registered, never indexed
  Indexing  : IndexState   -- full (re)index in progress
  Indexed   : IndexState   -- index is up to date
  Watching  : IndexState   -- indexed + file-watcher active
  Stale     : IndexState   -- watcher detected changes not yet applied

-- Valid state transitions, encoded as an indexed inductive type so that only
-- the permitted edges exist.
data IndexTransition : IndexState → IndexState → Set where
  startIndex    : IndexTransition Unindexed Indexing   -- first indexing run
  finishIndex   : IndexTransition Indexing  Indexed    -- indexing complete
  startReindex  : IndexTransition Indexed   Indexing   -- manual reindex
  attachWatcher : IndexTransition Indexed   Watching   -- start watching
  detectChange  : IndexTransition Watching  Stale      -- watcher fires
  reindexStale  : IndexTransition Stale     Indexing   -- reindex after stale

-- ─── Validity Predicates ────────────────────────────────────────────────────────

-- The end line of a range must be at or after the start line.
ValidRange : LineRange → Set
ValidRange r = LineRange.start r ≤ LineRange.end r

-- A chunk's content must be non-empty (cannot equal the empty string).
ValidChunk : Chunk → Set
ValidChunk c = ¬ (Chunk.content c ≡ "")
  where
    open import Relation.Nullary using (¬_)

-- ─── Query Semantics ───────────────────────────────────────────────────────────

-- Cosine similarity is a Float known to lie in [0, 1].
record Similarity : Set where
  field value : Float

-- Reciprocal Rank Fusion score for a result at position `rank` (1-based).
-- The standard constant k = 60 dampens the influence of high ranks.
--   rrfScore(rank) = 1 / (60 + rank)
private
  floatRRFK : Float
  floatRRFK = fromℕF 60

  floatOne : Float
  floatOne = fromℕF 1

rrfScore : ℕ → Float
rrfScore rank = floatOne /F (floatRRFK +F fromℕF rank)

-- The hybrid search result list must contain no more entries than the
-- caller-requested limit.
HybridResultBound : (limit : ℕ) → List SearchResult → Set
HybridResultBound limit results = length results ≤ limit

-- ─── Embedding Backend Dimensions ─────────────────────────────────────────────

data EmbeddingBackend : Set where
  Voyage : EmbeddingBackend   -- voyage-code-3
  OpenAI : EmbeddingBackend   -- text-embedding-3-small
  Local  : EmbeddingBackend   -- default fastembed model

-- Each backend produces vectors of a fixed dimension.
EmbeddingDimension : EmbeddingBackend → ℕ
EmbeddingDimension Voyage = 1024
EmbeddingDimension OpenAI = 1536
EmbeddingDimension Local  = 768