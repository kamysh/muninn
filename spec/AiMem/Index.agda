-- AiMem/Index.agda
-- Indexing state machine and chunk validity predicates.
module AiMem.Index where

open import AiMem.Types
open import Data.Nat    using (_≤_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

-- ─── Indexing State Machine ────────────────────────────────────────────────────

data IndexState : Set where
  Unindexed : IndexState   -- repo registered, never indexed
  Indexing  : IndexState   -- full (re)index in progress
  Indexed   : IndexState   -- index is up to date
  Watching  : IndexState   -- indexed + file-watcher active
  Stale     : IndexState   -- watcher detected changes not yet applied

-- Valid transitions encoded as an indexed inductive type so that only the
-- permitted edges exist.
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

-- A chunk's content must be non-empty.
ValidChunk : Chunk → Set
ValidChunk c = ¬ (Chunk.content c ≡ "")