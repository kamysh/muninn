-- Muninn/Index.agda
-- Indexing state machine, chunk validity predicates, and daemon dispatch logic.
module Muninn.Index where

open import Muninn.Types
open import Muninn.Concurrency
open import Data.Bool   using (Bool; true; false)
open import Data.List   using (List)
open import Data.Maybe  using (Maybe; nothing; just)
open import Data.Nat    using (_≤_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

-- ─── Indexing State Machine ────────────────────────────────────────────────────

data IndexState : Set where
  Unindexed : IndexState   -- repo registered, never indexed
  Indexing  : IndexState   -- full (re)index in progress (lock held)
  Indexed   : IndexState   -- index is up to date, no active task
  Watching  : IndexState   -- indexed + file-watcher active
  Stale     : IndexState   -- watcher detected changes not yet applied

-- The outcome of processing a batch of files.
-- NoneSucceeded is intentionally absent: a totally-failed batch must NOT
-- advance to Indexed.  Only a batch where at least one file was successfully
-- indexed may close the Indexing state.
data BatchOutcome : Set where
  AllSucceeded  : BatchOutcome  -- every file in the batch indexed without error
  SomeSucceeded : BatchOutcome  -- at least one indexed; others warned and skipped

-- Valid transitions encoded as an indexed inductive type so that only the
-- permitted edges exist.
--
-- All transitions INTO Indexing require the lock to be acquirable first
-- (CanAcquire), enforced at the call site.  The lock is released when the
-- transition OUT of Indexing fires (finishIndex / indexFailed).
data IndexTransition : IndexState → IndexState → Set where
  startIndex    : IndexTransition Unindexed Indexing            -- first index (CLI)
  finishIndex   : BatchOutcome → IndexTransition Indexing Indexed -- at-least-partial success
  indexFailed   : IndexTransition Indexing  Unindexed           -- total failure; lock released, stay unindexed
  startReindex  : IndexTransition Indexed   Indexing            -- daemon or CLI reindex
  attachWatcher : IndexTransition Indexed   Watching            -- daemon attaches watcher
  detectChange  : IndexTransition Watching  Stale               -- watcher fires
  reindexStale  : IndexTransition Stale     Indexing            -- reindex after stale

-- ─── Lock Precondition for Indexing Transitions ──────────────────────────────
-- Any transition INTO Indexing requires that the repo's lock is acquirable.
-- This is checked atomically via try_lock_repo (CAS on indexing_heartbeat).

IndexingPre : Repo → Set
IndexingPre repo = CanAcquire (Repo.indexingHeartbeat repo)

-- ─── Daemon Reindex Decision ─────────────────────────────────────────────────
-- The indexer daemon must decide what to do for each repo on every scan cycle.
-- The decision depends on three fields: indexingHeartbeat, indexedAt, everIndexed.
--
--   lock is live                              → Skip.
--     Another process (CLI or previous daemon task) holds the lock.
--     Do not interfere; it will notify when done.
--
--   lock not live, indexedAt = nothing, everIndexed = false → Skip.
--     Freshly registered, never indexed. User must run `muninn index` first.
--
--   lock not live, indexedAt = nothing, everIndexed = true  → Reindex.
--     Was indexed before; `muninn reindex` reset indexedAt. Daemon must act.
--
--   lock not live, indexedAt = just _                       → Watch.
--     Already indexed and no writer active; start or maintain a file-change watcher.

data DaemonAction : Set where
  Skip    : DaemonAction   -- do nothing this cycle
  Reindex : DaemonAction   -- acquire lock, spawn a full reindex
  Watch   : DaemonAction   -- attach a file-change watcher

-- Computable liveness check (bridges the postulated IsLive to Bool for pattern matching).
postulate isLiveBool : Maybe String → Bool

daemonDecision : Repo → DaemonAction
daemonDecision repo with isLiveBool (Repo.indexingHeartbeat repo)
... | true  = Skip   -- lock is held by another process; do not interfere
... | false with Repo.indexedAt repo | Repo.everIndexed repo
...           | just _  | _     = Watch
...           | nothing | true  = Reindex
...           | nothing | false = Skip

-- ─── Daemon Dispatch Idempotency ────────────────────────────────────────────
-- The daemon's scan loop runs on every NOTIFY and every 60 s poll tick.
-- daemonDecision may return Reindex for the same repo on consecutive scans
-- (indexed_at stays NULL until the reindex completes).
--
-- Invariant: the daemon must never have more than one in-flight action per repo.
-- A repo that is already being reindexed must be skipped even if daemonDecision
-- returns Reindex.  Likewise, a repo that already has a watcher must not get
-- a second one.
--
-- InFlight models the set of repo ids that currently have an active task.
-- The implementation tracks this as HashSet<Uuid> (for reindexing) and
-- HashMap<Uuid, _> (for watchers).

open import Data.List.Membership.Propositional using (_∈_)

InFlight : Set
InFlight = List RepoId

-- The daemon must not dispatch an action for a repo that is already in flight.
-- This predicate must hold before every dispatch.
UniqueDispatch : Repo → InFlight → Set
UniqueDispatch repo inflight = ¬ (Repo.id repo ∈ inflight)

-- ─── Validity Predicates ────────────────────────────────────────────────────────

-- The end line of a range must be at or after the start line.
ValidRange : LineRange → Set
ValidRange r = LineRange.start r ≤ LineRange.end r

-- A chunk's content must be non-empty.
ValidChunk : Chunk → Set
ValidChunk c = ¬ (Chunk.content c ≡ "")