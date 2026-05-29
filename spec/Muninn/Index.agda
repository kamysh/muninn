{-# OPTIONS --safe #-}
-- Muninn/Index.agda
-- Chunk validity predicates and daemon dispatch logic.
--
-- The indexing state machine itself (IndexState, Step, holder kinds, preemption,
-- and the configure decision) lives in the --safe, postulate-free module
-- Muninn.IndexFsm, which this module re-exports. The mutex is the advisory lock
-- in Muninn.AdvisoryLock (re-exported via Muninn.Concurrency); the daemon's scan
-- decision below is a pure function of the observed lock occupancy and the repo's
-- indexedAt / everIndexed / preemptRequested.
module Muninn.Index where

open import Muninn.Types
open import Muninn.Concurrency
open import Muninn.IndexFsm public
open import Data.Bool   using (Bool; true; false)
open import Data.List   using (List)
open import Data.Maybe  using (Maybe; nothing; just)
open import Data.Nat    using (_≤_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

-- ─── Lock Precondition for Indexing Transitions ──────────────────────────────
-- Any transition INTO Indexing requires the advisory lock to be free (acquired
-- via pg_try_advisory_lock, or blockingly via pg_advisory_lock).

IndexingPre : Lock → Set
IndexingPre lk = lk ≡ Free

-- ─── Daemon Reindex Decision ─────────────────────────────────────────────────
-- The indexer daemon decides what to do for each repo on every scan cycle from
-- the repo's state alone. The advisory lock is NOT an input: contention is
-- detected operationally — `pg_try_advisory_lock` fails on the reindex path, and
-- the `indexed_at = NULL` discipline (every index resets it at the start) keeps
-- the watch branch out of an in-progress index. This mirrors the branch order in
-- crates/indexer scan_and_dispatch.
--
--   indexedAt = just _                          → Watch.
--   indexedAt = nothing, everIndexed = false    → Skip (never indexed; the
--                                                  daemon never first-indexes).
--   indexedAt = nothing, a foreground job waits → Skip (leave it for the CLI).
--   indexedAt = nothing, everIndexed = true     → Reindex (was indexed; reset).

data DaemonAction : Set where
  Skip    : DaemonAction   -- do nothing this cycle
  Reindex : DaemonAction   -- acquire the lock, spawn a full reindex
  Watch   : DaemonAction   -- attach a file-change watcher

daemonDecision : Repo → DaemonAction
daemonDecision repo with Repo.indexedAt repo
... | just _  = Watch
... | nothing with Repo.everIndexed repo | Repo.preemptRequested repo
...             | false | _     = Skip
...             | true  | true  = Skip
...             | true  | false = Reindex

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