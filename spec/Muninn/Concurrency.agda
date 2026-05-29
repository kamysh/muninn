{-# OPTIONS --safe #-}
-- Muninn/Concurrency.agda
-- Index-mutex concurrency invariants.
--
-- The mutex itself is a PostgreSQL session-scoped advisory lock, modelled in
-- Muninn.AdvisoryLock (re-exported here). Liveness is the session: the DB frees
-- the lock when the holding process dies, so there is no heartbeat, no staleness
-- window, and mutual exclusion is structural (a single Lock value) rather than a
-- postulated invariant that a staleness threshold could violate.
--
-- This module adds the repo-level guards the implementation upholds around the
-- lock, plus the watcher-eviction invariant.
module Muninn.Concurrency where

open import Muninn.Types
open import Muninn.AdvisoryLock public
open import Data.List using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

-- ─── Unregister Safety ────────────────────────────────────────────────────────
-- `muninn remove` drops the chunks table and removes the repo row. It must only
-- proceed when no one is indexing — i.e. the advisory lock is free. The
-- implementation enforces this by acquiring the lock before deleting (and holding
-- it for the delete); if it cannot acquire, it refuses.

UnregisterSafe : Lock → Set
UnregisterSafe lk = lk ≡ Free

-- ─── Daemon Watch Guard ───────────────────────────────────────────────────────
-- The daemon must not attach a file-change watcher to a repo whose index is in
-- progress (a watcher write would race the indexer's delete-and-reinsert). There
-- is no cheap non-acquiring read of the advisory lock, so the implementation uses
-- the indexedAt discipline instead: every index resets indexedAt = nothing at its
-- start (mark_unindexed), so a repo with indexedAt set has no index in progress.
-- The daemon attaches a watcher exactly when indexedAt is set.

DaemonMayWatch : Repo → Set
DaemonMayWatch repo = Repo.indexedAt repo ≢ nothing

-- ─── Watcher Eviction Invariant ───────────────────────────────────────────────
-- After each scan_and_dispatch, every repo in the `watched` map must still appear
-- in the live repo list (not yet unregistered). Implemented by
-- `watched.retain(|id, _| live_ids.contains(id))`. Independent of the lock.

WatchedSubsetOfLive : List RepoId → List RepoId → Set
WatchedSubsetOfLive watched live =
  ∀ (r : RepoId) → r ∈ watched → r ∈ live
