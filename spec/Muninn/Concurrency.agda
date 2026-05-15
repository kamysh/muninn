-- Muninn/Concurrency.agda
-- Heartbeat-based distributed mutex for index_repo exclusion.
--
-- Design: a single `indexing_heartbeat TIMESTAMPTZ` column per repo.
--   NULL       → unlocked
--   just hb    → locked; last heartbeat pulse at hb
--
-- Liveness: a lock is "live" when the heartbeat is within the staleness
-- window.  A lock is "stale" when the heartbeat is set but old (holder is
-- dead).  The window is 2× the heartbeat interval (60 s pulse → stale after
-- 2 min).
--
-- Crucially the window measures PROCESS LIVENESS, not job duration.
-- A healthy 3-day reindex has a heartbeat from ~30 s ago and is never stale.
-- A crashed process stops pulsing immediately and becomes stale within 2 min.
module Muninn.Concurrency where

open import Muninn.Types
open import Data.Bool   using (Bool; true; false)
open import Data.Maybe  using (Maybe; nothing; just)
open import Data.List   using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.String using (String)
open import Data.Sum    using (_⊎_; inj₁; inj₂)
open import Data.Unit   using (⊤; tt)
open import Data.Empty  using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

-- ─── Liveness Predicates (abstract) ──────────────────────────────────────────
-- Time comparison is left abstract to avoid formalising wall-clock time.

postulate
  IsLive  : Maybe String → Set  -- heartbeat is recent (within staleness window)
  IsStale : Maybe String → Set  -- heartbeat is set but old (holder is dead)

  -- Mutual exclusion between Live and Stale.
  live-not-stale : ∀ hb → IsLive hb  → ¬ IsStale hb
  stale-not-live : ∀ hb → IsStale hb → ¬ IsLive  hb

  -- NULL heartbeat is neither live nor stale.
  null-not-live  : ¬ IsLive  nothing
  null-not-stale : ¬ IsStale nothing

-- Unlocked iff the column is NULL.
IsUnlocked : Maybe String → Set
IsUnlocked nothing  = ⊤
IsUnlocked (just _) = ⊥

-- ─── Acquisition Predicate ────────────────────────────────────────────────────
-- A process may acquire the lock iff the column is NULL or stale.
-- Implemented as an atomic CAS:
--   UPDATE repos
--      SET indexing_heartbeat = NOW()
--    WHERE id = $1
--      AND (indexing_heartbeat IS NULL
--           OR indexing_heartbeat < NOW() - INTERVAL '2 min')
-- PostgreSQL row-level locking guarantees exactly one concurrent UPDATE wins.

CanAcquire : Maybe String → Set
CanAcquire hb = IsUnlocked hb ⊎ IsStale hb

-- A live lock cannot be acquired by another process.
live-not-acquirable : ∀ hb → IsLive hb → ¬ CanAcquire hb
live-not-acquirable nothing   lv _          = null-not-live lv
live-not-acquirable (just _)  lv (inj₁ ())
live-not-acquirable (just _)  lv (inj₂ st)  = live-not-stale (just _) lv st

-- ─── Safety Invariant ─────────────────────────────────────────────────────────
-- At most one process holds a live lock for any given repo at any time.
-- This follows from CAS atomicity: two concurrent acquirers on the same row
-- compete; exactly one UPDATE wins (the other sees rows_affected = 0 and bails).
-- Stated as a predicate the implementation must uphold.

postulate
  AtMostOneWriter :
    ∀ (r : RepoId) (writers : List RepoId) →
      r ∈ writers →                -- r is claimed to hold the lock
      ∀ (r' : RepoId) → r' ∈ writers →
        RepoId.value r ≡ RepoId.value r'

-- ─── Unregister Safety ────────────────────────────────────────────────────────
-- `muninn unregister` drops the chunks table and removes the repo row.
-- Must only proceed when no writer holds the lock; otherwise the writer would
-- insert into a table that no longer exists.

UnregisterSafe : Repo → Set
UnregisterSafe repo = ¬ IsLive (Repo.indexingHeartbeat repo)

-- ─── Daemon Watch Guard ───────────────────────────────────────────────────────
-- The daemon must not attach a file-change watcher while a full reindex is in
-- progress (CLI or daemon task holds the lock for that repo).

DaemonMayWatch : Repo → Set
DaemonMayWatch repo = ¬ IsLive (Repo.indexingHeartbeat repo)

-- ─── Watcher Eviction Invariant ───────────────────────────────────────────────
-- After each scan_and_dispatch, every repo in the `watched` map must still
-- appear in the live repo list (not yet unregistered).
-- Implemented by `watched.retain(|id, _| live_ids.contains(id))`.

WatchedSubsetOfLive : List RepoId → List RepoId → Set
WatchedSubsetOfLive watched live =
  ∀ (r : RepoId) → r ∈ watched → r ∈ live