{-# OPTIONS --safe #-}
-- Muninn/AdvisoryLock.agda
-- The index mutex: a PostgreSQL session-scoped advisory lock plus one boolean
-- preemption signal. Replaces the heartbeat-timestamp mutex (the old
-- Muninn.Concurrency). Re-exported by Muninn.Concurrency.
--
-- Liveness is no longer a modelled clock. A held lock is held by a LIVE session;
-- the database frees it when the session ends (crash / kill -9 / connection
-- drop). So there is NO "held-but-stale" state — the case the heartbeat model
-- had to detect and override is unrepresentable here (see `Lock`).
--
-- The only persisted state is one boolean, `preempt`. The advisory lock itself is
-- a session resource, not a column, and it records NO holder identity — the
-- implementation has no `lock_holder` column and `pg_advisory_lock` does not
-- track a "kind". So the lock here is a bare Free/Held, matching reality.
-- `HolderKind` is retained only for the *task* identity in Muninn.IndexFsm
-- (the CLI indexes as Fg, the daemon as Bg — known by code path), not for the
-- lock. Which job holds the lock is therefore NOT observable from the lock; the
-- preempt flag is raised by any blocked foreground job (it cannot tell who holds
-- it), and the daemon's background task yields by polling that flag.
module Muninn.AdvisoryLock where

open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

-- The task identity used by Muninn.IndexFsm.Indexing. NOT part of the lock.
data HolderKind : Set where
  Fg : HolderKind   -- foreground CLI job; never preempted
  Bg : HolderKind   -- background daemon; yields to a waiting foreground job

-- The advisory lock. No holder identity, and no "held by a dead session" state:
-- the DB frees the lock at session end, so abandonment is indistinguishable from
-- a clean release and never produces a stale-held state.
data Lock : Set where
  Free : Lock
  Held : Lock

-- The whole persisted coordination state: lock occupancy plus the single boolean
-- column. (Occupancy mirrors the advisory lock, which is the source of truth;
-- the model keeps it explicit so transitions are visible.)
record Coord : Set where
  constructor ⟨_,_⟩
  field lock    : Lock
        preempt : Bool   -- preempt_requested: a foreground job is waiting

-- ─── Transitions ────────────────────────────────────────────────────────────────

data LockStep : Coord → Coord → Set where
  -- A foreground job acquires a free lock (its blocking pg_advisory_lock returns).
  -- Acquiring clears the waiter flag.
  fgAcquire : ∀ {p} → LockStep ⟨ Free , p ⟩ ⟨ Held , false ⟩

  -- The daemon acquires a free lock — ONLY when no foreground job is waiting.
  -- This guard (preempt = false in the source) is the structural encoding of
  -- "the daemon does not grab the lock while a foreground job waits".
  bgAcquire : LockStep ⟨ Free , false ⟩ ⟨ Held , false ⟩

  -- A blocked foreground job raises the flag, then blocks on pg_advisory_lock.
  -- It cannot tell who holds the lock, so the flag is raised against any holder;
  -- only the daemon's background task acts on it (a foreground holder ignores it
  -- and the flag is cleared when the waiter acquires).
  fgRequest : LockStep ⟨ Held , false ⟩ ⟨ Held , true ⟩

  -- The holder finishes and releases (pg_advisory_unlock). The daemon's yield is
  -- this same edge, taken because it saw preempt = true.
  release   : ∀ {p} → LockStep ⟨ Held , p ⟩ ⟨ Free , p ⟩

  -- ENVIRONMENT: the owning session dies and the DB frees the lock.
  -- State-identical to `release` — that IS the crash story: abandonment and
  -- release coincide, so there is no recovery state and no takeover logic.
  die       : ∀ {p} → LockStep ⟨ Held , p ⟩ ⟨ Free , p ⟩

-- Reflexive-transitive closure, for reachability statements.
data _↠_ : Coord → Coord → Set where
  done : ∀ {c} → c ↠ c
  _∷_  : ∀ {a b c} → LockStep a b → b ↠ c → a ↠ c
infixr 5 _∷_

-- ─── Safety properties (all structural — refl / absurd) ──────────────────────────
-- Mutual exclusion is by construction: `Coord` has a single `lock` field with
-- one value, so two simultaneous holders are unrepresentable. (No staleness
-- heuristic that could admit a second writer, unlike the heartbeat threshold.)

-- When a foreground job is waiting and the lock is free, the ONLY enabled move is
-- a (foreground) acquire — `bgAcquire`'s preempt = false source guard excludes it,
-- so the daemon cannot grab the lock ahead of the waiter. This is the core of
-- foreground priority: the waiter cannot be jumped.
freeWithWaiterOnlyFg : ∀ {c} → LockStep ⟨ Free , true ⟩ c → c ≡ ⟨ Held , false ⟩
freeWithWaiterOnlyFg fgAcquire = refl

-- No stuck lock: every held state can become free (release; and, unbidden, die).
noStuckLock : ∀ {p} → LockStep ⟨ Held , p ⟩ ⟨ Free , p ⟩
noStuckLock = release

-- The forced handoff path exists: "held, foreground waiting" reaches "held by the
-- foreground" via yield-then-acquire. With freeWithWaiterOnlyFg (no one can jump
-- the waiter) the path is also forced.
handoff : ⟨ Held , true ⟩ ↠ ⟨ Held , false ⟩
handoff = release ∷ fgAcquire ∷ done

-- Crash during the handoff is harmless: die reaches the same waiting-free state,
-- whence only the foreground can acquire.
handoffSurvivesCrash : ⟨ Held , true ⟩ ↠ ⟨ Held , false ⟩
handoffSurvivesCrash = die ∷ fgAcquire ∷ done

-- ─── Trust base for PROGRESS (liveness) ──────────────────────────────────────────
--
-- The lemmas above are SAFETY. PROGRESS — "a waiting foreground job *eventually*
-- acquires" — rests on three guarantees outside this relational model, and a
-- finite Step relation cannot express "eventually" (just as the heartbeat model
-- documented PREEMPT_POLL ≪ HEARTBEAT_PULSE in a comment rather than proving it):
--
--   1. The database frees a session's advisory locks when the session ends
--      (so `die` is real and immediate).
--   2. A dead daemon is restarted by its supervisor (launchd KeepAlive /
--      systemd Restart=on-failure), so the Bg actor reappears.
--   3. The blocking acquire is fair: a queued foreground waiter is scheduled to
--      fire fgAcquire once the lock is free, rather than starving.
