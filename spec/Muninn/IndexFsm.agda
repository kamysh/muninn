{-# OPTIONS --safe #-}
-- Muninn/IndexFsm.agda
-- Proposed indexing state machine with foreground/background lock holders and
-- cooperative preemption.  Supersedes the IndexState / IndexTransition section
-- of Muninn.Index once reconciled (and the matching Rust enum + two new repos
-- columns described under LockState).
--
-- This module is `--safe`: it contains NO postulates.  The abstract facts that
-- genuinely depend on wall-clock time (lock staleness) or on DB rows
-- (indexedAt) are taken as explicit inputs, not assumed.  Foreground priority
-- is PROVEN (foregroundPriority) rather than postulated.
--
-- Motivation (the UX bugs this fixes):
--
--   1. A user-initiated index MUST be interactive (foreground, visible progress).
--      The daemon only does automatic incremental work; it never first-indexes
--      (DaemonNeverFirstIndexes).
--   2. A foreground job MUST take priority over a running background reindex.
--      The daemon, while reindexing, polls a preempt flag every PREEMPT_POLL
--      seconds (≪ the 60 s heartbeat pulse) and YIELDS the lock to a waiting
--      foreground job (bgPollDecision / foregroundPriority), so the user never
--      waits on an unbounded background job.
--   3. Interrupting a foreground index (Ctrl-C) releases the lock immediately
--      (the `interrupt` edge → `released`), so the next command is never blocked
--      by a corpse lock.
--   4. Whether to reindex is decided from DB STATE (indexedAt), never from a
--      byte-diff of the edited config — killing the "No changes" dead-end
--      (configureAction).
module Muninn.IndexFsm where

open import Data.Bool    using (Bool; true; false)
open import Data.Maybe   using (Maybe; nothing; just)
open import Data.Nat     using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Unit    using (⊤; tt)
open import Data.Empty   using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

-- An opaque timestamp.  The FSM only ever inspects presence (just / nothing),
-- never the value; the DB realisation is TIMESTAMPTZ.  Modelled as a unit-like
-- type so the spec stays --safe and carries no irrelevant payload.
record Timestamp : Set where
  constructor now

-- ─── Lock holder kind ─────────────────────────────────────────────────────────
-- Who currently holds the indexing lock.  Foreground = a CLI command the user is
-- actively watching; Background = the daemon.  Only Background yields to a waiter.

data HolderKind : Set where
  Fg : HolderKind   -- foreground (CLI): interactive, NEVER preempted
  Bg : HolderKind   -- background (daemon): yields to a waiting Fg within one poll

-- ─── Lock state ───────────────────────────────────────────────────────────────
-- Extends the bare heartbeat (cf. Muninn.Concurrency.indexingHeartbeat) with the
-- holder kind and a preempt flag.  DB realisation: two new columns on `repos`:
--
--   lock_holder       TEXT     -- 'fg' | 'bg' | NULL   (NULL iff heartbeat NULL)
--   preempt_requested BOOLEAN  -- a foreground waiter has asked Bg to yield

record LockState : Set where
  field heartbeat : Maybe Timestamp    -- mirrors Repo.indexingHeartbeat; NULL = unlocked
        holder    : Maybe HolderKind   -- present iff the lock is held
        preempt   : Bool               -- foreground preemption requested

-- Well-formedness: the holder is present exactly when the lock is held.
HolderWellFormed : LockState → Set
HolderWellFormed ls with LockState.heartbeat ls | LockState.holder ls
... | nothing | nothing = ⊤
... | just _  | just _  = ⊤
... | _       | _       = ⊥

-- The unlocked state produced by every release (finish / fail / interrupt / yield).
released : LockState
released = record { heartbeat = nothing ; holder = nothing ; preempt = false }

-- A foreground waiter raises the preempt flag, then polls for the lock to free.
requestPreempt : LockState → LockState
requestPreempt ls = record ls { preempt = true }

-- ─── Lock acquisition (mirrors Muninn.Concurrency.CanAcquire, kept --safe) ──────
-- The CAS succeeds iff the lock is unlocked OR its heartbeat is stale.  Staleness
-- is a wall-clock fact (heartbeat older than STALE_WINDOW), so it is an INPUT
-- here, computed by the implementation's SQL predicate, not assumed.

canAcquire : (unlocked stale : Bool) → Bool
canAcquire true  _     = true
canAcquire false stale = stale

-- ─── Indexing state machine ─────────────────────────────────────────────────────
-- The transient state of a repo's indexing.  Indexing is parameterised by the
-- holder so the foreground/background distinction is visible in every transition.

data IndexState : Set where
  Unindexed : IndexState               -- indexedAt = nothing (never / interrupted / reset)
  Indexing  : HolderKind → IndexState   -- a (re)index is running; lock held by this holder
  Indexed   : IndexState               -- indexedAt = just _, no active task
  Watching  : IndexState               -- indexed + file-watcher active
  Stale     : IndexState               -- watcher saw changes; reindex owed

-- The outcome of processing a batch of files.  NoneSucceeded is intentionally
-- absent: a totally-failed batch must NOT close the Indexing state.
data BatchOutcome : Set where
  AllSucceeded  : BatchOutcome
  SomeSucceeded : BatchOutcome

-- ─── Transitions ────────────────────────────────────────────────────────────────
-- Encoded as an indexed inductive type so only the permitted edges exist.
-- Every edge INTO Indexing requires canAcquire at the call site (the Fg waiter
-- or the daemon CAS).  Every edge OUT OF Indexing releases the lock (→ released).

data Step : IndexState → IndexState → Set where

  -- Foreground (user-initiated; always interactive).  Lock acquired as Fg.
  cliIndex        : Step Unindexed (Indexing Fg)   -- add (first) or reindex of a reset repo
  cliReindex      : Step Indexed   (Indexing Fg)   -- configure / reindex on a clean repo
  cliReindexStale : Step Stale     (Indexing Fg)   -- configure / reindex after watcher changes

  -- Background (daemon only).  Note there is NO edge from Unindexed: the daemon
  -- never performs a first-time index (DaemonNeverFirstIndexes below).
  bgReindex       : Step Indexed (Indexing Bg)
  bgReindexStale  : Step Stale   (Indexing Bg)

  -- Completion (≥ partial success): lock released, indexedAt := now.
  finish    : ∀ {k} → BatchOutcome → Step (Indexing k) Indexed

  -- Total failure: lock released; no index produced → indexedAt stays nothing.
  fail      : ∀ {k} → Step (Indexing k) Unindexed

  -- Interrupt (Ctrl-C / SIGTERM): FOREGROUND ONLY.  The signal handler clears the
  -- lock and sets indexedAt := nothing; everIndexed is left unchanged, so a
  -- previously-indexed repo is "owed a reindex", not demoted to never-indexed.
  interrupt : Step (Indexing Fg) Unindexed

  -- Preemption: a waiting foreground job raised `preempt`; the Bg holder observes
  -- it on its poll, aborts, and releases the lock.  indexedAt was already nothing
  -- throughout a Bg reindex, so the result is Unindexed — whence the waiter fires
  -- cliIndex to take over.
  yield     : Step (Indexing Bg) Unindexed

  -- Watcher lifecycle.
  attachWatcher : Step Indexed  Watching
  detectChange  : Step Watching Stale

-- ─── Preconditions ──────────────────────────────────────────────────────────────

-- A foreground job may START only when the lock is acquirable (unlocked or stale).
-- If a LIVE lock is held it does not start: it raises `preempt` and waits.
FgStartPre : (unlocked stale : Bool) → Set
FgStartPre u s = canAcquire u s ≡ true

-- The `yield` transition fires only when the lock is held by Bg AND a foreground
-- waiter has requested preemption.
YieldPre : LockState → Set
YieldPre ls = (LockState.holder ls ≡ just Bg) × (LockState.preempt ls ≡ true)

-- ─── Timing constants (seconds) ──────────────────────────────────────────────────
-- Liveness rationale.  PREEMPT_POLL ≪ HEARTBEAT_PULSE bounds how long a
-- foreground job waits for a Bg yield.

HEARTBEAT_PULSE : ℕ
HEARTBEAT_PULSE = 60

STALE_WINDOW : ℕ
STALE_WINDOW = 120   -- 2 × pulse; matches the Concurrency staleness window

PREEMPT_POLL : ℕ
PREEMPT_POLL = 10    -- daemon checks `preempt` this often ⇒ foreground waits ≤ ~10 s

-- ─── The daemon's per-poll decision while holding the lock as Bg ─────────────────
-- Every PREEMPT_POLL seconds the background reindex task wakes, pulses its
-- heartbeat, and checks the preempt flag.  If a foreground job is waiting it
-- yields; otherwise it keeps indexing.

data BgDecision : Set where
  Yield    : BgDecision   -- abort, release the lock to the waiting foreground job
  Continue : BgDecision   -- keep indexing; pulse heartbeat

bgPollDecision : (preemptRequested : Bool) → BgDecision
bgPollDecision true  = Yield
bgPollDecision false = Continue

-- ─── Structural / proven invariants ──────────────────────────────────────────────

-- The daemon never performs a first-time index: there is no background edge out of
-- Unindexed.  Proven by absurdity — no constructor inhabits this type.
DaemonNeverFirstIndexes : ¬ Step Unindexed (Indexing Bg)
DaemonNeverFirstIndexes ()

-- Foreground priority (PROVEN, not postulated): whenever a foreground job is
-- waiting, the background holder's poll decision is necessarily Yield.  Together
-- with the bound PREEMPT_POLL this guarantees the foreground job waits at most one
-- poll interval before the lock is released to it.
foregroundPriority : ∀ {b} → b ≡ true → bgPollDecision b ≡ Yield
foregroundPriority refl = refl

-- ─── Reindex decision (state-driven, not content-diff-driven) ─────────────────────
-- A repo's index is "owed" iff indexedAt is nothing (never / interrupted / reset /
-- stale-after-watcher).

NeedsReindex : (indexedAt : Maybe Timestamp) → Set
NeedsReindex (just _) = ⊥   -- clean: nothing owed
NeedsReindex nothing  = ⊤   -- (re)index owed

-- What `muninn configure` does on save.  The ONLY case that skips a reindex is a
-- clean index with an unchanged config; everything else reindexes in the
-- foreground.  This removes the "No changes" dead-end where a saved exclude list
-- was never applied to a stale index.
data ConfigureAction : Set where
  ReindexFg   : ConfigureAction   -- run a foreground reindex
  ReportClean : ConfigureAction   -- "index up to date; nothing to do"

configureAction : (contentChanged : Bool) → (indexedAt : Maybe Timestamp) → ConfigureAction
configureAction true  _        = ReindexFg
configureAction false (just _) = ReportClean
configureAction false nothing  = ReindexFg

-- A sanity lemma: configure never reports "clean" while a reindex is owed.
configureNeverSkipsOwed : ∀ {c} → configureAction c nothing ≡ ReindexFg
configureNeverSkipsOwed {true}  = refl
configureNeverSkipsOwed {false} = refl
