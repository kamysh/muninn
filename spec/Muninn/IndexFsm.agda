{-# OPTIONS --safe #-}
-- Muninn/IndexFsm.agda
-- The index lifecycle state machine and the configure decision. The lock/liveness
-- mechanism lives in Muninn.AdvisoryLock (the session-scoped advisory lock); this
-- module imports HolderKind from there to parameterise the Indexing state.
--
-- Properties this module pins down (--safe, postulate-free):
--   * DaemonNeverFirstIndexes — the daemon never performs a first-time index.
--   * foregroundPriority — a foreground waiter forces the daemon's poll to Yield.
--   * configureNeverSkipsOwed — `configure` decides from DB state (indexedAt),
--     never from the config byte-diff, so a saved exclude list always reaches a
--     stale index.
module Muninn.IndexFsm where

open import Muninn.AdvisoryLock using (HolderKind; Fg; Bg)
open import Muninn.Types using (EmbeddingState; Embedded; Pending; Absent)
open import Data.Bool   using (Bool; true; false)
open import Data.Maybe  using (Maybe; nothing; just)
open import Data.Nat    using (ℕ)
open import Data.Unit   using (⊤; tt)
open import Data.Empty  using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

-- ─── Indexing state machine ─────────────────────────────────────────────────────
-- The transient state of a repo's indexing. Indexing is parameterised by the
-- holder so the foreground/background distinction is visible in every transition.
-- The holder is the *task* identity (Muninn.AdvisoryLock.HolderKind), NOT a
-- property of the advisory lock (which records no holder). The implementation
-- mirrors this: core/src/types.rs IndexState::Indexing carries a HolderKind, and
-- the daemon watcher constructs Indexing(Bg) (indexer/src/watcher.rs).

data IndexState : Set where
  Unindexed : IndexState               -- indexedAt = nothing (never / interrupted / reset)
  Indexing  : HolderKind → IndexState   -- a (re)index is running; lock held by this holder
  Indexed   : IndexState               -- indexedAt = just _, no active task
  Watching  : IndexState               -- indexed + file-watcher active
  Stale     : IndexState               -- watcher saw changes; reindex owed

-- The outcome of processing a batch of files. NoneSucceeded is intentionally
-- absent: a totally-failed batch must NOT close the Indexing state.
data BatchOutcome : Set where
  AllSucceeded  : BatchOutcome
  SomeSucceeded : BatchOutcome

-- ─── Transitions ────────────────────────────────────────────────────────────────
-- Encoded as an indexed inductive type so only the permitted edges exist. Every
-- edge INTO Indexing requires the advisory lock to be free at the call site (the
-- foreground blocking-acquire or the daemon try-acquire). Every edge OUT OF
-- Indexing releases the lock.

data Step : IndexState → IndexState → Set where

  -- Foreground (user-initiated; always interactive). Lock acquired as Fg.
  cliIndex        : Step Unindexed (Indexing Fg)   -- add (first) or reindex of a reset repo
  cliReindex      : Step Indexed   (Indexing Fg)   -- configure / reindex on a clean repo
  cliReindexStale : Step Stale     (Indexing Fg)   -- configure / reindex after watcher changes

  -- Background (daemon only). NO edge from Unindexed — the daemon never performs a
  -- first-time index (DaemonNeverFirstIndexes below).
  bgReindex       : Step Indexed (Indexing Bg)
  bgReindexStale  : Step Stale   (Indexing Bg)

  -- Completion (≥ partial success): lock released, indexedAt := now.
  finish    : ∀ {k} → BatchOutcome → Step (Indexing k) Indexed

  -- Total failure: lock released; no index produced → indexedAt stays nothing.
  fail      : ∀ {k} → Step (Indexing k) Unindexed

  -- Interrupt (Ctrl-C): FOREGROUND ONLY. The index sets indexedAt := nothing at
  -- the start, so any interruption (or crash, via the lock auto-release) leaves
  -- the repo owed a reindex. everIndexed is unchanged.
  interrupt : Step (Indexing Fg) Unindexed

  -- The daemon yields to a waiting foreground job (it unlocked the advisory lock).
  -- indexedAt was already nothing during a Bg reindex, so the result is Unindexed.
  yield     : Step (Indexing Bg) Unindexed

  -- Watcher lifecycle.
  attachWatcher : Step Indexed  Watching
  detectChange  : Step Watching Stale

-- ─── The daemon's per-poll decision while holding the lock as Bg ─────────────────
-- Every PREEMPT_POLL seconds the background reindex task checks the preempt flag.
-- If a foreground job is waiting it yields (unlocks); otherwise it keeps indexing.

PREEMPT_POLL : ℕ
PREEMPT_POLL = 10   -- seconds; bounds how long a foreground job waits for a yield

data BgDecision : Set where
  Yield    : BgDecision   -- abort, unlock, hand the lock to the waiting foreground job
  Continue : BgDecision   -- keep indexing

bgPollDecision : (preemptRequested : Bool) → BgDecision
bgPollDecision true  = Yield
bgPollDecision false = Continue

-- ─── Structural / proven invariants ──────────────────────────────────────────────

-- The daemon never performs a first-time index: there is no background edge out of
-- Unindexed. Proven by absurdity — no constructor inhabits this type.
DaemonNeverFirstIndexes : ¬ Step Unindexed (Indexing Bg)
DaemonNeverFirstIndexes ()

-- Foreground priority (PROVEN): whenever a foreground job is waiting, the
-- background holder's poll decision is necessarily Yield. With PREEMPT_POLL this
-- bounds the foreground wait to one poll interval.
foregroundPriority : ∀ {b} → b ≡ true → bgPollDecision b ≡ Yield
foregroundPriority refl = refl

-- ─── Reindex decision (state-driven, not content-diff-driven) ─────────────────────
-- A repo's index is "owed" iff indexedAt is nothing (never / interrupted / reset /
-- stale-after-watcher). Abstract over the timestamp type: only presence matters.

NeedsReindex : ∀ {A : Set} → Maybe A → Set
NeedsReindex (just _) = ⊥   -- clean: nothing owed
NeedsReindex nothing  = ⊤   -- (re)index owed

-- What `muninn configure` does on save. The ONLY case that skips a reindex is a
-- clean index with an unchanged config; everything else reindexes in the
-- foreground. Removes the "No changes" dead-end where a saved exclude list was
-- never applied to a stale index.
data ConfigureAction : Set where
  ReindexFg   : ConfigureAction   -- run a foreground reindex
  ReportClean : ConfigureAction   -- "index up to date; nothing to do"

configureAction : ∀ {A : Set} → (contentChanged : Bool) → Maybe A → ConfigureAction
configureAction true  _        = ReindexFg
configureAction false (just _) = ReportClean
configureAction false nothing  = ReindexFg

-- configure never reports "clean" while a reindex is owed.
configureNeverSkipsOwed : ∀ {A : Set} {c} → configureAction {A} c nothing ≡ ReindexFg
configureNeverSkipsOwed {c = true}  = refl
configureNeverSkipsOwed {c = false} = refl

-- ─── Chunk-level embedding backfill (daemon, Bg) ──────────────────────────────
-- Distinct from the repo-level IndexState FSM above: this is the per-chunk
-- embedding lifecycle. The foreground indexer leaves a Tier-2 chunk Pending
-- (full-text indexed, no vector); the always-present daemon (Bg) embeds it later.
-- The ONLY transition is Pending → Embedded: backfill never touches an already
-- Embedded or Absent chunk, and (not modelled as state here) never changes the
-- chunk's tier or content. Tier-1 chunks are embedded eagerly and so never enter
-- this relation (see Muninn.Types.Tier1NeverPending).
data EmbedStep : EmbeddingState → EmbeddingState → Set where
  backfill : EmbedStep Pending Embedded

-- Backfill only advances out of Pending: there is no step from Embedded/Absent.
backfillOnlyFromPending : ¬ EmbedStep Embedded Embedded
backfillOnlyFromPending ()
