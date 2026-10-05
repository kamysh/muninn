{-# OPTIONS --safe #-}
-- Proposed lifecycle: explicit first family start, automatic linked worktrees,
-- application/AGE pair readiness, and snapshot retention during Git operations.
module Muninn.IndexFsm where

open import Muninn.AdvisoryLock using (HolderKind; Fg; Bg)
open import Muninn.Types using (EmbeddingState; Embedded; Pending; Absent)
open import Muninn.Schema using (SchemaState; Missing; Migrating; Ready)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

data GitState : Set where
  Settled : GitState -- ordinary uncommitted edits are allowed
  Operating : GitState -- merge/rebase in progress, including a paused operation
  Conflicted : GitState -- unresolved index conflicts, even without operation metadata

data GitBlocked : GitState → Set where
  operationBlocked : GitBlocked Operating
  conflictBlocked : GitBlocked Conflicted

data IndexState : Set where
  Unindexed : IndexState
  Indexing : HolderKind → IndexState
  Indexed Watching Stale : IndexState

data BatchOutcome : Set where
  AllSucceeded SomeSucceeded : BatchOutcome

-- Source and destination family-start flags are explicit. Only a CLI start
-- can change false to true. Background indexing of any worktree requires true.
-- The pair's readiness and Git state are observations rechecked during work.
-- SchemaStep supplies the migration/AGE receipt contract for a Ready report;
-- this job FSM consumes that report, not the physical database catalog.
data Step : Bool → SchemaState → GitState → IndexState → Bool → IndexState → Set where
  cliIndex : ∀ {started} → Step started Ready Settled Unindexed true (Indexing Fg)
  cliReindex : Step true Ready Settled Indexed true (Indexing Fg)
  cliReindexStale : Step true Ready Settled Stale true (Indexing Fg)
  autoDiscovered : Step true Ready Settled Unindexed true (Indexing Bg)
  bgReindex : Step true Ready Settled Indexed true (Indexing Bg)
  bgReindexStale : Step true Ready Settled Stale true (Indexing Bg)
  finish : ∀ {k} → BatchOutcome → Step true Ready Settled (Indexing k) true Indexed
  fail : ∀ {s g k} → Step true s g (Indexing k) true Stale
  interrupt : ∀ {s g} → Step true s g (Indexing Fg) true Stale
  yield : ∀ {s g} → Step true s g (Indexing Bg) true Stale
  suspend : ∀ {s g k} → GitBlocked g → Step true s g (Indexing k) true Stale
  attachWatcher : Step true Ready Settled Indexed true Watching
  detectChange : ∀ {g} → Step true Ready g Watching true Stale

noAutoBeforeFamilyStart : ∀ s g before after →
  ¬ Step false s g before after (Indexing Bg)
noAutoBeforeFamilyStart s g before after ()

blockedCannotStart : ∀ {b s g before after k} → GitBlocked g →
  ¬ Step b s g before after (Indexing k)
blockedCannotStart () cliIndex
blockedCannotStart () cliReindex
blockedCannotStart () cliReindexStale
blockedCannotStart () autoDiscovered
blockedCannotStart () bgReindex
blockedCannotStart () bgReindexStale

indexingRequiresReadySchema : ∀ {b s g before after k} →
  Step b s g before after (Indexing k) → s ≡ Ready
indexingRequiresReadySchema cliIndex = refl
indexingRequiresReadySchema cliReindex = refl
indexingRequiresReadySchema cliReindexStale = refl
indexingRequiresReadySchema autoDiscovered = refl
indexingRequiresReadySchema bgReindex = refl
indexingRequiresReadySchema bgReindexStale = refl

-- Publication is separate from job state: failure, suspension, and retries
-- keep the entire last snapshot (including graph), even when no snapshot exists.
chooseSnapshot : ∀ {A : Set} → GitState → Maybe A → Maybe A → Maybe A
chooseSnapshot Operating previous candidate = previous
chooseSnapshot Conflicted previous candidate = previous
chooseSnapshot Settled previous nothing = previous
chooseSnapshot Settled previous (just candidate) = just candidate

blockedRetainsSnapshot : ∀ {A : Set} g (previous candidate : Maybe A) →
  GitBlocked g → chooseSnapshot g previous candidate ≡ previous
blockedRetainsSnapshot .Operating previous candidate operationBlocked = refl
blockedRetainsSnapshot .Conflicted previous candidate conflictBlocked = refl

data SnapshotStatus : Set where
  Current CatchingUp Pending SuspendedStale SuspendedPending : SnapshotStatus

snapshotStatus : ∀ {A : Set} → GitState → Maybe A → (current : Bool) → SnapshotStatus
snapshotStatus Operating nothing _ = SuspendedPending
snapshotStatus Operating (just _) _ = SuspendedStale
snapshotStatus Conflicted nothing _ = SuspendedPending
snapshotStatus Conflicted (just _) _ = SuspendedStale
snapshotStatus Settled nothing _ = Pending
snapshotStatus Settled (just _) false = CatchingUp
snapshotStatus Settled (just _) true = Current

blockedSnapshotIsExplicitlyStale : ∀ {A : Set} g (snapshot : A) current →
  GitBlocked g → snapshotStatus g (just snapshot) current ≡ SuspendedStale
blockedSnapshotIsExplicitlyStale Operating snapshot current operationBlocked = refl
blockedSnapshotIsExplicitlyStale Conflicted snapshot current conflictBlocked = refl

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

-- Saving policy on a family that has never started does not start indexing.
-- Once started, a changed policy or stale view requests the existing foreground
-- reindex behavior. Automatic first indexing applies only to linked worktrees.
data ConfigureAction : Set where
  WaitForStart : ConfigureAction
  ReindexFg : ConfigureAction
  ReportClean : ConfigureAction   -- "index up to date; nothing to do"

configureAction : ∀ {A : Set} → (familyStarted contentChanged : Bool) → Maybe A → ConfigureAction
configureAction false _ _ = WaitForStart
configureAction true true _ = ReindexFg
configureAction true false (just _) = ReportClean
configureAction true false nothing = ReindexFg

configureNeverStartsFamily : ∀ {A : Set} {c} {at : Maybe A} →
  configureAction false c at ≡ WaitForStart
configureNeverStartsFamily = refl

configureNeverSkipsOwed : ∀ {A : Set} {c} →
  configureAction {A} true c nothing ≡ ReindexFg
configureNeverSkipsOwed {c = true} = refl
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
