# Tiered Indexing — Design

**Status:** approved design (spec-first implementation to follow)
**Date:** 2026-06-28

## Problem

On large repos (e.g. yovico) muninn has two failure modes:

1. **Indexing takes too long.** Every file is parsed, chunked, and *embedded*
   (the network/compute-dominant step). Vendored dependency trees
   (`node_modules`, `vendor`, `.venv`, …) are huge and embedding them dominates
   wall-clock — the user waits minutes on `muninn add`.
2. **Search is noisy.** Vendored code is indexed with equal weight to
   first-party source, so it floods and outranks real results. Documented
   defect: searching `buildRoundRobinSummary` returned `node_modules/typescript`
   chunks at uniform ~0.016 scores and missed the actual source file.

The two existing tools are insufficient: `exclude` is all-or-nothing. Excluding
`node_modules` makes search fast+quiet but loses the ability to search
dependency code (rejected — vendored code is often worth searching). Indexing it
keeps it searchable but is slow and noisy. Tiering is the missing third option:
**keep vendored code searchable but stop it from dominating, and move its
expensive embedding off the user's critical path.**

## Two axes

Indexing classifies every file into one of three outcomes:

```
all files in repo
   │
   ├─ exclude globs ──► DROP        (never indexed, not searchable)
   │
   └─ survivors of exclude
         │
         ├─ vendor globs ──► TIER 2 (indexed, down-weighted, lazily embedded)
         │
         └─ the rest     ──► TIER 1 (first-party, full weight, eager embed)
```

- **`exclude` = drop.** Applied first; **wins on overlap** (a path matching both
  `exclude` and `vendor` is dropped).
- **`vendor` = down-weight, not drop.** Classifies what survives `exclude`.
- **Unmatched survivors = Tier 1.**

Migration framing for the historical pain: move `node_modules`-class entries
**out of `exclude` and into `vendor`** — searchable but quiet.

## Glob resolution (unified for both axes)

Both `exclude` and `vendor` resolve identically:

```
effective patterns = shipped_defaults ++ global_config ++ repo_config
matched left-to-right against a path, LAST MATCH WINS, `!pattern` negates.
```

This **supersedes** the whole-list-REPLACE `exclude` merge semantics introduced
in spec-reconcile commit `d6d7c8a`. The replace rule had a real wart (recorded
for yovico: adding one repo-local pattern required copying the entire global
list). The layered fold fixes it: a repo writes only its delta and inherits the
rest; `!pattern` lets a repo *remove* a default or an inherited entry (e.g.
`!target/` to reclaim a Rust build dir as Tier 1). This is a deliberate,
spec-first revision of the just-shipped `exclude` contract.

The matching engine already exists: `build_excludes` in `pipeline.rs` feeds
patterns to `ignore::overrides::OverrideBuilder`, which *is* a last-match-wins,
`!`-negation matcher. The change is what we feed it (defaults ++ global ++ repo,
per axis) and adding a second axis (vendor).

### Shipped defaults (starting point — refine during implementation)

**`exclude` (drop — degenerate / generated junk):**
`.git/`, `**/*.min.js`, `**/*.min.css`, `**/*.map`, `**/*.snap`, and lockfiles
(`package-lock.json`, `yarn.lock`, `pnpm-lock.yaml`, `Cargo.lock`,
`poetry.lock`, `Gemfile.lock`, `composer.lock`).

**`vendor` (down-weight — real code, rarely wanted first):**
`**/node_modules/**`, `**/vendor/**`, `vendor/`, `**/.venv/**`, `**/venv/**`,
`**/site-packages/**`, `**/target/**`, `**/dist/**`, `**/build/**`,
`**/.tox/**`, `**/__pycache__/**`.

Generated-but-occasionally-useful dirs (`dist`, `build`, `target`) go in
`vendor`, not `exclude`, so they stay findable-but-quiet; a repo can `!`-reclaim
or drop them as needed.

## Noise fix — search-side (in `rrf_merge`)

Tier affects ranking only; retrieval is unchanged. Two complementary mechanisms,
both with **fixed code constants (no config knobs)** like the existing `K = 60`
and `MAX_LIMIT = 1000`:

1. **Down-weight:** a Tier-2 chunk's fused RRF score is multiplied by
   `vendorWeight` (≈ 0.3) before the final sort. A vendor chunk must match much
   better than a first-party chunk to outrank it, but a genuinely strong vendor
   match (with nothing first-party competing) still surfaces.
2. **Per-file cap:** at most `perFileCap` (≈ 3) chunks from any single file in
   the merged result. Directly defeats the "one vendor file floods the top-10"
   mode; also improves Tier-1 diversity as a bonus.

**Vendor stays reachable** — down-weighted and capped, never filtered out. There
is no "Tier-1-only" mode.

## Time fix — index-side

**Assumption (stated invariant):** `muninn-index` is always present. Tier-2
embedding is unconditionally the daemon's job; there is no
CLI-finishes-it-itself fallback.

- **CLI `add`/`reindex` (foreground, `Fg` lock):**
  - Tier 1: parse + chunk + **embed** + full-text → `embedding_state = embedded`.
  - Tier 2: parse + chunk + full-text, **no embed** → `embedding_state =
    pending`, `content_hash` set.
  - mark indexed; return. **The user waits only for Tier 1.**
- **`muninn-index` daemon (background, `Bg` lock):** drains the Tier-2 backlog
  (`WHERE embedding_state = 'pending'`, via a partial index), **deduplicating by
  `content_hash`** — embed each unique content once, fan the vector to all
  duplicate chunks — then flips `pending → embedded`.
- **Self-healing search:** a Tier-2 chunk is full-text-searchable immediately
  and becomes semantic-searchable once the daemon embeds it.

### Deferral model: backfill (push), not on-demand (pull)

We chose **daemon backfill**: the daemon proactively embeds all Tier-2 chunks in
the background. We explicitly **rejected on-demand-at-search-time** because it
cannot be implemented cleanly:

- Tier-2 chunks without embeddings are invisible to a vector query (no vector to
  compare against), so the search path cannot discover which vendor chunks
  *would* match in order to lazily embed them.
- Every workaround either re-introduces bulk embedding into a (blocking) search
  call, pushes indexing work + failure modes into the read path, or collapses
  back into "the daemon backfills it anyway."

Backfill keeps **`muninn-mcp` a pure reader** — no embedder, no write path, no
per-query indexing.

## `muninn-mcp` search path (what actually changes)

Retrieval is essentially unchanged; only fusion becomes tier-aware:

- `fulltext_search`: returns Tier 1 **and** Tier 2 (tsvectors exist from
  Phase 1, before embedding).
- `semantic_search`: returns only `embedding_state = 'embedded'` chunks
  (pending/absent have no vector — the existing `WHERE embedding IS NOT NULL`
  already handles this; pending naturally degrades to full-text-only).
- `rrf_merge`: fuse → multiply Tier-2 scores by `vendorWeight` → sort → apply
  `perFileCap` → truncate to `limit`.

Before/after for the recorded yovico bug: the real Go file (Tier 1, full weight)
rises; the `typescript` chunks (Tier 2, ×0.3, and per-file capped) are throttled
but a vendor-only symbol is still findable.

## Schema

The per-repo chunk table (`chunks_<uuid>`, created by `register_repo` in
`store.rs` — **not** the static migration chain) gains:

```sql
tier            SMALLINT NOT NULL DEFAULT 1,   -- 1 = first-party, 2 = vendor
embedding_state TEXT NOT NULL DEFAULT 'embedded'
                CHECK (embedding_state IN ('embedded','pending','absent')),
content_hash    BYTEA                          -- sha256(content), for dedup
-- plus a partial index: (embedding_state) WHERE embedding_state = 'pending'
```

- `tier` is set at index time (single source of truth; not recomputed at search
  time). Default 1 is safe for any path.
- `embedding_state` keeps three states distinct: `pending` (Tier-2 awaiting
  backfill), `embedded` (has a vector), `absent` (embedder genuinely returned
  empty — the existing warn-and-store path). This avoids overloading
  `embedding IS NULL` to mean two different things.
- `content_hash` groups identical Tier-2 chunks for dedup. It is computed for
  **all** chunks at index time (cheap, uniform — no writer-side conditional) but
  **only used** by the Tier-2 backfill dedup path in v1; computing it for Tier 1
  too leaves the door open to Tier-1 dedup later with no schema change.

### Rollout to existing repos

- **New repos:** columns added to the `CREATE TABLE IF NOT EXISTS` template in
  `register_repo`.
- **Existing repos:** brought up to shape via idempotent
  `ALTER TABLE "<chunks_uuid>" ADD COLUMN IF NOT EXISTS …` in the same
  store.rs ensure-table path (mirrors the existing idempotent
  `CREATE TABLE/INDEX IF NOT EXISTS` pattern). **Not** a `DO $$` loop migration —
  per-repo tables are deliberately kept out of the static migration chain
  (migration 002's design note).
- **Tiering takes effect on `reindex`.** Until a repo is reindexed it stays
  all-Tier-1 (`tier` default 1, everything `embedded`) — i.e. current behavior.
  Graceful, no-surprise upgrade.

Any `repos`-level migration (if needed at all) is a *new* `#!migration` block,
never an edit to an existing one (migrations are append-only).

## Spec changes (spec-first; `agda --safe` before any Rust)

Extend the existing modules — no new top-level module.

1. **`Muninn/Config.agda`** — replace the `effective`-based `exclude` merge with
   a shared **ordered-fold-with-negation** resolution used by both `exclude` and
   the new `vendor : List String`; model shipped defaults as named constants;
   model resolution as `defaults ++ global ++ repo`, last-match-wins, `!`
   negates; model composition precedence as
   `classify : Path → {Drop, Tier1, Tier2}` with `Drop` shadowing `Tier2`.
2. **`Muninn/Types.agda`** — `Tier = Tier1 | Tier2` on `Chunk`;
   `EmbeddingState = Embedded | Pending | Absent` on `Chunk`; invariant **Tier-1
   chunks are never Pending** (only Tier 2 defers).
3. **`Muninn/Search.agda`** — constants `vendorWeight : Float`,
   `perFileCap : ℕ`; `tieredScore`; a per-file-cap result-bound lemma
   (analogous to the existing length bound); a **reachability** statement that
   Tier-2 chunks are down-weighted, not filtered.
4. **`Muninn/IndexFsm.agda` / `Index.agda`** — foreground index produces Tier-2
   chunks in `Pending`; a daemon **backfill** step `Pending → Embedded`
   (holder `Bg`) that never touches Tier 1, content, or tier.

## Component boundaries (each independently testable)

- **`classify`** — pure, config-driven (defaults + globs + negation +
  precedence). Unit + property tests in isolation.
- **Foreground indexer** — writes `tier` + `embedding_state`; upholds
  "Tier-1 never Pending".
- **Daemon backfill** — drains `pending → embedded`, dedup by `content_hash`;
  testable: backlog drains, duplicates share a vector, Tier-1 untouched.
- **`rrf_merge` tiering** — down-weight + cap; property tests (existing RRF
  harness extends naturally).

## Scope

**In v1:** two-axis classify (exclude/vendor) with layered-fold-with-negation
resolution + shipped defaults; schema (tier / embedding_state / content_hash);
foreground Tier-1-eager / Tier-2-pending split; daemon backfill with
content-hash dedup; tier-aware `rrf_merge` (down-weight + per-file cap).

**Deferred:** canonical-form / degenerate-content collapse (mostly covered by
`exclude` defaults — min.js/maps/lockfiles); on-demand-at-search embedding
(rejected — cannot be implemented cleanly); config knobs for `vendorWeight` /
`perFileCap` (fixed code constants for now).
