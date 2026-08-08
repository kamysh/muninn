# Tiered Indexing Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Index vendored code (node_modules, vendor, .venv, …) as a down-weighted, lazily-embedded second tier so large repos index fast and search isn't drowned by dependency noise — while keeping vendor code searchable.

**Architecture:** Two glob axes resolved by one layered-fold-with-negation function (`exclude`=drop, `vendor`=Tier 2; unmatched=Tier 1). The foreground CLI eagerly embeds Tier 1 and writes Tier 2 as full-text-only `pending`; the always-present `muninn-index` daemon backfills Tier-2 embeddings in the background, deduplicating by content hash. `rrf_merge` down-weights Tier-2 scores and caps results per file.

**Tech Stack:** Rust (tokio-postgres, pgvector, the `ignore` crate's `OverrideBuilder`), PostgreSQL (per-repo `chunks_<uuid>` tables), Agda (`spec/Muninn/*.agda`).

## Global Constraints

- **Spec-first, hard gate:** No implementation line may exist without a governing Agda spec description FIRST. Each phase edits `spec/Muninn/*.agda` and `agda --safe` exits 0 BEFORE any Rust in that phase.
- **Agda check:** `cd spec && nix develop --command agda --safe Muninn.agda` → exit 0. Capture the bare exit code (no piping through filters that discard it).
- **Rust gates (workspace root, via `nix develop --command bash -c "cd <repo> && …"`):** `cargo build` exit 0; `cargo clippy --all-targets -- -D warnings` exit 0; `cargo fmt --all -- --check` exit 0; `cargo nextest run` (or `cargo test`) exit 0. All five gates green before a phase's final commit.
- **Migrations are append-only.** Per-repo `chunks_<uuid>` tables are managed by `store.rs` (idempotent `CREATE/ALTER … IF NOT EXISTS`), NOT the static migration chain. Any `repos`-level migration is a NEW `#!migration` block, never an edit to an existing file.
- **No `Co-Authored-By: Claude` trailers** in commits.
- **No config knobs in v1:** `vendorWeight` and `perFileCap` are fixed code constants.
- All commands run inside the Nix dev shell. `cargo fmt` must run from the repo root (`cd` inside the nix command) or it fails "Failed to find targets".

---

## File Structure

| File | Responsibility | Phase |
|------|----------------|-------|
| `spec/Muninn/Config.agda` | `vendor` field, shared layered-fold-with-negation resolution, `classify` precedence | 1 |
| `spec/Muninn/Types.agda` | `Tier`, `EmbeddingState` on `Chunk`; Tier1-never-Pending invariant | 1 |
| `spec/Muninn/Search.agda` | `vendorWeight`, `perFileCap`, `tieredScore`, per-file-cap bound, reachability | 1 |
| `spec/Muninn/IndexFsm.agda` | foreground produces Tier-2 `Pending`; daemon backfill `Pending → Embedded` | 1 |
| `crates/core/src/config.rs` | `IndexConfig.vendor`, shipped defaults, fold resolution, `classify` | 2, 3 |
| `crates/core/src/types.rs` | `Tier`, `EmbeddingState` enums; `Chunk` gains `tier`/`embedding_state`/`content_hash` | 2 |
| `crates/core/src/store.rs` | chunk-table DDL (new cols + partial index), idempotent `ADD COLUMN IF NOT EXISTS`, `upsert_chunk` cols, pending-backlog queries | 2, 5 |
| `crates/core/src/parser.rs` | the two `Chunk { … }` constructors gain new fields | 2 |
| `crates/core/src/pipeline.rs` | `classify` per file; Tier-1 eager embed / Tier-2 pending split; set `content_hash` | 3, 4 |
| `crates/core/src/search.rs` | SELECT + row-map `tier`; tier-aware `rrf_merge` (weight + cap) | 6 |
| `crates/indexer/src/main.rs` | daemon drains pending backlog | 5 |
| `crates/indexer/src/backfill.rs` (new) | backfill task: group pending by `content_hash`, embed once, fan out | 5 |

---

## Phase / Task Overview

1. **Spec** — extend all four Agda modules; `agda --safe` green. (No Rust.)
2. **Schema + types** — `Tier`/`EmbeddingState`/`content_hash` on `Chunk`; chunk-table columns + partial index; idempotent column-add; thread fields through all constructors and `upsert_chunk`.
3. **Classify** — `IndexConfig.vendor`, shipped defaults, layered-fold-with-negation resolver, `classify(path) → Decision`.
4. **Foreground split** — pipeline classifies per file; Tier 1 eager-embed; Tier 2 chunked + full-text only, `pending`, `content_hash` set.
5. **Daemon backfill** — drain `pending`, dedup by `content_hash`, embed once, flip to `embedded`.
6. **Tier-aware search** — SELECT/map `tier`; `rrf_merge` down-weight + per-file cap.
7. **Tests** — quickcheck + integration across the above (folded into each phase; this phase adds cross-cutting integration coverage).

---

## Task 1: Agda spec extensions

**Files:**
- Modify: `spec/Muninn/Config.agda`
- Modify: `spec/Muninn/Types.agda`
- Modify: `spec/Muninn/Search.agda`
- Modify: `spec/Muninn/IndexFsm.agda`

**Interfaces:**
- Produces (consumed by all later Rust tasks as the governing contract):
  - `Tier = Tier1 | Tier2`; `EmbeddingState = Embedded | Pending | Absent` on `Chunk`.
  - `IndexConfig` gains `vendor : List String`.
  - resolution `resolveAxis : List String → List String → List String → (String → Bool)` (defaults, global, repo) — last-match-wins with `!` negation.
  - `classify : (excludeMatch vendorMatch : Bool) → Decision` where `Decision = Drop | T1 | T2`, `Drop` shadows `T2`.
  - `vendorWeight : Float`, `perFileCap : ℕ`.

- [ ] **Step 1: `Types.agda` — add Tier and EmbeddingState to Chunk**

Read the current `Chunk` record first. Add two data types above it and two fields to it:

```agda
data Tier : Set where
  Tier1 : Tier   -- first-party source; full weight; eager embed
  Tier2 : Tier   -- vendored dependency; down-weighted; lazily embedded

data EmbeddingState : Set where
  Embedded : EmbeddingState   -- vector present
  Pending  : EmbeddingState   -- Tier-2 chunk awaiting daemon backfill
  Absent   : EmbeddingState   -- embedder returned empty (existing warn-path)
```

Add to the `Chunk` record fields:
```agda
        tier           : Tier
        embeddingState : EmbeddingState
```
(The `content_hash` is an impl-level dedup detail, not a spec invariant — do NOT add it to the spec `Chunk`.)

- [ ] **Step 2: `Types.agda` — Tier-1-never-Pending invariant**

```agda
-- A Tier-1 chunk is always eagerly embedded; only Tier 2 defers.
Tier1NeverPending : Chunk → Set
Tier1NeverPending c = Chunk.tier c ≡ Tier1 → Chunk.embeddingState c ≢ Pending
```
(Import `_≢_` if not already imported.)

- [ ] **Step 3: `Config.agda` — vendor field + shared resolution + classify**

Add `vendor : List String` to `IndexConfig` (next to `exclude`). Replace the `effective`-based `exclude` merge clause in `merge` (the one from commit `d6d7c8a`) with a shared fold. Model the resolution and classification:

```agda
-- A pattern is a glob; a leading '!' negates (removes a prior match).
-- Resolution concatenates defaults ++ global ++ repo and matches last-wins.
-- Modelled abstractly: matchAxis returns whether a path is in the axis set.
postulate
  globMatch : String → String → Bool   -- (pattern, path) ; engine = ignore crate

-- last-match-wins fold over an ordered pattern list (defaults++global++repo).
-- '!p' (negation) un-sets; bare 'p' sets. Returned: final membership for path.
resolveAxis : List String → String → Bool
-- (definition: left fold, each matching pattern overrides the running Bool;
--  a "!"-prefixed pattern that matches sets False, otherwise True.)

data Decision : Set where
  Drop : Decision   -- excluded
  T1   : Decision   -- first-party
  T2   : Decision   -- vendor

-- exclude wins over vendor; unmatched = Tier 1.
classify : (excluded vendored : Bool) → Decision
classify true  _     = Drop
classify false true  = T2
classify false false = T1
```

Keep the shipped-default lists as named constants:
```agda
excludeDefaults : List String   -- .git/, **/*.min.js, lockfiles, …
vendorDefaults  : List String   -- **/node_modules/**, **/vendor/**, …
```
(List the same entries as the design doc; the exact glob strings are the engine's concern but record them so spec and impl agree.)

- [ ] **Step 4: `Search.agda` — constants, tieredScore, bounds, reachability**

```agda
vendorWeight : Float
vendorWeight = ...   -- 0.3 (use the Float constructor already in Muninn.Float)

perFileCap : ℕ
perFileCap = 3

-- Tier-2 fused scores are scaled down before the final sort.
tieredScore : Tier → Float → Float
tieredScore Tier1 s = s
tieredScore Tier2 s = s *F vendorWeight

-- Per-file cap: no single file contributes more than perFileCap chunks.
-- (State as a property over the merged result, analogous to HybridResultBound.)
PerFileBound : List SearchResult → Set
-- ∀ file, count of results from that file ≤ perFileCap

-- Reachability: Tier-2 results are down-weighted, NOT filtered out.
-- (State that a Tier-2 chunk with a positive score can appear in the result.)
```

- [ ] **Step 5: `IndexFsm.agda` — Tier-2 pending + daemon backfill transition**

The chunk-level embedding lifecycle (this is NOT the repo IndexState FSM):
```agda
-- Foreground indexing leaves a Tier-2 chunk Pending; the daemon backfills it.
data EmbedStep : EmbeddingState → EmbeddingState → Set where
  backfill : EmbedStep Pending Embedded   -- daemon (Bg) embeds a pending chunk

-- Backfill only ever advances Pending → Embedded; it never touches an
-- already-Embedded/Absent chunk, never changes tier or content.
```
(Place near the existing `Step` relation; reuse the `Bg` holder note.)

- [ ] **Step 6: Type-check the spec**

Run: `cd /home/kamysh/Work/balovstvo/muninn/spec && nix develop --command agda --safe Muninn.agda >/dev/null 2>&1; echo "AGDA_EXIT: $?"`
Expected: `AGDA_EXIT: 0`
(If a postulate/abstract definition won't check, make the definition concrete enough to pass — e.g. define `resolveAxis` as a real left fold over `List String` with a `Bool` accumulator. Do not leave holes.)

- [ ] **Step 7: Commit**

```bash
cd /home/kamysh/Work/balovstvo/muninn
git add spec/Muninn/Config.agda spec/Muninn/Types.agda spec/Muninn/Search.agda spec/Muninn/IndexFsm.agda
git commit -m "spec: tiered indexing — vendor axis, classify, tier/embedding-state, backfill"
```

---

## Task 2: Schema + Rust types

**Files:**
- Modify: `crates/core/src/types.rs`
- Modify: `crates/core/src/store.rs:58-103` (table DDL + indexes), `upsert_chunk` (263-310)
- Modify: `crates/core/src/parser.rs:394, 442` (both `Chunk { … }` constructors)
- Modify: `crates/core/src/pipeline.rs:81-85` (post-chunk loop sets repo_id/file_path — now also defaults)
- Modify: `crates/core/src/search.rs:44-58` (row-map) and `arb_result` (243-255)
- Test: inline `#[cfg(test)]` in `types.rs`

**Interfaces:**
- Produces:
  - `pub enum Tier { Tier1, Tier2 }` with `Tier::as_i16()/from_i16()` (1/2).
  - `pub enum EmbeddingState { Embedded, Pending, Absent }` with `as_str()/from_str()` ('embedded'/'pending'/'absent').
  - `Chunk` gains `pub tier: Tier`, `pub embedding_state: EmbeddingState`, `pub content_hash: Option<Vec<u8>>`.
  - `pub fn content_sha256(content: &str) -> Vec<u8>` in `types.rs` (or `store.rs`).

- [ ] **Step 1: Write failing tests for the enums (types.rs)**

```rust
#[test]
fn tier_round_trips_i16() {
    assert_eq!(Tier::from_i16(1), Some(Tier::Tier1));
    assert_eq!(Tier::from_i16(2), Some(Tier::Tier2));
    assert_eq!(Tier::Tier2.as_i16(), 2);
    assert_eq!(Tier::from_i16(7), None);
}

#[test]
fn embedding_state_round_trips_str() {
    assert_eq!(EmbeddingState::from_str("pending"), Some(EmbeddingState::Pending));
    assert_eq!(EmbeddingState::Embedded.as_str(), "embedded");
    assert_eq!(EmbeddingState::from_str("nonsense"), None);
}

#[test]
fn content_sha256_is_stable_and_distinct() {
    assert_eq!(content_sha256("abc"), content_sha256("abc"));
    assert_ne!(content_sha256("abc"), content_sha256("abd"));
    assert_eq!(content_sha256("abc").len(), 32);
}
```

- [ ] **Step 2: Run to verify failure**

Run: `nix develop --command bash -c "cd /home/kamysh/Work/balovstvo/muninn && cargo test -p muninn-core --lib tier_round_trips 2>&1 | tail -5"`
Expected: compile error / unresolved `Tier`.

- [ ] **Step 3: Add the enums, helpers, and Chunk fields (types.rs)**

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Tier { Tier1, Tier2 }

impl Tier {
    pub fn as_i16(self) -> i16 { match self { Tier::Tier1 => 1, Tier::Tier2 => 2 } }
    pub fn from_i16(v: i16) -> Option<Tier> {
        match v { 1 => Some(Tier::Tier1), 2 => Some(Tier::Tier2), _ => None }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum EmbeddingState { Embedded, Pending, Absent }

impl EmbeddingState {
    pub fn as_str(self) -> &'static str {
        match self { Self::Embedded => "embedded", Self::Pending => "pending", Self::Absent => "absent" }
    }
    pub fn from_str(s: &str) -> Option<EmbeddingState> {
        match s {
            "embedded" => Some(Self::Embedded),
            "pending"  => Some(Self::Pending),
            "absent"   => Some(Self::Absent),
            _ => None,
        }
    }
}

/// SHA-256 of chunk content, used to dedup identical Tier-2 chunks.
pub fn content_sha256(content: &str) -> Vec<u8> {
    use sha2::{Digest, Sha256};
    Sha256::digest(content.as_bytes()).to_vec()
}
```
Add to `Chunk`:
```rust
    pub tier: Tier,
    pub embedding_state: EmbeddingState,
    pub content_hash: Option<Vec<u8>>,
```
Add `sha2 = { workspace = true }` to `crates/core/Cargo.toml` (check workspace deps first; add to `[workspace.dependencies]` in root `Cargo.toml` if absent).

- [ ] **Step 4: Update every `Chunk { … }` literal to set the new fields**

In `parser.rs` both constructors (≈394, ≈442): add
```rust
                    tier: Tier::Tier1,
                    embedding_state: EmbeddingState::Embedded,
                    content_hash: None,
```
(Parser default is Tier1/Embedded/None; the pipeline overrides per-file in Task 3/4. Import `Tier`, `EmbeddingState`.)
In `search.rs` row-mapper (≈48) and `arb_result` (≈243): set the three fields too (row-mapper reads from DB in Task 6; for now `Tier::Tier1`, `EmbeddingState::Embedded`, `None` to compile).

- [ ] **Step 5: Run the enum tests — verify pass**

Run: `nix develop --command bash -c "cd /home/kamysh/Work/balovstvo/muninn && cargo test -p muninn-core --lib tier_round_trips embedding_state_round_trips content_sha256 2>&1 | tail -8"`
Expected: 3 passed.

- [ ] **Step 6: Chunk-table DDL — add columns + partial index (store.rs)**

In `register_repo`'s `CREATE TABLE IF NOT EXISTS "{table}"`, add columns:
```sql
            tier            SMALLINT NOT NULL DEFAULT 1,
            embedding_state TEXT NOT NULL DEFAULT 'embedded'
                            CHECK (embedding_state IN ('embedded','pending','absent')),
            content_hash    BYTEA
```
After the existing index creates, add a partial index:
```rust
client.execute(
    &format!(r#"CREATE INDEX IF NOT EXISTS "{table}_pending_idx" ON "{table}" (embedding_state) WHERE embedding_state = 'pending'"#),
    &[],
).await?;
```
Then add idempotent self-heal for existing repos right after the `CREATE TABLE` (so older tables gain the columns when touched):
```rust
for ddl in [
    format!(r#"ALTER TABLE "{table}" ADD COLUMN IF NOT EXISTS tier SMALLINT NOT NULL DEFAULT 1"#),
    format!(r#"ALTER TABLE "{table}" ADD COLUMN IF NOT EXISTS embedding_state TEXT NOT NULL DEFAULT 'embedded'"#),
    format!(r#"ALTER TABLE "{table}" ADD COLUMN IF NOT EXISTS content_hash BYTEA"#),
] {
    client.execute(&ddl, &[]).await?;
}
```
(The `CHECK` is only on the CREATE path; ADD COLUMN omits it to stay idempotent — the enum mapping enforces validity in Rust.)

- [ ] **Step 7: `upsert_chunk` — write the new columns (store.rs)**

Update the INSERT column list, VALUES, ON CONFLICT SET, and params to include `tier`, `embedding_state`, `content_hash`:
```rust
INSERT INTO "{table}" (id, repo_id, file_path, start_line, end_line, content, embedding, tier, embedding_state, content_hash)
VALUES ($1,$2,$3,$4,$5,$6,$7,$8,$9,$10)
ON CONFLICT (id) DO UPDATE SET
    file_path=EXCLUDED.file_path, start_line=EXCLUDED.start_line, end_line=EXCLUDED.end_line,
    content=EXCLUDED.content, embedding=EXCLUDED.embedding,
    tier=EXCLUDED.tier, embedding_state=EXCLUDED.embedding_state, content_hash=EXCLUDED.content_hash
```
Params append: `&chunk.tier.as_i16(), &chunk.embedding_state.as_str(), &chunk.content_hash`.

- [ ] **Step 8: Gates + commit**

Run each, expect exit 0:
```bash
cd /home/kamysh/Work/balovstvo/muninn/spec && nix develop --command agda --safe Muninn.agda >/dev/null 2>&1; echo "AGDA: $?"
nix develop /home/kamysh/Work/balovstvo/muninn --command bash -c "cd /home/kamysh/Work/balovstvo/muninn && cargo build >/dev/null 2>&1; echo BUILD: \$?; cargo clippy --all-targets -- -D warnings >/dev/null 2>&1; echo CLIPPY: \$?; cargo fmt --all -- --check >/dev/null 2>&1; echo FMT: \$?; cargo nextest run -p muninn-core >/dev/null 2>&1; echo TEST: \$?"
```
```bash
git add crates/core/src/types.rs crates/core/src/store.rs crates/core/src/parser.rs crates/core/src/search.rs crates/core/Cargo.toml Cargo.toml Cargo.lock
git commit -m "feat(core): Tier/EmbeddingState/content_hash on Chunk + chunk-table schema"
```

---

## Task 3: classify() — exclude/vendor resolution

**Files:**
- Modify: `crates/core/src/config.rs` (add `IndexConfig.vendor`, defaults, resolver, `classify`)
- Modify: `crates/core/src/pipeline.rs` (`build_excludes` companion for vendor; expose a classifier)
- Test: inline in `config.rs`

**Interfaces:**
- Consumes: `EffectiveConfig` (already has `exclude: Vec<String>`).
- Produces:
  - `EffectiveConfig.vendor: Vec<String>`.
  - `pub const EXCLUDE_DEFAULTS: &[&str]`, `pub const VENDOR_DEFAULTS: &[&str]` in `config.rs`.
  - `EffectiveConfig::merge` resolves `exclude` and `vendor` by `defaults ++ global ++ repo` (layered fold replaces the prior replace semantics).
  - `pub enum Decision { Drop, Tier1, Tier2 }` and `pub fn classify(repo_root: &Path, exclude: &[String], vendor: &[String], rel: &Path) -> Decision` in `pipeline.rs`, built on `ignore::overrides::Override` (last-match-wins, `!` negation already native).

- [ ] **Step 1: Failing tests for merge resolution + classify (config.rs / pipeline.rs)**

In `config.rs`:
```rust
#[test]
fn exclude_layered_fold_inherits_and_adds() {
    let mut global = GlobalConfig::default();
    global.index.exclude = vec!["g_only/".into()];
    let repo = RepoConfig { index: Some(IndexConfig { exclude: vec!["r_only/".into()], vendor: vec![] }), ..Default::default() };
    let eff = EffectiveConfig::merge(&global, &repo, "p");
    // defaults ++ global ++ repo — all present (no longer whole-list replace)
    assert!(eff.exclude.iter().any(|g| g == "g_only/"));
    assert!(eff.exclude.iter().any(|g| g == "r_only/"));
    assert!(eff.exclude.iter().any(|g| g == ".git/")); // a shipped default
}
```
In `pipeline.rs` tests:
```rust
#[test]
fn classify_exclude_wins_over_vendor() {
    let root = Path::new("/repo");
    let d = classify(root, &["**/x/**".into()], &["**/x/**".into()], Path::new("x/a.js"));
    assert_eq!(d, Decision::Drop);
}
#[test]
fn classify_vendor_then_tier1() {
    let root = Path::new("/repo");
    assert_eq!(classify(root, &[], &["**/node_modules/**".into()], Path::new("node_modules/p/i.js")), Decision::Tier2);
    assert_eq!(classify(root, &[], &["**/node_modules/**".into()], Path::new("src/main.rs")), Decision::Tier1);
}
#[test]
fn classify_negation_reclaims_tier1() {
    let root = Path::new("/repo");
    // vendor default target/, but repo negates it
    let d = classify(root, &[], &["**/target/**".into(), "!**/target/**".into()], Path::new("target/x.rs"));
    assert_eq!(d, Decision::Tier1);
}
```

- [ ] **Step 2: Run — verify failure**

Run: `nix develop /home/kamysh/Work/balovstvo/muninn --command bash -c "cd /home/kamysh/Work/balovstvo/muninn && cargo test -p muninn-core --lib classify 2>&1 | tail -5"`
Expected: unresolved `classify` / `Decision`.

- [ ] **Step 3: Add defaults + vendor field + layered merge (config.rs)**

```rust
pub const EXCLUDE_DEFAULTS: &[&str] = &[
    ".git/", "**/*.min.js", "**/*.min.css", "**/*.map", "**/*.snap",
    "**/package-lock.json", "**/yarn.lock", "**/pnpm-lock.yaml",
    "**/Cargo.lock", "**/poetry.lock", "**/Gemfile.lock", "**/composer.lock",
];
pub const VENDOR_DEFAULTS: &[&str] = &[
    "**/node_modules/**", "**/vendor/**", "vendor/",
    "**/.venv/**", "**/venv/**", "**/site-packages/**",
    "**/target/**", "**/dist/**", "**/build/**", "**/.tox/**", "**/__pycache__/**",
];
```
Add `pub vendor: Vec<String>` to `IndexConfig` (with `#[serde(default)]`). Add `pub vendor: Vec<String>` to `EffectiveConfig`. In `merge`, build each axis as `defaults ++ global ++ repo`:
```rust
fn layer(defaults: &[&str], global: &[String], repo: Option<&[String]>) -> Vec<String> {
    let mut v: Vec<String> = defaults.iter().map(|s| s.to_string()).collect();
    v.extend(global.iter().cloned());
    if let Some(r) = repo { v.extend(r.iter().cloned()); }
    v
}
```
Resolve `exclude` and `vendor` with `layer(...)` (drop the old `effective`-replace clause for exclude). The `ignore` matcher applies last-match-wins + `!` negation, so the concatenated order is the precedence.

- [ ] **Step 4: Add classify (pipeline.rs)**

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Decision { Drop, Tier1, Tier2 }

/// Classify a repo-relative path: exclude drops first; vendor → Tier 2;
/// otherwise Tier 1. Built on the same last-match-wins/`!`-negation matcher
/// as build_excludes. Spec: Muninn.Config.classify.
pub fn classify(repo_root: &Path, exclude: &[String], vendor: &[String], rel: &Path) -> Decision {
    if path_excluded(&build_excludes(repo_root, exclude), rel) { return Decision::Drop; }
    if path_excluded(&build_excludes(repo_root, vendor), rel) { return Decision::Tier2; }
    Decision::Tier1
}
```
(`build_excludes`/`path_excluded` already implement the negation + ancestor semantics. Building two `Override`s per call is fine for now; Task 4 hoists them out of the per-file loop.)

- [ ] **Step 5: Run tests — verify pass**

Run: `nix develop /home/kamysh/Work/balovstvo/muninn --command bash -c "cd /home/kamysh/Work/balovstvo/muninn && cargo test -p muninn-core --lib classify exclude_layered 2>&1 | tail -8"`
Expected: all pass.

- [ ] **Step 6: Gates + commit** (run the full five-gate block from Task 2 Step 8.)

```bash
git add crates/core/src/config.rs crates/core/src/pipeline.rs
git commit -m "feat(core): classify() with exclude/vendor layered-fold resolution + defaults"
```

---

## Task 4: Foreground pipeline split (Tier-1 eager, Tier-2 pending)

**Files:**
- Modify: `crates/core/src/pipeline.rs` (`index_repo` classifies; `index_file` gains a `tier` param and branches embed vs pending)
- Test: `crates/core/tests/` (new integration or inline)

**Interfaces:**
- Consumes: `classify`, `Decision`, `EffectiveConfig.{exclude,vendor}`, `content_sha256`, `Tier`, `EmbeddingState`.
- Produces: `index_file(..., tier: Tier)` — Tier 1 embeds (state `Embedded`/`Absent`), Tier 2 skips embed (state `Pending`), both set `content_hash`.

- [ ] **Step 1: Failing test — Tier-2 file is chunked, pending, hashed, not embedded**

Add an integration test that indexes a tiny temp repo with a `node_modules/` file and a `src/` file, then asserts (querying the chunk table): src chunks `embedding_state='embedded'` with non-null embedding; node_modules chunks `embedding_state='pending'`, null embedding, non-null `content_hash`, `tier=2`.
(Use the existing test-repo harness pattern from `graph_integration.rs`: `register_repo` with a tiny dim, a `TestEmbeddingBackend`.)

- [ ] **Step 2: Run — verify failure** (Tier-2 currently embedded like everything else).

- [ ] **Step 3: Thread tier through index_repo → index_file**

In `index_repo`, before the per-file loop, hoist the two `Override`s once (exclude, vendor); for each file compute `rel = file.strip_prefix(repo_path)` and `decision = classify(...)`; skip `Drop` (already excluded by the walker, but classify is the authority); call `index_file(..., tier)` with `Tier1`/`Tier2`. Pass `eff.exclude`/`eff.vendor` into `index_repo` (signature gains `vendor: &[String]`).

**Update ALL callers of `index_repo`** — grep for `index_repo(` first. Known sites: `crates/cli/src/main.rs` (`run_foreground_index` → pass `&eff.vendor`), and `crates/indexer/src/main.rs` (the daemon reindex spawn → pass `&eff.vendor`; it already builds `eff = EffectiveConfig::merge(...)`). Both must pass the resolved vendor list or the build breaks.

In `index_file`, add `tier: Tier` param. After chunking, set on each chunk: `c.tier = tier; c.content_hash = Some(content_sha256(&c.content));`. Then:
- `Tier1`: embed as today; set `embedding_state = Embedded` (or `Absent` on the empty-embedder warn-path).
- `Tier2`: **skip the embed batch entirely**; set `embedding_state = Pending`, leave `embedding = None`.

- [ ] **Step 4: Run the integration test — verify pass.**

- [ ] **Step 5: Gates + commit**

```bash
git add crates/core/src/pipeline.rs crates/cli/src/main.rs crates/indexer/src/main.rs crates/core/tests/
git commit -m "feat(core): foreground indexes Tier 1 eagerly, Tier 2 as pending+hashed"
```

---

## Task 5: Daemon backfill (drain pending, dedup by content_hash)

**Files:**
- Create: `crates/indexer/src/backfill.rs`
- Modify: `crates/indexer/src/main.rs` (call backfill in the scan loop; declare `mod backfill`)
- Modify: `crates/core/src/store.rs` (queries: list pending grouped by hash; bulk-set embedding for a hash)
- Test: integration in `crates/core/tests/` or `crates/indexer`

**Interfaces:**
- Consumes: `EmbeddingBackend`, `content_hash`, per-repo chunk table, `expected_dimension`.
- Produces:
  - `store::pending_content_groups(client, repo_id, limit) -> Vec<(Vec<u8>, String)>` — distinct (content_hash, one representative content) where `embedding_state='pending'`.
  - `store::set_embedding_for_hash(client, repo_id, content_hash, &embedding) -> u64` — set embedding + `embedding_state='embedded'` for all pending chunks with that hash; returns rows updated.
  - `backfill::run_once(client, cfg, repo_id, embedder, expected_dim) -> Result<usize>` — embeds up to a batch of unique pending contents, returns chunks updated.

- [ ] **Step 1: Failing test — backfill embeds pending, dedups identical content**

Seed a repo table with 3 pending chunks: two identical content (same hash), one distinct. Run `backfill::run_once`. Assert: embedder called for **2 unique contents** (not 3); all 3 chunks become `embedded` with non-null embeddings; the two identical chunks share the same vector. (Use a `TestEmbeddingBackend` that counts calls.)

- [ ] **Step 2: Run — verify failure.**

- [ ] **Step 3: store.rs queries**

```rust
pub async fn pending_content_groups(client: &Client, repo_id: Uuid, limit: i64)
    -> Result<Vec<(Vec<u8>, String)>> {
    let table = chunks_table(repo_id);
    let rows = client.query(&format!(
        r#"SELECT DISTINCT ON (content_hash) content_hash, content
           FROM "{table}" WHERE embedding_state = 'pending' AND content_hash IS NOT NULL
           ORDER BY content_hash LIMIT $1"#), &[&limit]).await?;
    Ok(rows.iter().map(|r| (r.get::<_, Vec<u8>>(0), r.get::<_, String>(1))).collect())
}

pub async fn set_embedding_for_hash(client: &Client, repo_id: Uuid, content_hash: &[u8], embedding: &[f32])
    -> Result<u64> {
    let table = chunks_table(repo_id);
    let vec = pgvector::Vector::from(embedding.to_vec());
    Ok(client.execute(&format!(
        r#"UPDATE "{table}" SET embedding = $1, embedding_state = 'embedded'
           WHERE content_hash = $2 AND embedding_state = 'pending'"#),
        &[&vec, &content_hash]).await?)
}
```

- [ ] **Step 4: backfill.rs**

```rust
use anyhow::Result;
use muninn_core::{embeddings::EmbeddingBackend, store};
use tokio_postgres::Client;
use uuid::Uuid;

const BACKFILL_BATCH: i64 = 128;

pub async fn run_once(client: &Client, repo_id: Uuid, embedder: &dyn EmbeddingBackend, expected_dim: usize) -> Result<usize> {
    let groups = store::pending_content_groups(client, repo_id, BACKFILL_BATCH).await?;
    if groups.is_empty() { return Ok(0); }
    let texts: Vec<String> = groups.iter().map(|(_, c)| c.clone()).collect();
    let embeddings = embedder.embed(&texts).await?;
    let mut updated = 0usize;
    for ((hash, _), emb) in groups.iter().zip(embeddings) {
        if emb.len() != expected_dim { continue; } // mismatch guard (spec: ValidStoredEmbedding)
        updated += store::set_embedding_for_hash(client, repo_id, hash, &emb).await? as usize;
    }
    Ok(updated)
}
```

- [ ] **Step 5: Wire into the daemon scan loop (main.rs)**

Add `mod backfill;`. In the per-repo handling, after a repo is `Indexed` and the watcher is (re)attached, call `backfill::run_once` in a loop until it returns 0 (or once per scan tick to stay cooperative). Open a `Client` for it as the daemon already does for other per-repo work; use the repo's effective embedder + `expected_dimension`. Log progress (`tracing::info!`).

- [ ] **Step 6: Run the dedup test — verify pass (embedder called twice, 3 chunks embedded).**

- [ ] **Step 7: Gates + commit**

```bash
git add crates/indexer/src/backfill.rs crates/indexer/src/main.rs crates/core/src/store.rs crates/core/tests/
git commit -m "feat(indexer): daemon backfills pending Tier-2 embeddings, dedup by content_hash"
```

---

## Task 6: Tier-aware search (down-weight + per-file cap)

**Files:**
- Modify: `crates/core/src/search.rs` (SELECT `tier`; map it; `rrf_merge` weight + cap)
- Test: extend the existing `rrf_merge` quickcheck block

**Interfaces:**
- Consumes: `Tier`, `Chunk.tier`.
- Produces: `rrf_merge` applies `VENDOR_WEIGHT` to Tier-2 fused scores and enforces `PER_FILE_CAP`. Constants `pub const VENDOR_WEIGHT: f32 = 0.3; pub const PER_FILE_CAP: usize = 3;`.

- [ ] **Step 1: Failing tests (search.rs)**

```rust
#[test]
fn tier2_is_downweighted_below_equal_tier1() {
    // same rank in one list each; Tier1 must outrank Tier2 after weighting
    let t1 = result_with_tier(Uuid::new_v4(), Tier::Tier1);
    let t2 = result_with_tier(Uuid::new_v4(), Tier::Tier2);
    let merged = rrf_merge(vec![t2], vec![t1.clone()], 10);
    assert_eq!(merged[0].chunk.id, t1.chunk.id);
}
#[test]
fn per_file_cap_limits_one_file() {
    let same = "node_modules/x.js";
    let items: Vec<_> = (0..10).map(|_| result_in_file(Uuid::new_v4(), same, Tier::Tier2)).collect();
    let merged = rrf_merge(items, vec![], 100);
    assert!(merged.iter().filter(|r| r.chunk.file_path == same).count() <= PER_FILE_CAP);
}
```
Add helpers `result_with_tier`/`result_in_file` mirroring `arb_result` but with `tier`/`file_path`.

Also a quickcheck:
```rust
fn prop_no_file_exceeds_cap(n: u8) -> bool {
    let n = (n as usize).min(50);
    let items: Vec<_> = (0..n).map(|_| result_in_file(Uuid::new_v4(), "f", Tier::Tier1)).collect();
    let merged = rrf_merge(items, vec![], 1000);
    merged.iter().filter(|r| r.chunk.file_path == "f").count() <= PER_FILE_CAP
}
```

- [ ] **Step 2: Run — verify failure.**

- [ ] **Step 3: SELECT + map tier (search.rs)**

Add `tier` to the SELECT column lists in `fulltext_search` and `semantic_search`, and to the row-mapper: `tier: Tier::from_i16(row.try_get::<_, i16>("tier")?).unwrap_or(Tier::Tier1)`. (Set `embedding_state`/`content_hash` to read-defaults `Embedded`/`None` in the mapper — search doesn't need them.)

- [ ] **Step 4: Tier-aware rrf_merge (search.rs)**

After computing each entry's fused score, apply the weight using the carried `chunk.tier`; after sort, enforce the per-file cap while truncating:
```rust
pub const VENDOR_WEIGHT: f32 = 0.3;
pub const PER_FILE_CAP: usize = 3;

// in rrf_merge, when finalizing each (score, result):
let score = if result.chunk.tier == Tier::Tier2 { raw * VENDOR_WEIGHT } else { raw };
// after sort_by desc, build the output respecting PER_FILE_CAP per file_path,
// then truncate to `limit`.
```
Replace the `results.truncate(limit)` tail with a cap-aware fold: iterate sorted, keep a `HashMap<String, usize>` of per-file counts, push while `count < PER_FILE_CAP` and total `< limit`.

- [ ] **Step 5: Run tests + the existing rrf props — verify pass.**

- [ ] **Step 6: Gates + commit**

```bash
git add crates/core/src/search.rs
git commit -m "feat(search): tier-aware rrf_merge — down-weight Tier 2, cap results per file"
```

---

## Task 7: Cross-cutting integration + docs

**Files:**
- Test: `crates/core/tests/tiered_indexing.rs` (new)
- Modify: `CLAUDE.md` / `docs/development.md` (document tiers, vendor config, reindex-to-activate)

**Interfaces:** consumes everything above.

- [ ] **Step 1: End-to-end integration test**

Index a temp repo containing `src/a.rs`, `node_modules/dep/i.js`, and a `*.min.js` (excluded). After foreground index: assert excluded file has zero chunks; src chunks `embedded`+Tier1; node_modules chunks `pending`+Tier2+hashed, no embedding. Run `backfill::run_once`; assert node_modules chunks become `embedded`. Then a hybrid search where a query term appears in both src and node_modules returns the src chunk ranked above the vendor chunk, and never more than `PER_FILE_CAP` from one vendor file.

- [ ] **Step 2: Run — verify pass.**

- [ ] **Step 3: Docs**

Update `CLAUDE.md` (config section) and `docs/development.md`: document `[index] vendor`, the layered-fold-with-negation resolution (defaults ++ global ++ repo, `!` to subtract), exclude=drop vs vendor=downweight, and that **existing repos need `muninn reindex` to gain tiering**.

- [ ] **Step 4: Full gate sweep + commit**

```bash
cd /home/kamysh/Work/balovstvo/muninn/spec && nix develop --command agda --safe Muninn.agda >/dev/null 2>&1; echo "AGDA: $?"
nix develop /home/kamysh/Work/balovstvo/muninn --command bash -c "cd /home/kamysh/Work/balovstvo/muninn && cargo build >/dev/null 2>&1; echo BUILD:\$?; cargo clippy --all-targets -- -D warnings >/dev/null 2>&1; echo CLIPPY:\$?; cargo fmt --all -- --check >/dev/null 2>&1; echo FMT:\$?; cargo nextest run >/dev/null 2>&1; echo TEST:\$?"
git add crates/core/tests/tiered_indexing.rs CLAUDE.md docs/development.md
git commit -m "test+docs: end-to-end tiered indexing coverage and config docs"
```

---

## Notes for the implementer

- **Integration tests need Postgres** (per-repo tables, pgvector). They follow the `graph_integration.rs` pattern: `register_repo` with a small dim, a `TestEmbeddingBackend`, `cleanup` via `delete_repo`. They will be skipped/fail without `TEST_DATABASE_URL`; run them in the Nix shell where the DB is configured.
- **`embedding_state='absent'`** is set only on the existing empty-embedder warn-path in `index_file` (Tier 1). Keep it distinct from `pending`.
- **Reindex pruning** (`prune_chunks_not_in`) already handles orphans; tier/state ride along on re-upsert. No change needed.
- **Per-repo table ALTERs** run on every `register_repo` call — idempotent and cheap. The daemon reaches `register_repo`/ensure-table on its scan path, so existing repos self-heal when next touched, but tier/state values only become correct after a reindex.
