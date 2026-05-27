# Building and development

## Prerequisites

- [Nix](https://nixos.org/download) with flakes enabled
- PostgreSQL 16+ with [pgvector](https://github.com/pgvector/pgvector) and [Apache AGE](https://age.apache.org/) (or use the [kamysh/postgres-ai](https://hub.docker.com/r/kamysh/postgres-ai) Docker image)

## Enter the dev shell

All tools (Rust, sqlx-cli, Agda, etc.) are provided by the Nix dev shell:

```bash
nix develop
```

The shell sets:
- `DATABASE_URL=postgresql://localhost/muninn_dev`
- `TEST_DATABASE_URL=postgresql://localhost/muninn_test`

The local embedding backend is pure-Rust (tessera-embeddings + candle), so the binary has no runtime native dependency on ONNX Runtime or any other inference engine.

## Database setup

```bash
createdb muninn_dev
createdb muninn_test
sqlx migrate run
```

## Common commands

| Task | Command |
|------|---------|
| Build (debug) | `cargo build` |
| Build (release) | `cargo build --release` |
| Test (all) | `cargo nextest run` |
| Test (single crate) | `cargo nextest run -p muninn_core` |
| Test (single test by name) | `cargo nextest run -p muninn_core -- types::tests::line_range_valid_when_start_equals_end` |
| Lint | `cargo clippy -- -D warnings` |
| Format | `cargo fmt` |
| Watch mode | `cargo watch -x build` |
| Regenerate offline query cache | `cargo sqlx prepare --workspace` |
| Apply pending migrations | `sqlx migrate run` |
| Roll back one migration | `sqlx migrate revert` |
| Type-check Agda spec | `cd spec && agda Muninn.agda` |
| Build (Nix-managed install) | `nix build` |
| Build a portable release binary | `cargo build --release --target=<triple>` |

After changing any `sqlx::query!` macro, run `cargo sqlx prepare --workspace` to update the offline query cache (`.sqlx/` directory). This cache lets CI compile without a live database. The CI build will fail if the cache is stale — commit the updated `.sqlx/` files along with your SQL changes.

---

## Architecture

This section explains the non-obvious design decisions. Reading code is faster once you understand why things are shaped the way they are.

### Why the indexer is database-driven

The indexer daemon does not scan the filesystem for repos. It queries the `repos` table. This means adding or removing a repo via the CLI takes effect in the daemon within seconds — the CLI sends `NOTIFY muninn_repos_changed` after any mutation, and the daemon wakes up and re-queries. There is also a 60-second fallback poll because NOTIFY is not durable: it is delivered only to clients connected at the moment the notification fires, so a daemon that was down during a CLI operation would miss it entirely.

When the daemon receives a repo change (or the 60-second timer fires), it calls `scan_and_dispatch`, which queries all registered repos and makes one of two decisions per repo:

- If the repo has `indexed_at IS NOT NULL` and no watcher running, spawn a file-watcher task (`notify` crate).
- If `indexed_at IS NULL` and `ever_indexed` is true, abort the existing watcher (if any) and spawn a full reindex task. The watcher is aborted first to prevent concurrent chunk mutations in the same table.

The `ever_indexed` column distinguishes "freshly registered, never indexed" (skip — the user must run `muninn add` which does the first index in the foreground) from "was indexed, then reset via `muninn reindex`" (daemon must act).

### Why per-repo chunk tables

Each registered repo gets its own PostgreSQL table, named `chunks_<uuid>` where `uuid` is the repo's primary key in the `repos` table. Each table has a `VECTOR(N)` column where N is the embedding dimension chosen at registration time.

This design is forced by how vector columns work: a `VECTOR(768)` column cannot store a `VECTOR(1024)` embedding — the type is parameterised by dimension. Because different repos can use different embedding backends, and different backends produce different dimensions (local=768, voyage=1024, openai=1536), a single shared `chunks` table is not viable unless all repos use the same dimension. The per-repo table design sidesteps this entirely.

The consequence is the DimFrozen invariant: once a repo's embedding dimension is recorded in `repos.embedding_dim`, it cannot change without dropping and recreating the table. `muninn remove` + `muninn add` is the supported migration path. The dimension is recorded at `muninn add` time by calling `expected_dimension(&eff.embeddings)`, which maps (backend, model) → fixed integer. This function must return a stable value — see the contributor note in the Embedding backends section.

Per-repo AGE graphs follow the same pattern: each repo gets a graph named `code_graph_<uuid>`, created alongside the chunks table in `store::register_repo`.

### The distributed indexer lock

`repos.indexing_heartbeat` is a lightweight distributed mutex. Before starting to index a repo, the daemon calls `store::try_lock_repo`, which does a conditional update:

```sql
UPDATE repos
   SET indexing_heartbeat = NOW()
 WHERE id = $1
   AND (indexing_heartbeat IS NULL
        OR indexing_heartbeat < NOW() - INTERVAL '2 minutes')
```

If `rows_affected == 1`, the lock was acquired. If `0`, another process holds a live lock and the repo is skipped for this cycle.

During indexing, a background task pulses the heartbeat every 60 seconds. The stale threshold is 120 seconds — exactly 2× the pulse interval. This allows one missed pulse (e.g. due to a transient network delay to the database) before the lock is declared stale and can be taken over by another indexer. The lock is released unconditionally in a finally-equivalent after `index_repo` completes (success or error).

`muninn remove` checks `repo.is_lock_live()` before deleting any index data. If the lock is live, removal is refused. This prevents a race where an in-progress indexer writes chunks into a table that the CLI just deleted.

### How repo resolution works in muninn-mcp

MCP tools accept two ways to identify a repo: `repo` (an explicit absolute path) or `cwd` (the caller's working directory). When `cwd` is provided, `repo_resolver::find_repo_root` walks up the directory tree until it finds `.muninn.toml`. This is why the marker file must sit at the repo root — it is the anchor for resolution.

The MCP server does not cache a list of registered repos in memory. It resolves the repo root from the filesystem marker on every query, then looks up the repo record in the database by path. The decoupling means the MCP server starts instantly with no warmup query and never gets out of sync with the `repos` table.

### Config merge semantics

The merge logic in `EffectiveConfig::merge(global, repo_cfg, dir_name)` is section-level, not key-level. If `repo_cfg.embeddings` is present, it entirely replaces `global.embeddings`. If it is absent, `global.embeddings` is used as-is. Individual key merging is not supported — partial overrides create confusing precedence interactions and are hard to reason about statically.

All config structs carry `#[serde(deny_unknown_fields)]`. Unknown keys in TOML are rejected at parse time with a clear error. Typos do not silently inherit the global value.

### The Agda formal specification

`spec/Muninn.agda` and its submodules (`spec/Muninn/Types.agda`, `spec/Muninn/Index.agda`, `spec/Muninn/Concurrency.agda`) are a machine-checked formal model of the system's core invariants. The spec does not generate code and is not wired into the build. It is type-checked with Agda separately and exists to:

1. Make invariants precise and checkable — "no empty chunks" is a theorem, not a comment in a README.
2. Catch implementation drift — when you change Rust code that touches an invariant, updating and re-checking the spec verifies that the invariant still holds as stated.

Run the spec check (without `--safe`, since `Concurrency.agda` has intentional postulates):

```bash
cd spec && agda Muninn.agda
```

Invariants formalised (these must match the implementation):

| Invariant | What it says | Where enforced |
|-----------|-------------|----------------|
| `ValidChunk` | No empty-content chunks | `store::upsert_chunk`, `pipeline.rs` |
| `ValidStoredEmbedding` | Embedding length must equal `repos.embedding_dim` | `pipeline.rs` |
| `BatchOutcome` | A totally-failed batch must not advance repo to Indexed state | `pipeline.rs` |
| `DimFrozen` | Embedding dimension is immutable after registration | `store::register_repo`, indexer DimFrozen check |
| `IsolatedGraph` | Chunks written to DB before symbols can reference them | `pipeline.rs` ordering |
| `UniqueRepoPaths` | One registration per filesystem path | `UNIQUE` constraint on `repos.path` |
| `Concurrency` | One indexer per repo; stale lock threshold 120 s | `store::try_lock_repo`, heartbeat pulse |

When you make a change touching any of these, update the spec and re-run `agda Muninn.agda`. Use the `spec-reconcile` Claude Code skill for systematic audits.

---

## Embedding backends

The `EmbeddingBackend` trait lives in `crates/core/src/embeddings/`. `make_backend(&eff.embeddings)` dispatches to the correct implementation. `expected_dimension(&eff.embeddings)` returns the fixed output dimension for a (backend, model) pair.

| Backend | Model | Dims |
|---------|-------|------|
| `local` | BGE-Base-EN-v1.5 | 768 |
| `voyage` | voyage-code-3 | 1024 |
| `openai` | text-embedding-3-small | 1536 |

**Critical constraint for contributors:** `expected_dimension` must return a stable value for a given (backend, model) pair. Changing this value for an existing combination would invalidate all repos registered with that combination — their stored `embedding_dim` would no longer match what the backend produces, and every query would fail the DimFrozen check. If you add a new model or backend, the dimension is determined by what the embedding API actually returns and must match exactly.

---

## Adding a language parser

Parsers live in `crates/core/src/parser.rs`. Each language needs four additions:

1. A tree-sitter grammar crate dependency in `crates/core/Cargo.toml`
2. A match arm in `detect_language` mapping file extensions to a `Language` enum value
3. A match arm in `chunk_file` mapping `Language` to a tree-sitter query for chunking
4. A match arm in `extract_edges` mapping `Language` to a tree-sitter query for symbol edges

Run `cargo nextest run -p muninn_core` after adding a parser. Tests in `parser.rs` cover round-trip parse → chunk → edge extraction.

---

## Adding an embedding backend

1. Add a variant to `EmbeddingBackend` enum in `crates/core/src/config.rs`
2. Implement the `EmbeddingBackend` trait for the new backend in `crates/core/src/embeddings/`
3. Add the dispatch case to `make_backend`
4. Add the dimension to `expected_dimension` — this value is permanent once the backend ships
5. Add the backend name to `docs/configuration.md`

---

## Database migrations

Migrations are SQL files in `migrations/`, numbered sequentially (`001_initial.sql` through the latest). They are embedded into the binary at compile time:

```rust
sqlx::migrate!("../../migrations").run(pool).await?
```

Migrations run automatically when `muninn config` is called. Applied migrations are tracked in `_sqlx_migrations`. Migrations are idempotent — re-running is always safe.

After adding or changing a `sqlx::query!` macro anywhere in the workspace:

```bash
cargo sqlx prepare --workspace
```

This regenerates `.sqlx/` — the offline query cache that allows CI to compile without a live database. Commit the updated `.sqlx/` files alongside your SQL changes.

---

## Building distributable binaries

There are two paths depending on whether you want a Nix-managed install on this
machine, or a portable binary that can be copied elsewhere.

### Nix-managed install (this machine only)

```bash
nix profile install .
claude mcp add --scope user muninn ~/.nix-profile/bin/muninn-mcp
```

The `muninn` derivation produces a binary that references a small number of
Nix-store paths (notably `libiconv` on darwin). The profile install keeps
those paths alive as a GC root. The binary will not run on a machine without
the same Nix-store entries — use `muninn-static` if you need that.

### Portable release binary (copy anywhere)

```bash
nix build .#muninn-static
```

`pkgsStatic.rustPlatform` links everything reachable statically, so the
result has no `/nix/store` references — only Apple system frameworks (darwin)
or no shared libraries at all (Linux musl). The local embedding backend is
pure-Rust (tessera-embeddings + candle), so there is no `libonnxruntime` to
ship or load.

Binaries land in `result/bin/`: `muninn`, `muninn-index`, `muninn-mcp`. The
GitHub release workflow (`.github/workflows/release.yml`) builds this target
for `linux-amd64`, `linux-arm64`, and `darwin-arm64`.
