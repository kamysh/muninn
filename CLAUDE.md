# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Development Environment

All commands assume you are inside the Nix dev shell:

```bash
nix develop
```

The shell sets `DATABASE_URL` (default: `postgresql://localhost/muninn_dev`), `TEST_DATABASE_URL`, and `ORT_DYLIB_PATH` for ONNX runtime.

## Common Commands

```bash
# Build
cargo build
cargo build --release

# Test (nextest preferred)
cargo nextest run
cargo nextest run -p muninn_core                          # single crate
cargo nextest run -p muninn_core -- types::tests::line_range_valid_when_start_equals_end  # single test

# Lint and format
cargo clippy -- -D warnings
cargo fmt

# Watch mode
cargo watch -x build

# Database migrations
sqlx migrate run                  # apply pending migrations
sqlx migrate revert               # roll back one migration

# Prepare sqlx offline query cache (run after changing queries)
cargo sqlx prepare --workspace

# Formal spec type-check
cd spec && agda Muninn.agda

# Nix builds
nix build                         # dynamically linked (requires nix profile install to run)
nix build .#muninn-static         # fully static musl binary, safe to copy
```

## Architecture

Four-crate workspace sharing a PostgreSQL database (pgvector + Apache AGE):

```
crates/
  core/       — muninn_core library (shared by all binaries)
  indexer/    — muninn-index daemon
  mcp/        — muninn-mcp MCP server
  cli/        — muninn CLI
```

### `muninn_core` modules

| Module | Responsibility |
|--------|---------------|
| `types` | Domain types: `Repo`, `Chunk`, `Symbol`, `SearchResult`, `IndexState`, `BatchOutcome`, `Similarity` |
| `config` | `GlobalConfig` / `RepoConfig` / `EffectiveConfig`; `EffectiveConfig::merge` applies per-repo overrides |
| `db` | Pool construction (`connect_with_app_name`, `connect_listener`) |
| `store` | DB read/write for `repos` and `chunks`; `notify_repos_changed` sends `LISTEN/NOTIFY` |
| `pipeline` | `index_file` and `index_repo` — parse → embed → store chunks → store graph |
| `parser` | tree-sitter parsing (Rust, Python, JS, TS); `detect_language`, `parse_file`, `chunk_file`, `extract_edges` |
| `embeddings` | `EmbeddingBackend` trait; Voyage AI / OpenAI / local ONNX backends; `expected_dimension` |
| `graph` | AGE graph writes (`upsert_symbol_node`, `upsert_edge`) and structural queries (`query_related`) |
| `search` | `semantic_search`, `fulltext_search`, `rrf_merge` (Reciprocal Rank Fusion) |
| `knowledge` | `KnowledgeItem` CRUD + hybrid search (separate from code chunks) |
| `repo_resolver` | Walk up from a path to the nearest `.muninn.toml` |

### Indexer daemon (`muninn-index`)

DB-driven: discovers repos by querying the `repos` table, not by scanning filesystem. Receives `NOTIFY muninn_repos_changed` on any repo change, with a 60 s fallback poll for resilience. For each repo it either spawns a full reindex task or a file-watcher task (`notify` crate), tracking both in a `HashMap<Uuid, JoinHandle>`. A watcher is aborted before a reindex starts to prevent concurrent chunk mutations.

### MCP server (`muninn-mcp`)

Exposes 7 tools via stdio JSON-RPC (rmcp):

- `search_hybrid` — semantic + full-text with RRF ranking
- `search_fulltext` — PostgreSQL tsvector keyword search
- `search_semantic` — pgvector cosine similarity
- `search_structural` — AGE graph traversal (callers/callees/imports/inheritors/inherits/defines)
- `record_knowledge` — upsert a structured knowledge item (with embedding)
- `search_knowledge` — hybrid search over knowledge items
- `delete_knowledge` / `list_knowledge`

Repo resolution: tools accept `repo` (explicit path) or `cwd` (walks up to nearest `.muninn.toml`).

### CLI (`muninn`)

`add`, `configure`, `remove`, `list`, `reindex`, `status`, `stats`. Does not perform background indexing — that is the daemon's job.

- `add <path>` — creates `.muninn.toml` (via `$EDITOR` in a temp file), registers the repo in the DB, and runs a foreground index in one step; fails if the repo is already registered
- `configure <path>` — opens existing `.muninn.toml` in a temp file, validates (including DimFrozen check), writes the real file only on success, and runs a foreground reindex if the content changed; prints "No changes." otherwise
- `remove <path>` — deletes `.muninn.toml` and all index data (refuses if a live indexing lock is held)
- `reindex <path>` — signals the daemon to reindex (sets `indexed_at = NULL`; daemon picks it up)

## Database Schema

Per-repo chunks are stored in **per-repo tables** named after the repo UUID, each with a `VECTOR(embedding_dim)` column where `embedding_dim` is fixed at registration time. The `repos` table is the central registry.

Key `repos` columns:
- `indexed_at` — `NULL` means needs (re)index; set by `mark_indexed`
- `ever_indexed` — survives reindex reset; daemon uses it to distinguish "never indexed" from "needs reindex"
- `embedding_dim` — frozen after first index (DimFrozen invariant)
- `indexing_heartbeat` — distributed mutex; pulsed every 60 s; stale if older than 120 s

## Formal Specification

`spec/Muninn.agda` (with sub-modules in `spec/Muninn/`) is a type-checked Agda specification. Key invariants it formalises and that the Rust code must maintain:

- **`ValidChunk`** — no empty-content chunks (enforced in `pipeline.rs`)
- **`ValidStoredEmbedding`** — embedding length must equal `repo.embedding_dim`; mismatch is a hard error
- **`BatchOutcome`** — a totally-failed batch must NOT advance repo to `Indexed` state
- **`DimFrozen`** — embedding dimension is frozen at registration; switching backends requires `muninn remove` + `muninn add`
- **`IsolatedGraph`** — chunks must be written to DB before symbols can reference them via `chunk_id`
- **`UniqueRepoPaths`** — enforced by `UNIQUE` constraint on `repos.path`
- **`Concurrency` / heartbeat mutex** — only one indexer may hold the lock per repo at a time; stale lock threshold is 120 s

When the spec and implementation diverge, use the `spec-reconcile` or `spec-audit` skills to audit and fix discrepancies systematically.

## Configuration

- Global config: `~/.config/muninn/config.toml` — created with defaults on first run
- Per-repo marker: `<repo-root>/.muninn.toml` — all sections optional; absent fields inherit from global
- Password: read from `~/.pgpass`; never stored in config files

## Key Conventions

- `EffectiveConfig::merge(global, repo_cfg, dir_name)` is the single source of truth for runtime config
- `repo_resolver::find_repo_root` walks up looking for `.muninn.toml` (note leading dot)
- Use `store::notify_repos_changed` after any mutation to `repos` so the daemon picks up changes promptly
- Embedding backends are selected at `EffectiveConfig` time; `make_backend(&eff.embeddings)` returns the correct implementation
- `graph` module uses Apache AGE Cypher via the `age_cypher_wrapper` SQL function (migration 008)
