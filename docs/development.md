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
- `ORT_DYLIB_PATH` — path to the ONNX runtime for the local embedding backend

## Database setup

```bash
createdb muninn_dev
sqlx migrate run
```

## Common commands

```bash
# Build
cargo build
cargo build --release

# Test
cargo nextest run
cargo nextest run -p muninn_core          # single crate
cargo nextest run -- <test_name>          # single test

# Lint and format
cargo clippy -- -D warnings
cargo fmt

# Watch mode
cargo watch -x build

# After changing SQL queries, regenerate the offline query cache
cargo sqlx prepare --workspace

# Database migrations
sqlx migrate run      # apply pending
sqlx migrate revert   # roll back one
```

## Building distributable binaries

```bash
# Dynamically linked — install via nix profile, do not copy the binary directly
nix build

# Fully static (Linux: musl; macOS: links only against libSystem)
# Safe to copy anywhere, no Nix store dependencies
nix build .#muninn-static
```

Binaries appear in `result/bin/`: `muninn`, `muninn-index`, `muninn-mcp`.

## Install locally via Nix profile

```bash
nix profile install .
claude mcp add --scope user muninn ~/.nix-profile/bin/muninn-mcp
```

The Nix profile is a GC root — the binaries' shared library dependencies in the Nix store will not be garbage-collected. Do **not** use `nix build` + manual copy for the dynamically linked build.

## Formal specification

The Agda specification in `spec/Muninn.agda` type-checks the core invariants. Run it without `--safe` (the Concurrency module has intentional postulates):

```bash
cd spec && agda Muninn.agda
```

Key invariants formalised in the spec that the Rust implementation must maintain:

- **ValidChunk** — no empty-content chunks
- **ValidStoredEmbedding** — embedding length must equal `repo.embedding_dim`
- **BatchOutcome** — a fully-failed batch does not advance the repo to `Indexed`
- **DimFrozen** — embedding dimension is fixed at `muninn add` time
- **IsolatedGraph** — chunks written to DB before symbols can reference them
- **UniqueRepoPaths** — enforced by `UNIQUE` constraint on `repos.path`
- **Concurrency / heartbeat mutex** — one indexer per repo; stale lock threshold 120 s

Use the `spec-reconcile` or `spec-audit` Claude Code skills to audit and fix spec/implementation discrepancies.

## Embedding backends

| Backend | Model | Dims | Notes |
|---------|-------|------|-------|
| `voyage` | `voyage-code-3` | 1024 | Best quality for code |
| `openai` | `text-embedding-3-small` | 1536 | |
| `local` | BGE-Base-EN-v1.5 | 768 | No API key; ONNX on CPU |

The embedding dimension is frozen at `muninn add` time (**DimFrozen**). To switch backends:

```bash
muninn remove /path/to/repo
muninn add    /path/to/repo
```

## Architecture

Four-crate Rust workspace sharing a PostgreSQL database (pgvector + Apache AGE):

```
crates/
  core/       — muninn_core library (shared by all binaries)
  indexer/    — muninn-index daemon
  mcp/        — muninn-mcp MCP server
  cli/        — muninn CLI
```

### Indexer daemon

DB-driven: discovers repos from the `repos` table, not by scanning the filesystem. Receives `NOTIFY muninn_repos_changed` when repos change, with a 60 s fallback poll. Uses a distributed lock (`indexing_heartbeat` column, pulsed every 60 s, stale after 120 s) so only one indexer operates on a repo at a time.

### Configuration

- Global: `~/.config/muninn/config.toml` — created by `muninn config`
- Per-repo: `<repo-root>/.muninn.toml` — created by `muninn add`; all sections optional
- `EffectiveConfig::merge(global, repo_cfg, dir_name)` is the single source of truth for runtime config
