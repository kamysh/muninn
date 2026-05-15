# muninn

> *Muninn* (Old Norse: "memory") — one of Odin's two ravens, sent out each day to observe the world and return with knowledge.

Full-text, semantic (vector), and structural (graph) code search for [Claude Code](https://claude.ai/code) — and any other MCP client. Index your repositories once; query them from any AI assistant.

## Features

- **Semantic search** — pgvector cosine similarity over code embeddings (Voyage AI, OpenAI, or local ONNX)
- **Full-text search** — PostgreSQL tsvector for keyword and identifier search
- **Structural search** — Apache AGE graph traversal: find callers, callees, imports, inheritors
- **Hybrid search** — semantic + full-text results merged with Reciprocal Rank Fusion
- **Knowledge store** — record and search freeform notes anchored to your codebase
- **Incremental indexing** — daemon watches for file changes and re-indexes incrementally
- **Distributed lock** — safe concurrent operation; only one indexer holds the lock per repo at a time
- **Formal specification** — core invariants type-checked in Agda

## Prerequisites

- **Nix** (with flakes enabled) — provides Rust, Agda, and all build dependencies
- **PostgreSQL 16+** with:
  - [pgvector](https://github.com/pgvector/pgvector) — vector similarity search
  - [Apache AGE](https://age.apache.org/) — property graph queries
- An embedding API key (**Voyage AI** or **OpenAI**), or use the bundled `local` ONNX backend

### Database setup

```bash
createdb muninn
psql muninn -c 'CREATE EXTENSION IF NOT EXISTS vector;'
psql muninn -c 'CREATE EXTENSION IF NOT EXISTS age;'
nix develop --command sqlx migrate run
```

## Installation

### Option A: Nix profile (recommended)

```bash
# From a local checkout
nix profile install .

# Register the MCP server with Claude Code
claude mcp add --scope user muninn ~/.nix-profile/bin/muninn-mcp
```

The Nix profile is a GC root — the binaries' shared library dependencies in the Nix store will not be garbage-collected. Do **not** use `nix build` + manual copy; those binaries reference store paths that `nix store gc` will remove.

### Option B: Static binary

A fully self-contained binary with no Nix store runtime dependencies:

```bash
nix build .#muninn-static
cp result/bin/muninn* ~/.local/bin/
claude mcp add --scope user muninn ~/.local/bin/muninn-mcp
```

### Option C: install.sh

```bash
git clone https://github.com/YOUR_ORG/muninn
cd muninn
./install.sh    # nix profile install + registers MCP with Claude Code
```

### Systemd service (optional)

```bash
cp muninn-index.service ~/.config/systemd/user/
systemctl --user daemon-reload
systemctl --user enable --now muninn-index
```

## Quick start

```bash
# 1. Bootstrap global config (opens $EDITOR — fill in your API key and DB user)
muninn config init

# 2. Add a repository (configures + indexes in one step)
muninn add /path/to/your/repo

# 3. Start the daemon (watches for file changes, reindexes incrementally)
systemctl --user start muninn-index

# Claude Code now has muninn search tools available
```

## Configuration

### Global config: `~/.config/muninn/config.toml`

Created by `muninn config init`. All settings have defaults; only `database.user` and `embeddings.api_key` must be filled in.

```toml
[database]
host   = "localhost"
port   = 5432
dbname = "muninn"
user   = "alice"           # your PostgreSQL username
# Password: add to ~/.pgpass — localhost:5432:muninn:alice:yourpassword
# (chmod 600 ~/.pgpass)

# Optional:
# ssl_mode        = "prefer"   # disable | allow | prefer | require | verify-ca | verify-full
# ssl_root_cert   = "/path/to/ca.pem"
# ssl_client_cert = "/path/to/client-cert.pem"
# ssl_client_key  = "/path/to/client-key.pem"
# max_connections = 10
# connect_timeout = 30
# dsn_override    = "postgresql://alice@localhost/muninn"  # bypasses host/port/dbname/user

[embeddings]
backend    = "voyage"          # voyage | openai | local
model      = "voyage-code-3"
api_key    = "pa-..."          # Voyage AI or OpenAI key; omit for local backend
# cache_dir  = "/path/to/cache"  # local backend: ONNX model cache
batch_size = 64

[watcher]
debounce_ms = 300              # ms to wait after last file change before reindexing

[mcp]
record_usage = true            # write aggregate usage stats to the database

[mcp.logging]
enabled              = true
dir                  = "~/.local/state/muninn/mcp"
retention_days       = 7
prune_interval_hours = 24
```

**Embedding backends:**

| Backend | Model | Dims | Notes |
|---------|-------|------|-------|
| `voyage` | `voyage-code-3` | 1024 | Best quality for code; [API key](https://dash.voyageai.com) required |
| `openai` | `text-embedding-3-small` | 1536 | [API key](https://platform.openai.com) required |
| `local` | BGE-Base-EN-v1.5 | 768 | No key needed; ~200 MB ONNX download on first use |

> **DimFrozen**: the embedding dimension is fixed at `muninn add` time. To switch backends, run `muninn remove <path>` then `muninn add <path>` again.

### Per-repo config: `<repo-root>/.muninn.toml`

The presence of this file marks a directory as a muninn repo root. An empty file is valid — all settings inherit from the global config. `muninn add` creates it and opens it in `$EDITOR`.

```toml
# repo_name = "my-project"   # display name; default: directory name

# [database]
# host   = "db.internal"     # use a different database for this repo

# [embeddings]
# backend    = "openai"
# model      = "text-embedding-3-small"
# api_key    = "sk-..."

# [watcher]
# debounce_ms = 500
```

## CLI reference

```
muninn add <path>           Register a repo, configure it, and run the initial index
muninn configure <path>     Edit .muninn.toml; validates and reindexes if content changed
muninn remove <path>        Delete .muninn.toml and all index data
muninn list                 List registered repos and their index status
muninn reindex [<path>]     Signal the daemon to reindex (--all for all repos)
muninn status               Show registered repos and index state
muninn stats [--days N]     Show MCP tool usage statistics
muninn config init          Create ~/.config/muninn/config.toml and open it for editing
```

### `muninn add <path>`

Opens `$EDITOR` with a template `.muninn.toml` (in a temp file). Validates the config on save — loops back if there are errors. Once valid, writes the real `.muninn.toml`, registers the repo in the database, and runs a foreground index with a progress bar:

```
Indexing /path/to/repo (1024 dims, voyage)…
  [   1/4231] src/main.rs
  [   2/4231] src/lib.rs
  …
Done in 312.4s.
```

Fails with a clear message if the repo is already registered — use `muninn configure` to change the config.

### `muninn configure <path>`

Opens the existing `.muninn.toml` in a temp file. Validates on save (including the DimFrozen check — embedding dimension cannot change). If the content changed, writes the real file and runs a foreground reindex. If the content is identical, prints "No changes." and exits.

### `muninn remove <path>`

Prompts for confirmation, then deletes `.muninn.toml` and drops all index data (chunks, embeddings, graph nodes) from the database. Refuses to proceed if a live indexing lock is held.

## How it works

### Indexer daemon (`muninn-index`)

The daemon discovers repos from the `repos` database table — it does not scan the filesystem. When `muninn add` or `muninn remove` registers or removes a repo, it sends a `NOTIFY muninn_repos_changed` PostgreSQL notification; the daemon receives this and updates its watcher set within milliseconds. A 60-second fallback poll handles any missed notifications.

For each repo the daemon either watches for file changes (`notify` crate) or spawns a full reindex task. A distributed lock (`indexing_heartbeat` column, pulsed every 60 s, stale after 120 s) ensures only one indexer operates on a repo at a time — even if multiple daemon instances are running.

### Indexing pipeline

For each file:
1. **Parse** — tree-sitter extracts symbols and call graph edges (Rust, Python, JavaScript, TypeScript)
2. **Chunk** — split into chunks at symbol boundaries
3. **Embed** — generate embeddings via the configured backend
4. **Store** — write chunks and embeddings to a per-repo PostgreSQL table; write symbol graph to Apache AGE

### MCP server (`muninn-mcp`)

Exposes 8 tools to Claude Code via stdio JSON-RPC:

| Tool | Description |
|------|-------------|
| `search_hybrid` | Semantic + full-text with RRF ranking |
| `search_fulltext` | PostgreSQL tsvector keyword search |
| `search_semantic` | pgvector cosine similarity |
| `search_structural` | Graph traversal — callers, callees, imports, inheritors |
| `record_knowledge` | Store a freeform note anchored to a repo |
| `search_knowledge` | Hybrid search over knowledge notes |
| `list_knowledge` | List knowledge notes for a repo |
| `delete_knowledge` | Delete a knowledge note |

Repo resolution: tools accept `repo` (explicit path) or `cwd` (walks up to the nearest `.muninn.toml`). MCP usage is logged to `mcp.logging.dir` and aggregate counts stored in the database (`muninn stats`).

## Architecture

```
~/.config/muninn/config.toml          Global defaults
         │
         ├── muninn-index              Daemon: watch, parse, embed, index
         │     ├── tree-sitter         Source parsing (Rust / Python / JS / TS)
         │     ├── Voyage AI / OpenAI  Embedding generation
         │     └── PostgreSQL          Chunks + pgvector + Apache AGE graph
         │
         ├── muninn-mcp                MCP server (stdio JSON-RPC)
         │     └── Claude Code         Calls search + knowledge tools
         │
         └── muninn                    CLI (add, configure, remove, reindex, …)

<repo>/.muninn.toml                   Per-repo overrides (optional)
```

Four-crate Rust workspace:

```
crates/
  core/       — muninn_core library (shared by all binaries)
  indexer/    — muninn-index daemon
  mcp/        — muninn-mcp MCP server
  cli/        — muninn CLI
```

## Formal specification

`spec/Muninn.agda` — Agda type-checked specification covering types, indexing state machine, validity predicates, query semantics, embedding dimension invariants, and config merge semantics.

```bash
cd spec && nix develop --command agda Muninn.agda
```

Key invariants the Rust implementation maintains:

- **ValidChunk** — no empty-content chunks
- **ValidStoredEmbedding** — embedding length must equal `repo.embedding_dim`
- **BatchOutcome** — a fully-failed batch does not advance the repo to `Indexed`
- **DimFrozen** — embedding dimension is fixed at registration time
- **IsolatedGraph** — chunks are written to the DB before symbols reference them
- **UniqueRepoPaths** — enforced by a `UNIQUE` constraint on `repos.path`
- **Concurrency / heartbeat mutex** — one indexer per repo; stale lock threshold 120 s

## License

Apache License 2.0 — see [LICENSE](LICENSE).
