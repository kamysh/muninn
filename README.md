# muninn

Indexed code search for Claude Code — full-text, semantic (vector), and structural (graph) search over your repositories.

## Prerequisites

- **Nix** (with flakes enabled) — provides Rust, Agda, and all build dependencies
- **PostgreSQL 16+** with extensions:
  - [pgvector](https://github.com/pgvector/pgvector) — vector similarity search
  - [Apache AGE](https://age.apache.org/) — graph queries for structural search
- A **Voyage AI** or **OpenAI** API key (for embeddings), or use the `local` backend

### Database setup

```bash
# Create the database
createdb muninn

# Enable required extensions (run as superuser or with CREATE EXTENSION privilege)
psql muninn -c 'CREATE EXTENSION IF NOT EXISTS vector;'
psql muninn -c 'CREATE EXTENSION IF NOT EXISTS age;'

# Run migrations
nix develop --command sqlx migrate run
```

## Installation

### Option A: Nix profile (recommended)

```bash
# From a local checkout — installs into ~/.nix-profile/bin/
nix profile install .

# Or directly from the repository
nix profile install github:your-org/muninn

# Register MCP server with Claude Code
claude mcp add muninn ~/.nix-profile/bin/muninn-mcp
```

The Nix profile is a GC root, so the shared libraries in the Nix store are kept alive. Do not use `nix build` + manual copy — the copied binaries reference Nix store paths that will be collected by `nix store gc`.

### Option B: Static build

For a fully self-contained binary with no Nix store runtime dependencies:

```bash
nix build .#muninn-static
# Binaries in ./result/bin/ — safe to copy anywhere
cp result/bin/muninn* ~/.local/bin/
claude mcp add muninn ~/.local/bin/muninn-mcp
```

### Option C: install.sh

```bash
git clone <repo-url> muninn
cd muninn
./install.sh    # nix profile install + registers MCP
```

### Systemd service (optional)

To run the indexer as a background daemon:

```bash
# Install the service file
cp muninn-index.service ~/.config/systemd/user/
systemctl --user daemon-reload

# Enable and start
systemctl --user enable --now muninn-index

# Check status
systemctl --user status muninn-index
```

## Configuration

### Global config: `~/.config/muninn/config.toml`

Created automatically with defaults on first run. All settings are fully populated — no optional fields.

```toml
[database]
host   = "localhost"
port   = 5432
dbname = "muninn"
user   = "your_username"
# Password is read from ~/.pgpass (host:port:dbname:user:password)
# dsn_override = "postgresql://pooler/muninn"  # escape hatch: use this DSN verbatim

[embeddings]
backend    = "voyage"              # voyage | openai | local
model      = "voyage-code-3"
api_key    = "pa-..."              # Voyage AI or OpenAI API key
cache_dir  = "/path/to/cache"      # local-only; ONNX model cache
batch_size = 64

[watcher]
debounce_ms = 300                  # file change debounce (milliseconds)

[indexer]
scan_roots = ["/home/you/projects", "/home/you/work"]
scan_depth = 3                     # max directory depth to scan for muninn.toml
include_hidden = false             # include hidden directories when scanning

[mcp]
record_usage = true                # write aggregate usage stats into the database

[mcp.logging]
enabled = true
dir = "~/.local/state/muninn/mcp"  # log directory (tilde expanded)
retention_days = 7                 # prune logs older than this
prune_interval_hours = 24          # prune cadence
```

### Per-repo config: `<repo-root>/muninn.toml`

An empty `muninn.toml` file marks a directory as a muninn repo root. All sections are optional — absent fields inherit from the global config.

```toml
# repo_name = "my-project"        # override repo name (default: directory name)

# [database]
# host = "db.internal"            # use a different database for this repo

# [embeddings]
# backend = "openai"              # use a different embedding backend
# model   = "text-embedding-3-small"
# api_key = "sk-..."
# cache_dir = "/path/to/cache"    # local-only

# [watcher]
# debounce_ms = 500
```

## Usage

### Register and index a repository

```bash
# Step 1: create muninn.toml and edit it
muninn register /path/to/your/repo

# Step 2: run the initial index (foreground, shows progress)
muninn index /path/to/your/repo
```

`register` creates `muninn.toml` and opens it in `$EDITOR`. Edit the file (set API key, choose backend, etc.) before indexing.

`index` runs the full indexing pipeline in the foreground:
```
Indexing /path/to/repo (1024 dims, voyage)…
  [   1/4231] src/main.rs
  [   2/4231] src/lib.rs
  ...
Done in 312.4s.
Start or restart muninn-index to begin watching for changes.
```

After the initial index, `muninn-index` daemon takes over — it watches for file changes and re-indexes incrementally.

### Unregister a repository

```bash
muninn unregister /path/to/your/repo
```

Deletes `muninn.toml` and removes all index data (chunks, embeddings, graph) from the database.

### List registered repos

```bash
muninn list
```

### Force reindex

```bash
muninn reindex /path/to/your/repo   # single repo
muninn reindex --all                 # all repos
```

Marks repos for reindex. Restart `muninn-index` to apply.

### Check status

```bash
muninn status
```

### MCP usage stats

```bash
muninn stats --days 30
```

## How it works

### Indexer daemon (`muninn-index`)

1. Scans each directory in `indexer.scan_roots` (up to `scan_depth` levels) for `muninn.toml` files
2. For each discovered repo:
   - Loads per-repo config, merges with global defaults
   - Parses source files with tree-sitter (Rust, Python, JavaScript, TypeScript)
   - Splits files into chunks by symbol boundaries
   - Generates embeddings via the configured backend
   - Stores chunks, embeddings, and symbol graph in PostgreSQL
3. Watches for file changes and re-indexes incrementally

### MCP server (`muninn-mcp`)

Exposes four search tools to Claude Code:

| Tool | Description |
|------|-------------|
| `search_hybrid` | Combined semantic + full-text search with RRF ranking |
| `search_fulltext` | Keyword search using PostgreSQL tsvector |
| `search_semantic` | Vector similarity search using pgvector |
| `search_structural` | Graph traversal — find callers, callees, imports, inheritors |

The MCP server resolves which repo to search by walking up from the current working directory to the nearest `muninn.toml`. You can also specify a repo path explicitly.
If logging is enabled, it writes rotating logs to `mcp.logging.dir` and prunes them periodically. Aggregate usage stats are stored in the database and can be viewed with `muninn stats`.

### CLI (`muninn`)

Manages repo registration and index lifecycle. Does not perform indexing itself — that's the daemon's job.

## Architecture

```
~/.config/muninn/config.toml          Global defaults
         │
         ├── muninn-index              Daemon: scan, parse, embed, index
         │     ├── tree-sitter         Source parsing (Rust/Python/JS/TS)
         │     ├── Voyage AI / OpenAI  Embedding generation
         │     └── PostgreSQL          Storage (pgvector + AGE + FTS)
         │
         ├── muninn-mcp                MCP server (stdio JSON-RPC)
         │     └── Claude Code         Calls search tools
         │
         └── muninn                    CLI (register, unregister, list, reindex)

<repo>/muninn.toml                     Per-repo overrides (optional)
```

## Formal specification

`spec/Muninn.agda` — Agda specification covering core types, indexing state machine, validity predicates, query semantics, embedding dimensions, and config merge semantics.

```bash
# Type-check the spec (from the spec/ directory)
cd spec && nix develop --command agda Muninn.agda
```

See [spec/README.md](spec/README.md) for details.
