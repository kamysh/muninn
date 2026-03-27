# muninn: Indexed Search MCP Server — Design

**Date:** 2026-03-27
**Status:** Approved

---

## Overview

`muninn` is a Rust workspace providing indexed search over code repositories for Claude Code via the Model Context Protocol (MCP). It gives Claude fast, rich search across three dimensions: full-text (keyword), semantic (vector), and structural (graph/AST).

---

## Architecture

Two-process split sharing a PostgreSQL database:

```
┌─────────────────────────────────────────────────────────────┐
│  Claude Code session                                        │
│                                                             │
│  MCP client  ──────────────────►  muninn-mcp               │
│                                   (query server)           │
└─────────────────────────────────────────┬───────────────────┘
                                          │ SQL queries
                                          ▼
                                    ┌──────────────┐
                                    │  PostgreSQL  │
                                    │  pgvector    │
                                    │  AGE         │
                                    └──────┬───────┘
                                           │ SQL writes
                                    ┌──────┴───────┐
                                    │ muninn-index │
                                    │  (daemon)    │
                                    └──────┬───────┘
                                           │
                              ┌────────────┼────────────┐
                              ▼            ▼            ▼
                         tree-sitter   embeddings   file watcher
                         (parsing)     (Voyage AI   (notify/inotify)
                                        / OpenAI
                                        / local)
```

### Binaries

| Binary | Role |
|--------|------|
| `muninn-index` | Long-running daemon: file watching, parsing, embedding, index writes |
| `muninn-mcp` | MCP server: handles search queries from Claude Code |
| `muninn` | CLI: repo registration, reindex commands, status |

---

## Database Schema

### `repos` table

```sql
CREATE TABLE repos (
    id          UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    path        TEXT UNIQUE NOT NULL,
    name        TEXT NOT NULL,
    indexed_at  TIMESTAMPTZ,
    config      JSONB
);
```

### `chunks` table

```sql
CREATE TABLE chunks (
    id          UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    repo_id     UUID REFERENCES repos(id) ON DELETE CASCADE,
    file_path   TEXT NOT NULL,
    start_line  INT NOT NULL,
    end_line    INT NOT NULL,
    content     TEXT NOT NULL,
    ts_vector   TSVECTOR GENERATED ALWAYS AS (to_tsvector('english', content)) STORED,
    embedding   VECTOR(1024)
);

CREATE INDEX ON chunks USING GIN (ts_vector);
CREATE INDEX ON chunks USING hnsw (embedding vector_cosine_ops);
```

### AGE graph

Nodes: `File`, `Function`, `Class`, `Module` — each carries a `chunk_id UUID` property linking back to `chunks`.

Edges: `CALLS`, `IMPORTS`, `DEFINES`, `INHERITS_FROM`

Example Cypher query:
```cypher
MATCH (f:Function)-[:CALLS]->(g:Function {name: 'parse'})
RETURN f.name, f.file_path
```

---

## Indexing Pipeline (`muninn-index`)

### Startup

1. Load config, connect to Postgres, run migrations
2. For each registered repo: check `indexed_at` — queue full reindex if stale or absent
3. Start file watcher (`notify` crate) on all registered repo paths

### Full reindex

For each file (respecting `.gitignore` via `ignore` crate):
1. Parse with tree-sitter → extract symbols (functions, classes, imports)
2. Chunk by symbol boundaries; fall back to max-token-size splits
3. Generate embeddings in batches (default batch size: 64)
4. Upsert into `chunks` table
5. Upsert AGE graph nodes and edges for structural relationships
6. Update `repos.indexed_at`

### Incremental update (file watcher)

- **Modified/created:** delete existing chunks + AGE nodes for file, re-run full file pipeline
- **Deleted:** delete chunks + AGE nodes for file

### Concurrency

File watcher events are fed into a debounced Tokio channel (300ms debounce) to avoid thrashing on rapid saves. Embedding calls are batched and sent asynchronously.

---

## MCP Server (`muninn-mcp`)

### Transport

stdio (standard Claude Code local MCP transport)

### Tools

| Tool | Description |
|------|-------------|
| `search_semantic` | Vector similarity search — find chunks by meaning |
| `search_fulltext` | Keyword/phrase search via `ts_vector` GIN index |
| `search_structural` | Graph traversal — find symbols by relationship |
| `search_hybrid` | Semantic + fulltext merged with Reciprocal Rank Fusion |
| `index_repo` | Register + trigger immediate indexing of a repo path |
| `list_repos` | List registered repos and index status |

### Hybrid search query flow

1. Generate embedding for query (same backend as indexer)
2. Vector search (pgvector cosine, top-K×2 candidates)
3. Fulltext search (GIN ts_vector, top-K×2 candidates)
4. Merge with RRF scoring → top-K results
5. Return: `file_path`, line range, content snippet

### Structural search signature

```
search_structural(
  symbol: string,
  relation: "callers" | "callees" | "imports" | "inheritors",
  repo?: string
) → [Symbol]
```

---

## Configuration

**File:** `~/.config/muninn/config.toml`

```toml
[database]
dsn = "postgresql://localhost/muninn"

[embeddings]
backend = "voyage"   # "voyage" | "openai" | "local"
api_key = "vo-..."
model = "voyage-code-3"
batch_size = 64

[watcher]
debounce_ms = 300

[[repos]]
id = "550e8400-e29b-41d4-a716-446655440000"
path = "/home/user/projects/my-repo"
name = "my-repo"
```

### Embedding backends

| Backend | Model | Notes |
|---------|-------|-------|
| `voyage` | `voyage-code-3` | **Default.** Code-optimized, 32K context, reranking available |
| `openai` | `text-embedding-3-small/large` | General-purpose |
| `local` | configurable | Via fastembed or ollama, no API key required |

---

## CLI

```
muninn register <path> [--name <name>]   # add repo to config + trigger index
muninn unregister <path>                 # remove repo + delete its index data
muninn list                              # show repos and index status
muninn reindex <path|--all>             # force full reindex
muninn status                           # show indexer daemon status
muninn install                          # install systemd units
```

---

## Development Process

Before writing any Rust implementation code, a **formal Agda specification** must be written covering:

- Core data types and invariants
- Indexing pipeline state machine
- Query semantics
- Repo registration rules

The Agda spec lives in `spec/` and serves as the authoritative contract that the implementation must satisfy.

---

## Technology Stack

| Concern | Crate / Tool |
|---------|-------------|
| MCP protocol | `rmcp` (Rust MCP SDK) |
| Postgres client | `sqlx` |
| Vector search | `pgvector` (via sqlx) |
| Graph queries | `apache-age` / raw SQL |
| Code parsing | `tree-sitter` + language grammars |
| File watching | `notify` |
| Gitignore handling | `ignore` |
| Async runtime | `tokio` |
| Config parsing | `toml` + `serde` |
| CLI | `clap` |