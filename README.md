# ai-mem

Indexed code search for Claude Code — full-text, semantic (vector), and structural (graph) search over your repositories.

## Setup

```bash
# Enter dev shell (provides Rust, Agda, sqlx-cli)
nix develop

# Build and install
./install.sh

# Register a repository
ai-mem register /path/to/your/repo

# The indexer daemon keeps the index up to date
systemctl --user status ai-mem-index
```

## Architecture

- **ai-mem-index** — daemon: tree-sitter parsing, Voyage AI embeddings, PostgreSQL writes
- **ai-mem-mcp** — MCP server: answers Claude Code search queries
- **ai-mem** — CLI: repo registration and management
- **PostgreSQL** — pgvector (semantic) + Apache AGE (structural graph) + full-text

## Configuration

`~/.config/ai-mem/config.toml` — database DSN, embedding backend, registered repos.

## Formal specification

See `spec/AiMem.agda` — Agda specification of core types, state machine, and query semantics.