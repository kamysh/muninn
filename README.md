# muninn

Indexed code search for Claude Code — full-text, semantic (vector), and structural (graph) search over your repositories.

## Setup

```bash
# Enter dev shell (provides Rust, Agda, sqlx-cli)
nix develop

# Build and install
./install.sh

# Register a repository
muninn register /path/to/your/repo

# The indexer daemon keeps the index up to date
systemctl --user status muninn-index
```

## Architecture

- **muninn-index** — daemon: tree-sitter parsing, Voyage AI embeddings, PostgreSQL writes
- **muninn-mcp** — MCP server: answers Claude Code search queries
- **muninn** — CLI: repo registration and management
- **PostgreSQL** — pgvector (semantic) + Apache AGE (structural graph) + full-text

## Configuration

`~/.config/muninn/config.toml` — database DSN, embedding backend, registered repos.

## Formal specification

See `spec/Muninn.agda` — Agda specification of core types, state machine, and query semantics.