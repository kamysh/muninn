# muninn

> *Muninn* (Old Norse: "memory") — one of Odin's two ravens, sent out each day to observe the world and return with knowledge.

Full-text, semantic, and structural (graph) code search for [Claude Code](https://claude.ai/code) and any other MCP client. Index your repositories once; search them from any AI assistant.

## How it works

Three components work together:

- **`muninn-index`** — daemon that watches your repos for changes and indexes them into PostgreSQL
- **`muninn-mcp`** — MCP server that exposes search tools to Claude Code (or any MCP client)
- **`muninn`** — CLI to register repos and manage the index

## Prerequisites

- [Docker](https://docs.docker.com/get-docker/) — for the database
- [Claude Code](https://claude.ai/code) — or any other MCP client

## Installation

### 1. Start the database

```bash
docker run -d \
  --name muninn-postgres \
  --restart always \
  -e POSTGRES_PASSWORD=changeme \
  -p 127.0.0.1:5432:5432 \
  -v muninn_data:/var/lib/postgresql/data \
  kamysh/postgres-ai:latest
```

This image ships with [pgvector](https://github.com/pgvector/pgvector) and [Apache AGE](https://age.apache.org/) pre-installed and pre-configured.

### 2. Download muninn binaries

Pick the archive for your platform from the [latest release](https://github.com/kamysh/muninn/releases/latest):

| Platform | File |
|----------|------|
| Linux x86_64 | `muninn-linux-amd64.tar.gz` |
| Linux ARM64 | `muninn-linux-arm64.tar.gz` |
| macOS Apple Silicon | `muninn-darwin-arm64.tar.gz` |
| macOS Intel | `muninn-darwin-amd64.tar.gz` |

```bash
# Example for Linux x86_64
curl -L https://github.com/kamysh/muninn/releases/latest/download/muninn-linux-amd64.tar.gz \
  | tar -xz -C ~/.local/bin
chmod +x ~/.local/bin/muninn ~/.local/bin/muninn-index ~/.local/bin/muninn-mcp
```

### 3. Configure

```bash
muninn config
```

This creates `~/.config/muninn/config.toml` (or opens the existing one) in `$EDITOR`. Fill in your database credentials and embedding API key (see below), then save. When you close the editor, muninn validates the config, connects to the database, and applies all schema migrations automatically — no `sqlx-cli` or separate migration step required.

**Embedding backends** — pick one:

| Backend | Model | API key |
|---------|-------|---------|
| [Voyage AI](https://www.voyageai.com) | `voyage-code-3` | [dash.voyageai.com](https://dash.voyageai.com) |
| [OpenAI](https://platform.openai.com) | `text-embedding-3-small` | [platform.openai.com](https://platform.openai.com) |
| Local (no key) | BGE-Base-EN-v1.5 | — |

### 4. Start the indexer daemon

```bash
muninn-index &
```

Or as a systemd user service:

```bash
cp muninn-index.service ~/.config/systemd/user/
systemctl --user enable --now muninn-index
```

### 5. Add Claude Code integration

```bash
claude mcp add --scope user muninn ~/.local/bin/muninn-mcp
```

### 6. Add a repository

```bash
muninn add /path/to/your/repo
```

This opens your editor to configure the repo, then indexes it in the foreground. The daemon takes over afterward, watching for file changes.

## CLI reference

```
muninn add <path>           Register a repo, configure it, and run the initial index
muninn configure <path>     Edit .muninn.toml; reindexes if content changed
muninn remove <path>        Delete .muninn.toml and all index data
muninn list                 List registered repos and their index status
muninn reindex [<path>]     Signal the daemon to reindex (--all for all repos)
muninn status               Show registered repos and index state
muninn stats [--days N]     Show MCP tool usage statistics
muninn config               Create or edit ~/.config/muninn/config.toml; applies DB migrations
```

## MCP search tools

Once connected, Claude Code has access to:

| Tool | Description |
|------|-------------|
| `search_hybrid` | Semantic + full-text search with RRF ranking |
| `search_fulltext` | PostgreSQL keyword search |
| `search_semantic` | Vector similarity search |
| `search_structural` | Graph traversal — callers, callees, imports, inheritors |
| `record_knowledge` | Store a note anchored to your codebase |
| `search_knowledge` | Search over stored notes |

## Further reading

- [Building from source / development setup](docs/development.md)
- [Configuration reference](docs/configuration.md)

## License

Apache License 2.0 — see [LICENSE](LICENSE).
Contributions are subject to the [Contributor License Agreement](CLA.md).
