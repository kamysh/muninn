# muninn

> *Muninn* (Old Norse: "memory") — one of Odin's two ravens, sent out each day to observe the world and return with knowledge.

Code search for [Claude Code](https://claude.ai/code). Index your repositories once; ask questions about them from anywhere.

## What it does

Muninn indexes your git repositories into a local database and exposes search tools to Claude Code. When you ask about your codebase, Claude Code queries muninn instead of reading files line by line. You get semantic search (meaning-based), full-text search (keyword-based), and graph traversal (who calls what, what imports where) — all running on your own machine.

Three pieces work together: `muninn` (the CLI), `muninn-index` (a background daemon that watches repos for file changes and keeps the index current), and `muninn-mcp` (the MCP server Claude Code talks to).

## Privacy

Everything runs locally. No source code, no file tree structure, no graph data ever leaves your machine. If you choose Voyage AI or OpenAI as the embedding backend, short text chunks are sent to those services to generate vector embeddings — but your source files are never transmitted. If you use the local backend, nothing goes outside at all.

## Which guide?

| I want to... | Go here |
|---|---|
| Get up and running with Docker (easiest path) | [docs/get-started.md](docs/get-started.md) |
| Use my own existing PostgreSQL instance | [docs/own-database.md](docs/own-database.md) |
| Build from source or contribute | [docs/development.md](docs/development.md) |
| Install muninn as an AI coding agent (Claude Code, Cursor, etc.) | [AGENTS.md](AGENTS.md) |

## CLI reference

| Command | What it does |
|---|---|
| `muninn config` | Create or edit `~/.config/muninn/config.toml`; validates and applies DB schema on save |
| `muninn add <path>` | Register a repo, open editor for per-repo config, run initial index |
| `muninn configure <path>` | Edit per-repo config; reindexes if anything changed |
| `muninn remove <path>` | Remove a repo from the index and delete all its data |
| `muninn list` | List registered repos and index status |
| `muninn reindex [<path>] [--all]` | Mark repo(s) for re-indexing by the daemon |
| `muninn status` | Show repos and current index state |
| `muninn stats [--days N]` | Show MCP tool usage statistics |

## MCP tools

Once muninn is connected to Claude Code, these tools are available:

| Tool | What it does |
|---|---|
| `search_hybrid` | Semantic + full-text search with RRF ranking |
| `search_fulltext` | Keyword search |
| `search_semantic` | Vector similarity search |
| `search_structural` | Graph traversal: callers, callees, imports, inheritors |
| `record_knowledge` | Store a note anchored to your codebase |
| `search_knowledge` | Search over stored notes |
| `delete_knowledge` | Remove a stored note |
| `list_knowledge` | List stored notes |

## Further reading

- [docs/upgrading.md](docs/upgrading.md) — upgrade binaries and apply migrations
- [docs/configuration.md](docs/configuration.md) — full config file reference
- [docs/uninstall.md](docs/uninstall.md) — full removal

## License

Apache License 2.0 — see [LICENSE](LICENSE).
Contributions are subject to the [Contributor License Agreement](CLA.md).
