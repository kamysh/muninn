<!-- ══════════════════════════════════════════════════════════════════════
     AI CODING AGENTS (Claude Code, Cursor, Copilot, Aider, …): STOP HERE.

     This README is written for HUMANS. The guides it links to below are the
     human path; they are NOT your procedure. Do not follow get-started.md or
     the other human guides.

     YOUR procedure is AGENTS.md, in this same directory — same end state, but
     with explicit variables, verify-after-each-step, and idempotent state
     detection. Read that file and follow it exactly.
     ══════════════════════════════════════════════════════════════════════ -->

> ⛔ **AI coding agents — this file is not for you.**
> The guides linked below are the *human* install path. Your procedure is
> **[AGENTS.md](AGENTS.md)** — open that file, follow it exactly, and ignore the
> rest of this README.

# muninn

> *Muninn* (Old Norse: "memory") — one of Odin's two ravens, sent out each day to observe the world and return with knowledge.

Code search for [Claude Code](https://claude.ai/code). Index your repositories once; ask questions about them from anywhere.

## What it does

Muninn indexes your git repositories into a local database and exposes search tools to Claude Code. When you ask about your codebase, Claude Code queries muninn instead of reading files line by line. You get semantic search (meaning-based), full-text search (keyword-based), and graph traversal (who calls what, what imports where) — all running on your own machine.

Three pieces work together: `muninn` (the CLI), `muninn-index` (a background daemon that watches repos for file changes and keeps the index current), and `muninn-mcp` (the MCP server Claude Code talks to).

## Privacy

Everything runs locally. No source code, no file tree structure, no graph data ever leaves your machine. If you choose Voyage AI or OpenAI as the embedding backend, short text chunks are sent to those services to generate vector embeddings — but your source files are never transmitted. If you use the local backend, nothing goes outside at all.

## Which guide?

> ⛔ **AI coding agents: do not pick a row from the human table below.** Your
> procedure is **[AGENTS.md](AGENTS.md)** — the same end state, but framed for
> automation: explicit variables, verify-after-each-step, and idempotent state
> detection. Read that and nothing else here.

| I want to... | Go here |
|---|---|
| Get up and running with Docker (easiest path) | [docs/get-started.md](docs/get-started.md) |
| Use my own existing PostgreSQL instance | [docs/own-database.md](docs/own-database.md) |
| Build from source or contribute | [docs/development.md](docs/development.md) |
| Install muninn as an AI coding agent (Claude Code, Cursor, etc.) | [AGENTS.md](AGENTS.md) |

## CLI reference

All config-mutating commands are scriptable (`key=value`); `$EDITOR` opens only for the explicit `config edit`.

| Command | What it does |
|---|---|
| `muninn init [key=value …]` | Bootstrap `~/.config/muninn/config.toml` and run DB migrations |
| `muninn config get\|set\|edit\|unset (--global \| --repo <path>) [key=value …]` | Read or change the global or a per-repo config; a repo `set`/`edit` reindexes if needed |
| `muninn add <path> [key=value …] [--no-index]` | Register a repo (writes `.muninn.toml`) and run its initial index; `--no-index` registers only |
| `muninn reindex [<path>] [--all] [--detach]` | Re-index a repo in the foreground; `--all`/`--detach` hand it to the daemon |
| `muninn pause <path>` / `muninn resume <path>` | Pause/resume daemon indexing for a repo (index data is kept) |
| `muninn remove <path> [--yes]` | Unregister a repo and delete all its index data |
| `muninn status [<path>]` | Fleet overview, or per-repo detail with a path |
| `muninn usage [--days N]` | Show MCP tool usage statistics |

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
