# Configuration reference

## Overview

muninn uses two configuration files:

| File | Scope | Created by |
|------|-------|-----------|
| `~/.config/muninn/config.toml` | Global defaults for all repos | `muninn init` |
| `<repo-root>/.muninn.toml` | Per-repo overrides | `muninn add` / `muninn config set --repo <path>` |

When both files exist, the per-repo file overrides settings section by section. If `.muninn.toml` has an `[embeddings]` section, it completely replaces the global `[embeddings]`. Sections not present in `.muninn.toml` inherit from the global config. Individual keys are not merged within a section: if you override `[embeddings]`, all required keys in that section must be present.

The global config file may contain API keys. `muninn init` (and `muninn config set --global`) set its permissions to `0600` (owner read/write only) automatically.

---

## Minimal working examples

**Local backend (no API key required):**

```toml
[database]
host   = "localhost"
port   = 5432
dbname = "muninn"
user   = "alice"

[embeddings]
backend    = "local"
model      = "potion-base-32M"
batch_size = 64

[watcher]
debounce_ms = 300
```

**Voyage AI backend:**

```toml
[database]
host   = "localhost"
port   = 5432
dbname = "muninn"
user   = "alice"

[embeddings]
backend    = "voyage"
model      = "voyage-code-3"
api_key    = "pa-..."
batch_size = 64

[watcher]
debounce_ms = 300
```

The `[watcher]`, `[mcp]`, and `[mcp.logging]` sections are optional and shown above at their defaults — they can be omitted entirely.

---

## `~/.config/muninn/config.toml` reference

### `[database]`

| Key | Type | Default | Description |
|-----|------|---------|-------------|
| `host` | string | `"localhost"` | PostgreSQL hostname, IP address, or Unix socket directory |
| `port` | integer | `5432` | PostgreSQL port |
| `dbname` | string | `"muninn"` | Database name |
| `user` | string | current OS user | PostgreSQL role name |
| `dsn_override` | string | — | Full connection URI (e.g. `postgresql://alice@localhost:5432/muninn`). When set, `host`/`port`/`dbname`/`user` are ignored for routing, but SSL and pool settings still apply. |
| `ssl_mode` | string | — | `disable` \| `allow` \| `prefer` \| `require` \| `verify-ca` \| `verify-full` |
| `ssl_root_cert` | string | — | Path to PEM CA bundle for server certificate verification (required for `verify-ca` / `verify-full`) |
| `ssl_client_cert` | string | — | Path to PEM client certificate (mutual TLS) |
| `ssl_client_key` | string | — | Path to PEM client private key (mutual TLS) |
| `max_connections` | integer | `10` | Connection pool size |
| `connect_timeout` | integer | — | Seconds to wait for a connection before giving up; omit for no timeout |
| `application_name` | string | — | Name shown in the database's active connections view |

**Password:** muninn never stores a password in config. Add a line to `~/.pgpass` — see `docs/own-database.md` for details.

**Unix socket connections:** set `host` to the socket directory (e.g. `host = "/var/run/postgresql"`).

### `[embeddings]`

| Key | Type | Default | Description |
|-----|------|---------|-------------|
| `backend` | string | `"voyage"` | `voyage` \| `openai` \| `local` |
| `model` | string | `"voyage-code-3"` | Model name passed to the API or loaded locally |
| `api_key` | string | — | API key; required for `voyage` and `openai` backends |
| `cache_dir` | string | — | Directory for local model weights (`local` backend only); defaults to a platform cache directory |
| `batch_size` | integer | `64` | Number of text chunks sent per request; reduce if you hit rate limits |

**Backend reference:**

| Backend | Model | Dims | API key |
|---------|-------|------|---------|
| `local` | `potion-base-32M` | 512 | None needed |
| `voyage` | `voyage-code-3` | 1024 | [dash.voyageai.com](https://dash.voyageai.com) |
| `openai` | `text-embedding-3-small` | 1536 | [platform.openai.com](https://platform.openai.com) |

**Embedding dimension lock:** The embedding dimension is fixed when you run `muninn add`. Changing the backend or model after indexing requires removing and re-adding the repo:

```bash
muninn remove /path/to/repo
muninn add    /path/to/repo
```

### `[watcher]`

| Key | Type | Default | Description |
|-----|------|---------|-------------|
| `debounce_ms` | integer | `300` | Milliseconds to wait after the last file-change event before re-indexing. Increase (e.g. `2000`) if you see excessive re-indexing during large rebases or when editors write many small saves. |

### `[index]`

muninn indexes **everything** under a repo root by default — including files that `.gitignore` normally hides (`node_modules`, build output, dotfiles), because gitignored files are often worth searching. The only automatic exclusions are `.git/`, binary files (detected by a null byte), and files larger than 10 MiB.

| Key | Type | Default | Description |
|-----|------|---------|-------------|
| `exclude` | array of strings | `[]` | Glob patterns (relative to the repo root) to exclude from indexing. Gitignore-style syntax. Example: `exclude = ["target/", "dist/", "**/*.min.js"]`. |

### `[mcp]`

| Key | Type | Default | Description |
|-----|------|---------|-------------|
| `record_usage` | bool | `true` | Record MCP tool call counts — visible via `muninn usage` |

### `[mcp.logging]`

| Key | Type | Default | Description |
|-----|------|---------|-------------|
| `enabled` | bool | `true` | Write a structured log file for each MCP session |
| `dir` | string | `"~/.local/state/muninn/mcp"` | Directory for log files (`~` is expanded) |
| `retention_days` | integer | `7` | Log files older than this are deleted at the next prune |
| `prune_interval_hours` | integer | `24` | How often `muninn-mcp` checks for and deletes old log files |

---

## Per-repo `.muninn.toml` reference

`.muninn.toml` lives at the repo root. Its presence marks the directory as a muninn repo — `muninn-mcp` walks up from the current working directory to find it. If this file is missing, `muninn-mcp` cannot resolve the repo from a `cwd` argument.

All sections are optional. An empty file is valid and inherits everything from the global config.

Overridable sections: `[database]`, `[embeddings]`, `[watcher]`, `[index]`. The `[mcp]` section cannot be overridden per-repo.

**Top-level key:** `repo_name` — the display name shown in `muninn status`. Defaults to the directory name.

```toml
# repo_name = "my-project"

# [embeddings]
# Override to use a different backend for this repo.
# WARNING: changing backend requires: muninn remove <path> && muninn add <path>
# backend    = "voyage"
# model      = "voyage-code-3"
# api_key    = "pa-..."
# batch_size = 64

# [watcher]
# debounce_ms = 300

# [index]
# Exclude paths from indexing (everything is indexed by default).
# exclude = ["target/", "dist/", "**/*.min.js"]
```

**Embedding dimension lock:** If you try to change the embedding backend in `.muninn.toml` after the first index, `muninn config set --repo <path>` (or `config edit --repo <path>`) will reject it. Remove and re-add the repo to switch backends.

**Unknown keys are errors.** All config structs reject unknown TOML keys. A typo in a key name is reported immediately, not silently ignored.
