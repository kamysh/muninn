# Config Redesign: Global + Per-Repo Design

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Replace the single global config (with an embedded repos list) with a two-layer config system: a global config for defaults and a per-repo `muninn.toml` that marks the repo root and optionally overrides any global setting.

**Architecture:** Field-level merge of global config into per-repo overrides produces an `EffectiveConfig` used by all components. The indexer discovers repos by scanning `scan_roots` for `muninn.toml` files. The MCP server resolves the repo by walking up the directory tree to the nearest `muninn.toml`.

**Tech Stack:** Rust, TOML (`toml` crate), `ignore` crate for filesystem scanning, existing `sqlx`/PostgreSQL stack.

---

## Design

### File Locations

| File | Purpose |
|------|---------|
| `~/.config/muninn/config.toml` | Global defaults — DB, embeddings, watcher, scan roots |
| `<repo-root>/muninn.toml` | Per-repo marker + optional overrides; can be empty |

### Global Config (`~/.config/muninn/config.toml`)

```toml
[database]
host   = "localhost"
port   = 5432
dbname = "muninn"
user   = "alice"
# password: not stored here — use ~/.pgpass (host:port:dbname:user:password)

[embeddings]
backend    = "voyage"        # voyage | openai | local
model      = "voyage-code-3"
api_key    = "pa-..."        # omit to use VOYAGE_API_KEY / OPENAI_API_KEY env var
batch_size = 64

[watcher]
debounce_ms = 300

[indexer]
scan_roots = ["/home/alice/projects"]
scan_depth = 5               # max directory depth to search for muninn.toml
```

The DSN is constructed as `postgresql://{user}@{host}:{port}/{dbname}`. libpq reads the password from `~/.pgpass` automatically. An optional `dsn` field overrides all individual fields for non-standard setups (connection poolers, etc.).

### Per-Repo Config (`muninn.toml`)

```toml
# All sections optional. Empty file is valid — it just marks the repo root.

[repo]
name        = "my-project"   # defaults to directory name if absent
description = ""             # informational only

[database]
host   = "db.internal"       # override any field
dbname = "muninn_project"

[embeddings]
backend = "local"            # only fields present override global

[watcher]
debounce_ms = 1000
```

Only fields explicitly present in `muninn.toml` override the global value. Absent fields are inherited unchanged. `[repo]` has no global equivalent.

**Embedding dimension constraint:** `embedding_dim` is fixed at first index time and stored in the DB. Changing `backend` in `muninn.toml` after a repo has been indexed is detected and rejected. A `muninn reindex --reset` wipes the existing index and re-registers with the new backend.

### Config Loading

```
GlobalConfig::load()            ← ~/.config/muninn/config.toml
    ↓ field-level merge
RepoConfig::load(repo_root)     ← muninn.toml (may not exist or be empty)
    ↓
EffectiveConfig                 ← used by indexer and MCP server
```

`EffectiveConfig` exposes:
- `db_dsn() -> String` — constructed from effective database fields
- `embeddings: EmbeddingConfig`
- `watcher: WatcherConfig`
- `repo_name: String` — from `[repo].name` or directory name

### Indexer Discovery

At startup `muninn-index`:

1. Reads global config → gets `scan_roots` and `scan_depth`
2. For each scan root, walks the directory tree (via `ignore::WalkBuilder`, respects `.gitignore`, skips hidden dirs) up to `scan_depth` levels
3. Collects every directory containing `muninn.toml`
4. For each discovered repo root:
   - Builds `EffectiveConfig`
   - Upserts repo in DB by path (registers if new, using effective `embedding_dim`)
   - Starts indexing + file watching with the repo's effective config
5. Scan runs once at startup. A restart is needed to pick up newly added `muninn.toml` files.

### CLI Changes

**`muninn register <path>`**
1. Creates `muninn.toml` in `<path>` (pre-filled with `[repo] name = "<dirname>"`, all other sections commented out as examples)
2. Opens `$EDITOR` for the user to review/edit
3. Does **not** touch the DB — actual registration happens on next indexer startup

**`muninn unregister <path>`**
1. Prompts for confirmation (destructive: deletes a file from the repo)
2. Deletes `<path>/muninn.toml`
3. Deletes DB entry + chunks for the repo

**`muninn list` / `muninn status`**
- Unchanged in behaviour; repo list still comes from DB

**Removed:** The `repos` list in global config is removed. `RepoEntry` (id, path, name) is no longer persisted in the config file.

### MCP Server Repo Resolution

Search tools currently require an explicit `repo` path parameter. With `muninn.toml` as a root marker:

- `repo` parameter becomes **optional**
- If omitted, the server walks up from `cwd` (current working directory supplied by Claude Code) until it finds `muninn.toml`
- If provided, it is used directly (existing behaviour)

Walk-up resolution:
```
cwd = /home/alice/projects/myapp/src/auth
  → check /home/alice/projects/myapp/src/auth/muninn.toml  (absent)
  → check /home/alice/projects/myapp/src/muninn.toml       (absent)
  → check /home/alice/projects/myapp/muninn.toml           ← found
  → repo root = /home/alice/projects/myapp
```

If no `muninn.toml` is found and `repo` is also absent, the server returns a clear error.

### What Changes in the DB

No schema migration needed. The existing `repos` table is unchanged. The `config` column (currently unused `jsonb`) remains available for future use.

### Testing

- Unit tests for `EffectiveConfig::merge` covering: all-defaults, full override, partial field override, empty `muninn.toml`
- Unit test for `db_dsn()` construction from individual fields
- Unit test for walk-up repo resolution (mock filesystem)
- Unit test for scan discovery (temp directory with nested `muninn.toml` files)
- Existing 49 tests must continue to pass