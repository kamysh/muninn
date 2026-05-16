# Configuration reference

## Overview

muninn uses two configuration files:

| File | Scope | Created by |
|------|-------|-----------|
| `~/.config/muninn/config.toml` | Global defaults for all repos | `muninn config` |
| `<repo-root>/.muninn.toml` | Per-repo overrides | `muninn add` / `muninn configure` |

`EffectiveConfig` is computed at runtime by merging the two: every section in `.muninn.toml` fully replaces the corresponding global section. Fields within a section are not merged individually — the entire `[database]` or `[embeddings]` block wins or loses as a unit.

The config file may contain API keys. `muninn config` sets its permissions to `0600` (owner read/write only) automatically.

---

## Database setup

muninn requires PostgreSQL 16 or later with two extensions:

| Extension | Purpose |
|-----------|---------|
| **pgvector** | Vector similarity search (`VECTOR` column type, HNSW index) |
| **Apache AGE** | Property graph storage and Cypher query engine |
| **pgcrypto** | UUID generation (usually bundled with PostgreSQL) |

The easiest path is the [kamysh/postgres-ai](https://hub.docker.com/r/kamysh/postgres-ai) Docker image, which ships with all three pre-installed and pre-configured. The sections below describe manual setup on an existing PostgreSQL instance.

### Option A — Docker (recommended)

```bash
docker run -d \
  --name muninn-postgres \
  --restart always \
  -e POSTGRES_PASSWORD=changeme \
  -p 127.0.0.1:5432:5432 \
  -v muninn_data:/var/lib/postgresql/data \
  kamysh/postgres-ai:latest
```

The image starts with `shared_preload_libraries = 'age'` already set, and both extensions installed. Skip to [Create the database](#create-the-database) below.

### Option B — Manual installation

#### 1. Install pgvector

pgvector is available as a pre-built package for most distributions:

**Ubuntu / Debian (PostgreSQL 16):**
```bash
sudo apt install postgresql-16-pgvector
```

**macOS (Homebrew):**
```bash
brew install pgvector
```

**From source** (any platform, requires PostgreSQL development headers):
```bash
git clone --branch v0.8.0 https://github.com/pgvector/pgvector.git
cd pgvector
make
sudo make install
```

#### 2. Install Apache AGE

AGE requires the PostgreSQL server development headers and must be compiled for your exact PostgreSQL major version.

**Ubuntu / Debian (PostgreSQL 16):**

AGE is not in the default APT repositories. Build from source:

```bash
sudo apt install postgresql-server-dev-16 build-essential flex bison

git clone https://github.com/apache/age.git
cd age
git checkout PG16/v1.6.0-rc0    # use the tag matching your PostgreSQL major version
make
sudo make install
```

**macOS (Homebrew):**
```bash
brew install apache-age
```

**Verify installation:**
```bash
ls $(pg_config --pkglibdir)/age.so    # must exist
ls $(pg_config --sharedir)/extension/age.control    # must exist
```

#### 3. Enable AGE in postgresql.conf

AGE must be loaded at server start. Add it to `shared_preload_libraries`:

```bash
# Find your postgresql.conf
psql -U postgres -c 'SHOW config_file;'
```

Edit `postgresql.conf`:
```
shared_preload_libraries = 'age'
```

If `shared_preload_libraries` already lists other libraries, append with a comma:
```
shared_preload_libraries = 'pg_stat_statements, age'
```

**Restart PostgreSQL** for the change to take effect:
```bash
# systemd
sudo systemctl restart postgresql

# macOS Homebrew
brew services restart postgresql@16

# pg_ctl (adjust data directory as needed)
pg_ctl restart -D /var/lib/postgresql/16/main
```

#### 4. Create the database and user

Connect as a PostgreSQL superuser:

```bash
psql -U postgres
```

```sql
-- Create a dedicated role (replace 'alice' with your username)
CREATE USER alice WITH PASSWORD 'yourpassword';

-- Create the database owned by that user
CREATE DATABASE muninn OWNER alice;

-- Connect to the new database to install extensions
\c muninn

-- pgcrypto is usually in the default contrib package
CREATE EXTENSION IF NOT EXISTS pgcrypto;

-- pgvector
CREATE EXTENSION IF NOT EXISTS vector;

-- Apache AGE
CREATE EXTENSION IF NOT EXISTS age;

-- AGE stores its graph data in ag_catalog.
-- The muninn user must have USAGE on this schema.
GRANT USAGE ON SCHEMA ag_catalog TO alice;

-- AGE functions used by muninn are in ag_catalog as well.
-- Grant EXECUTE so muninn can call cypher() and related functions.
GRANT EXECUTE ON ALL FUNCTIONS IN SCHEMA ag_catalog TO alice;
```

You can verify the setup:
```sql
\dx                          -- should list pgcrypto, vector, age
\dn                          -- should show ag_catalog schema
\c muninn alice localhost    -- reconnect as the muninn user to confirm access
SELECT ag_catalog.create_graph('test'); -- should succeed; clean up with DROP GRAPH test CASCADE;
```

#### 5. Configure password authentication

muninn reads passwords from `~/.pgpass` — it never stores a password in `config.toml`. The file format is:

```
hostname:port:database:username:password
```

Example:
```
localhost:5432:muninn:alice:yourpassword
```

The file must be owned by you and not group- or world-readable:
```bash
chmod 600 ~/.pgpass
```

For socket connections (`host = /var/run/postgresql`), use the socket path as the hostname in `.pgpass`:
```
/var/run/postgresql:5432:muninn:alice:yourpassword
```

#### 6. Apply migrations

Once the database is ready, run:
```bash
muninn config
```

If you have already created the config file, `muninn config` still re-opens it for editing — just save and close without changes. Migrations are applied every time and are idempotent: already-applied migrations are skipped and their checksums verified.

The first migration (`001_initial.sql`) checks that all three required extensions are installed and that the user has `USAGE` on `ag_catalog`. If any check fails, you will see a clear error pointing to the missing prerequisite.

---

## `~/.config/muninn/config.toml` reference

### `[database]`

| Key | Type | Default | Description |
|-----|------|---------|-------------|
| `host` | string | `"localhost"` | PostgreSQL hostname or IP address |
| `port` | integer | `5432` | PostgreSQL port |
| `dbname` | string | `"muninn"` | Database name |
| `user` | string | current OS user | PostgreSQL role name |
| `dsn_override` | string | — | Full connection URI (e.g. `postgresql://alice@localhost:5432/muninn`). When set, `host`/`port`/`dbname`/`user` are ignored for routing, but SSL settings and pool settings below still apply. |
| `ssl_mode` | string | — | `disable` \| `allow` \| `prefer` \| `require` \| `verify-ca` \| `verify-full` |
| `ssl_root_cert` | string | — | Path to PEM CA bundle for server certificate verification (needed for `verify-ca` / `verify-full`) |
| `ssl_client_cert` | string | — | Path to PEM client certificate (mutual TLS) |
| `ssl_client_key` | string | — | Path to PEM client private key (mutual TLS) |
| `max_connections` | integer | `10` | Connection pool size |
| `connect_timeout` | integer | — | Seconds to wait for a connection; omit for no timeout |
| `application_name` | string | — | Name shown in `pg_stat_activity` |

**Password** is never stored in config. Add a line to `~/.pgpass` (see above).

**Unix socket connections** — set `host` to the socket directory (e.g. `host = "/var/run/postgresql"`).

### `[embeddings]`

| Key | Type | Default | Description |
|-----|------|---------|-------------|
| `backend` | string | `"voyage"` | `voyage` \| `openai` \| `local` |
| `model` | string | `"voyage-code-3"` | Model name passed to the API or loaded locally |
| `api_key` | string | — | API key; required for `voyage` and `openai` |
| `cache_dir` | string | — | Directory for local model weights (`local` backend only); defaults to a platform cache dir |
| `batch_size` | integer | `64` | Number of text chunks sent to the API per request; reduce if you hit rate limits |

**The embedding dimension is frozen at `muninn add` time.** Changing the backend or model after indexing requires removing and re-adding the repo:
```bash
muninn remove /path/to/repo
muninn add    /path/to/repo
```

Available backends:

| Backend | Model | Dims | API key | Notes |
|---------|-------|------|---------|-------|
| `voyage` | `voyage-code-3` | 1024 | [dash.voyageai.com](https://dash.voyageai.com) | Best quality for code; recommended default |
| `openai` | `text-embedding-3-small` | 1536 | [platform.openai.com](https://platform.openai.com) | Good quality; higher dimensionality |
| `local` | BGE-Base-EN-v1.5 | 768 | — | No API key; ONNX on CPU; ~200 MB download on first use |

### `[watcher]`

| Key | Type | Default | Description |
|-----|------|---------|-------------|
| `debounce_ms` | integer | `300` | Milliseconds to wait after the last file-change event before triggering a re-index. Increase (e.g. `2000`) if you see excessive re-indexing during large rebases or editor auto-saves. |

### `[mcp]`

| Key | Type | Default | Description |
|-----|------|---------|-------------|
| `record_usage` | bool | `true` | Record MCP tool call counts in the `mcp_usage` table (visible via `muninn stats`) |

### `[mcp.logging]`

| Key | Type | Default | Description |
|-----|------|---------|-------------|
| `enabled` | bool | `true` | Write a structured log file for each MCP session |
| `dir` | string | `"~/.local/state/muninn/mcp"` | Directory for log files (`~` is expanded) |
| `retention_days` | integer | `7` | Log files older than this are deleted during the next prune |
| `prune_interval_hours` | integer | `24` | How often `muninn-mcp` checks for and deletes old log files |

---

## Per-repo `.muninn.toml` reference

`.muninn.toml` lives at the root of each registered repository. Its presence marks that directory as a muninn repo root — `muninn-mcp` resolves the repo by walking up from the current working directory until it finds this file.

All sections are optional. An empty file (or one where everything is commented out) is valid and inherits everything from the global config.

Overridable sections: `[database]`, `[embeddings]`, `[watcher]`. The `[mcp]` section cannot be overridden per-repo. The `repo_name` top-level key sets the display name shown in `muninn list`.

```toml
# repo_name = "my-project"    # overrides the directory name

# [database]
# Override to index this repo into a different database.
# host = "remote-pg.example.com"
# port = 5432
# dbname = "my_project_index"
# user = "alice"

# [embeddings]
# Override to use a different backend for this repo.
# backend = "local"
# model   = "bge-base-en-v1.5"
# batch_size = 32

# [watcher]
# debounce_ms = 2000
```

**DimFrozen invariant:** if you try to change the embedding backend in `.muninn.toml` after the first index, `muninn configure` will reject it with an error. Remove and re-add the repo to switch backends.
