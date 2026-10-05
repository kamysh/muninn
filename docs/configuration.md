# Configuration reference — 1.0

## Two scopes

| Location | Purpose | Interface |
| --- | --- | --- |
| `~/.config/muninn/config.toml` | Database connection, embedding credentials/cache, global knowledge embeddings, logging and legacy defaults | `muninn init`, `muninn config get/set/edit/unset --global` |
| Family schema in PostgreSQL | Name, ordered file-selection rules, embedding profile/batch size and watcher debounce, shared across linked worktrees | `muninn config PATH` TUI or `--json` |

New-family policy comes from **shipped defaults**, not a copy of global settings.
In particular it starts with Voyage, model `voyage-code-3`. A local global backend
does not select local for a new family. Choose the family backend before saving
its initial policy. Inspect the returned `policy`, `defaults`, `effective_policy`
and `capabilities` rather than guessing precedence.

Global changes do not rewrite existing family policies. Policy/default history
is stored in the database. `.muninn.toml` handling remains in the legacy code
path; it is not a database-family configuration file.

## Global bootstrap

```sh
muninn init database.host=localhost database.port=5432 \
  database.dbname=muninn database.user=muninn embeddings.backend=local
```

Or use `muninn init` to edit the template on a fresh installation. With an
existing config and no assignments, it preserves content and runs public
migrations. Global setters also validate and run public migrations; global getters
do not. The config file is written with mode `0600` because it can contain API keys.

A complete minimal local config is:

```toml
[database]
host = "localhost"
port = 5432
dbname = "muninn"
user = "muninn"

[embeddings]
backend = "local"
batch_size = 64

[watcher]
debounce_ms = 300
```

`[database]`, `[embeddings]` and `[watcher]` are required when writing the file
manually. `[index]` and `[mcp]` are optional. Unknown keys are rejected.

### Database connection

Required fields are `host`, `port`, `dbname`, `user`; `host` may be a PostgreSQL
Unix-socket directory. Muninn reads the first matching entry in `~/.pgpass`.
Keep that file owner-only and use literal values matching the configured fields.
The current reader supports `*` fields, but is not libpq's complete escaped-field
parser and does not read `PGPASSFILE`. Simple generated hexadecimal passwords
avoid delimiter/escaping differences with the setup helper and `psql`.

| Optional field | Current behavior |
| --- | --- |
| `connect_timeout` | Connection timeout in seconds; family preparation supplies 10 seconds when omitted |
| `application_name` | Regular connections use it unless a caller supplies its own name; listener/preparation use dedicated names |
| `ssl_mode` | Omitted, `disable`, `allow`, `prefer`: current code uses `NoTls`. `require`: selects a TLS connector with certificate validation disabled. `verify-ca`, `verify-full`: select the native TLS verifier; there is no separate CA-only implementation. See the transport limitation below |
| `ssl_root_cert` | Optional PEM CA certificate added to native TLS trust |
| `ssl_client_cert`, `ssl_client_key` | PEM client certificate/key pair for TLS client authentication |
| `dsn_override`, `max_connections` | Accepted by the config type but **not used** by the current connection builder; do not rely on them for routing or pooling |

**Transport limitation:** Muninn selects a connector but does not set the driver's
SSL mode. The pinned tokio-postgres driver defaults to `Prefer`, which can fall
back to plaintext when the server declines SSL. Thus even the `require` and
verification names do not currently enforce TLS-only transport. Do not present
these settings as a verified secure remote-database recipe. The recommended local
postgres-ai setup binds its port to loopback. A remote deployment needs a separately
validated transport arrangement; use explicit connection fields, not the unused
DSN override. See [database setup](own-database.md).

### Embeddings and credentials

| Backend | Family model field | Dimensions | Credentials |
| --- | --- | --- | --- |
| `local` | `null` in JSON; runtime uses `minishlab/potion-base-32M` | 512 | None |
| `voyage` | `"voyage-code-3"` | 1024 | Global `embeddings.api_key` for Voyage |
| `openai` | `"text-embedding-3-small"` | 1536 | Global `embeddings.api_key` for OpenAI |

Global `embeddings` accepts `backend`, optional `model`, optional `api_key`,
optional local `cache_dir`, and required `batch_size`. The local model is fixed;
a global model string does not choose a different local model. First use downloads
weights if absent; cached local embeddings require no provider API.

For a hosted profile, set matching global backend/model and its API key in the
owner-only config, then select that family profile. The runtime reuses the global
API key only when its backend matches the family backend; there is no per-family
credential store or simultaneous multi-provider key map. Global embeddings also
serve curated knowledge. Hosted requests send source chunks and query text to
the provider.

A registered family's backend/model/dimension cannot currently be changed through
policy apply. `capabilities` and candidate checking expose this limit. Do not
suggest remove/re-add as a routine setting change: removal destroys the family
index and registration. A model migration needs its own reviewed procedure.

## File selection

Git ignore files are not consulted. Rules classify paths as:

- **Excluded:** no chunks or embeddings.
- **Tier 1:** searchable text and eager embeddings.
- **Tier 2/vendor:** searchable text, initially deferred embeddings.

The shipped exclusions include `.git/`, minified JS/CSS, source maps, snapshots
and selected lockfiles. Vendor defaults include `node_modules`, vendor/virtualenv
paths and common build/cache directories. Build output is therefore not generally
excluded. The exact frozen lists are returned in `.data.defaults.index`.
`.git` metadata is excluded by the walker independently of configurable rules;
non-text and oversized files can also be skipped during indexing.

Family `index.exclude` and `index.vendor` arrays extend frozen defaults in order;
last matching rule wins within an axis, `!pattern` negates, and exclusion takes
precedence over vendor classification. Parent-directory pruning matters: to
reinclude a child, its parent must also be traversable. Check the effective rules
and preflight after editing.

Choose rules according to what you need searchable. Excluding dependencies can
be appropriate; keeping their source as vendor can also be useful. Do not assume
that all dependency/build files are valuable or that vendor classification makes
indexing free. The Git worktree search path currently neither lazily warms vendor
embeddings nor applies the legacy tier ranking penalty. Vendor text remains
available through full-text/hybrid text results; semantic coverage requires a
stored vector. These are current runtime limits, not promises of future behavior.

Global `[index].exclude` and `.vendor` remain legacy merge inputs. They do not
silently replace the shipped defaults or saved policy of a new/registered family.
Use the family TUI or JSON interface to change selection.

## Inspect, check, save, start

```sh
muninn config /path/to/checkout --json
muninn preflight /path/to/checkout --json
muninn config /path/to/checkout
```

For an unregistered path use preflight to obtain creation defaults; inspect
reports `not_registered`. Preflight is a bounded metadata scan (currently two
seconds or 100,000 entries). Counts may be lower bounds; it does not read file
contents, parse, embed, or guarantee runtime cost. Advice and candidate exclusions
are suggestions, not applied changes.

The [shared skill](claude-code-setup/skill/SKILL.md#configure-with-json) contains
complete JSON initial/check/apply/start requests. Requests are not configuration
files. Check validates without saving. Apply replaces a complete policy with
family/revision guards. Policy saves can reconcile an already-enabled family.
Registration or saving an unstarted family does not start it; `start` or the
TUI's separate Start confirmation does. A first start can download a model and
perform substantial indexing.

`watcher.debounce_ms` is part of family policy. File selection and policy are
shared across linked worktrees; preflight inventories only the selected checkout.

## MCP settings

`[mcp].record_usage` defaults to `true`; `muninn usage --days N` reads aggregate
call counts. `[mcp.logging]` accepts:

| Key | Default |
| --- | --- |
| `enabled` | `true` |
| `dir` | `"~/.local/state/muninn/mcp"` |
| `retention_days` | `7` |
| `prune_interval_hours` | `24` |

The MCP process reads global settings at startup. Reconnect it to load changed
settings; restarting only the indexer does not reload existing MCP clients.
