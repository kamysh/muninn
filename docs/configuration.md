# Configuration reference — 1.2.1

## Two scopes

| Location | Purpose | Interface |
| --- | --- | --- |
| `~/.config/muninn/config.toml` | Database connection, embedding credentials/cache, global knowledge embeddings, logging, defaults for new families and unbound registrations | `muninn init`, `muninn config get/set/edit/unset --global` |
| Family schema in PostgreSQL | Name, ordered file-selection rules, embedding profile/batch size and watcher debounce, shared across linked worktrees | `muninn config PATH` TUI or `--json` |

New repositories begin with a **snapshot of global settings**: embedding provider,
supported model and request size, watcher change delay, and global file-selection
rules. Shipped file rules run first, followed by the captured global rules, then
repository-specific rules. The TUI shows inherited global patterns alongside custom rules and marks edited
values. Existing saved snapshots are shown separately from the current global
patterns, which are a reference for new repositories. Older snapshots without
source labels show the full saved default list without guessing provenance.
The snapshot is captured when configuration opens and saved at registration;
later global edits do not change that draft or any already-saved repository.
Connection settings, credentials and machine-local cache paths remain global.
Inspect `policy`, `defaults`, `effective_policy`, `global_defaults` and
`capabilities` to see the selected values and current reference defaults.

Global changes do not rewrite existing family policies. Policy/default history
is stored in the database.

## Global bootstrap

```sh
muninn init database.host=localhost database.port=5432 \
  database.dbname=muninn database.user=muninn embeddings.backend=local
```

Use `muninn init`, `muninn config --global`, or `muninn config edit --global`
to create or edit global settings in the TUI. Focused-setting explanations stay in a labelled bottom region, separated from
the scrolling settings and above Save/Cancel. Press `?` for the complete focused
explanation; while editing a value, PgUp/PgDn scroll its help. Ordered rule editing
and masked API-key controls are built in. Save validates and writes the
file, then connects to prepare the configured database; a connection failure
leaves the saved file available for correction. Cancel leaves the file unchanged
and does not connect. Assignment-based init and global set/get/unset remain
available for automation. Global getters do not run migrations. The config file is written with mode `0600` because it can contain API keys.
Running daemon and MCP processes read global configuration at startup; restart
the daemon and reconnect MCP clients after changing connection, credential or
logging settings. Repository configuration reloads globals when opened or rescanned.

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
Unix-socket directory. Password precedence is optional `database.password`,
nonempty `PGPASSWORD`, then the first matching password-file entry.
The file is selected by optional `database.pgpassfile`, then `PGPASSFILE`, then
`~/.pgpass`. Files must be owner-only; escape colons and backslashes in every
field. Quotes and spaces are literal. See [credentials and TLS](database-connections.md)
for examples and the complete policy.

| Optional field | Current behavior |
| --- | --- |
| `connect_timeout` | Connection timeout in seconds; family preparation supplies 10 seconds when omitted |
| `application_name` | Regular connections use it unless a caller supplies its own name; listener/preparation use dedicated names |
| `password`, `pgpassfile` | Optional literal password and explicit password-file path |
| `ssl_mode` | Default `prefer`; `disable` uses plaintext; `allow` tries plaintext then TLS on server rejection; `require` requires encryption; `verify-ca` also verifies trust; `verify-full` also verifies hostname |
| `ssl_root_cert` | Optional PEM CA bundle replacing native system trust |
| `ssl_client_cert`, `ssl_client_key` | PEM certificate chain and matching unencrypted PKCS#8 private key; supply both |
| `dsn_override`, `max_connections` | Accepted by the config type but **not used** by the current connection builder; do not rely on them for routing or pooling |

`require`, `verify-ca` and `verify-full` refuse servers without TLS. All connection
paths, including listeners, preparation, locks and cancellation, share this policy.
Use `verify-full` with the appropriate CA for a remote database. The optional
[SSH tunnel recipe](own-database.md#remote-database-through-ssh) remains available.

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

`muninn remove PATH` uses the registered path displayed by `muninn status`.
Its confirmation names the repository and includes all indexed worktrees in the
removal scope. An empty answer, No, or end of input cancels before waiting for
indexing or asking the indexer to yield. An unregistered path has nothing to remove.

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

Global `[index].exclude` and `.vendor` are captured into a new family's frozen
default rules and remain runtime defaults for unbound registrations. Later global
edits do not replace an existing family's snapshot or saved policy.
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
TUI's explicit Start indexing action does. A first start can download a model and
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
