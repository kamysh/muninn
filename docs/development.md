# Building and development

## Building and testing

Use the pinned Nix flake from a source checkout containing the intended version:

```sh
nix develop
cargo build --locked
cargo test -p muninn-core --lib parser::tests
cargo fmt --check
cargo clippy --workspace --all-targets -- -D warnings
```

These are development commands, not a claim that every check has passed on every
platform. The database distribution for integration work is
[postgres-ai](https://github.com/kamysh/postgres-ai). It supplies compatible
PostgreSQL/pgvector/AGE components; independently assembling them is an
[advanced, non-recommended alternative](own-database.md).

The dev shell exports example `DATABASE_URL`/`TEST_DATABASE_URL` values, but the
application reads `~/.config/muninn/config.toml` and `~/.pgpass`. Do not treat the
shell's example variables as proof of a disposable database target. The guarded
integration harness supplies its own credentials and identity checks:

```sh
# Inside the dev shell, with Docker and the harness's pinned image available.
bash muninn-setup/test-persistence.sh
```

Read the script's image, port, container and resource requirements first. It uses
a disposable container, a temporary data filesystem, generated credentials and
an ownership marker, and verifies cleanup. It refuses a conflicting container
or port. Some legacy integration tests use different setup conventions; do not
run an unreviewed broad database test suite against your normal configuration.

For distributable binaries:

```sh
nix build .#muninn-static
result/bin/muninn --version
result/bin/muninn-index --version
result/bin/muninn-mcp --version
```

On Linux this target links statically with musl. The build includes native
OpenSSL and a C++ dependency via the tokenizer; it is not a pure-Rust dependency
stack. macOS uses system frameworks. A plain `cargo build --release` does not
promise a portable static executable. `nix build .#muninn` is the Nix-managed
variant, which may reference its Nix store dependencies.

The [release workflow](../.github/workflows/release.yml) builds Linux x86_64,
Linux ARM64 and macOS ARM64. Other assets, such as macOS Intel, must be verified
on the particular release. See [installation/version selection](get-started.md#3-install-matching-binaries).

## Architecture and rationale

The four crates are `core` (shared implementation), `cli` (`muninn`), `indexer`
(`muninn-index`) and `mcp` (`muninn-mcp`). All use PostgreSQL through
`tokio-postgres`; SQLx migration/cache instructions from older plans do not apply.

The index saves repeated exploration and embedding work. Linked worktrees need
independent searchable views of largely identical files. Independent full copies
multiply both storage and index-building cost. Sharing a mutable main index alone
would instead make a worktree's results change when main updates. The current
moving-base/file-delta design addresses both problems.

### Storage ownership

| Area | Ownership and contents |
| --- | --- |
| `public.repos` | Family routing, identity, preparation state and indexing authorization; retains legacy locator fields |
| `repo_<uuid>` | One application schema per Git family or independent directory: chunks, file versions, base/deltas, checkout registry and saved policy/history |
| AGE graph schemas | Code symbols/relationships; Git checkouts have separate graphs. AGE creates/removes these through its API |
| `public.knowledge` | Curated notes, keyed by exact repository-path strings; currently separate from family identity |

Kryzhen's Rust library creates application schemas while applying migrations.
Each migration directory is one dependency graph applied to **one target schema**:
`public/` targets public; `repo/` is replayed as a template for each application
schema. AGE graph schemas are not Kryzhen targets and do not belong in `repo/`.

Embedding dimension is fixed for the family's vector column. Current policy
operations reject changes to the registered embedding profile; there is no general
model-migration command. Removing a family is destructive, not an ordinary way
to edit its settings.

### Worktree indexing and search

`repo_resolver` obtains checkout roots and Git common-directory identity from Git.
`family_store` coordinates identity/preparation; `family_policy` implements policy,
preflight and start; `worktrees` reconciles file versions and checkout graphs.

The primary checkout is the current base. `base_files` maps its paths to shared
`file_versions`; `file_deltas` contains only checkout-specific path overrides or
deletions. Chunks and embeddings are stored with file versions. When the base
moves, formerly inherited versions needed by another checkout become references
in its delta. Redundant overrides are removed. This changes representation while
preserving other published views; it does not force every worktree to adopt main.

Family locking serializes publication. Base changes, deltas and the reconciled
checkout's graph commit transactionally. Embeddings can be reused for matching
content. Graph replacement deletes edges before vertices in bounded batches,
then reconstructs the selected checkout's relationships. Graphs themselves are
not shared in the same way as chunk/vector content.

Text/vector queries combine visible base chunks with the selected delta. The
base has partial GIN/HNSW indexes; semantic delta search is exact. Excluded paths
mask base candidates before ranking. Hybrid search ranks each modality across
base and delta before RRF in one SQL statement/snapshot. Approximate base vector
retrieval still has recall tradeoffs; a small RRF score is not a confidence estimate.

File watching and fallback Git discovery find edits, newly linked checkouts and
worktree removal. Removal from a successfully read Git registry retires the
checkout and drops its AGE graph. A root that is unavailable but remains registered
retains its data. Discovery does not invoke `git worktree prune`.

**Merge/rebase/conflicts suspend publication for the affected checkout.** It keeps
its last completed index; an uninitialized checkout has no completed view. The
watcher retries after completion/abort. Ordinary edits are indexable. Git hooks
are not required for correctness; the current discovery/watch/poll path provides
reconciliation. The SQL transaction cannot make the external filesystem atomic
against uncooperative concurrent writers.

Structural edges are name-based candidates rather than language-server bindings.
For Git call resolution, matches in the caller's file take priority, all local
ties are kept, and otherwise all checkout-wide name matches are retained. Inspect
source to establish the actual binding.

### Configuration and daemon coordination

Initial `add`/save does not start indexing. Explicit `start` or the TUI Start
confirmation enables the family and runs foreground indexing; the daemon can
continue an interrupted authorized run. New linked worktrees inherit family policy.

The global config holds connection/credentials and service/legacy settings.
New family policy uses shipped creation defaults. Stored defaults and revisioned
policy do not silently change when global settings or a new binary change defaults.
Read-only policy queries never prepare schemas or write configuration. The current
policy is locked against stale-policy publication during reconciliation.

The daemon reads registrations from the database, receives `muninn_repos_changed`
notifications and has a 60-second fleet fallback. Family watchers additionally
reconcile their Git inventory. Notifications improve responsiveness; they are not
durable job records. Existing directory and legacy registrations use the pipeline
appropriate to their registration state.

Indexing exclusion uses advisory locks and cooperative preemption, not the old
`indexing_heartbeat` mechanism. Removal waits for indexing coordination rather
than merely refusing every active index. Family publication also holds its
transaction advisory lock.

### MCP and knowledge

The MCP server is a stdio JSON-RPC process exposing eight tools. Code search
requires `repo` or `cwd`; explicit `repo` wins. Resolve to the actual checkout,
not the MCP process's working directory. Git/DB resolution does not require
`.muninn.toml`; a legacy fallback remains.

Curated knowledge currently has a different identity rule: exact `repo` strings.
Use an established main-checkout key for shared notes. Do not create accidental
note silos for temporary worktrees. See the [agent skill](claude-code-setup/skill/SKILL.md).

### Current limitations

- No 100-worktree load measurement or established large-delta latency/recall budget.
  Delta search cost grows with changed chunks; graph reconstruction can parse
  many files even when chunks/vectors are reused.
- Search responses currently contain results, not freshness/suspension metadata.
  Inspect Git state and daemon logs when currentness matters.
- `status PATH`, `pause`, `resume`, `remove` look up the registered locator, not
  arbitrary worktree paths. `config PATH --json` and code searches resolve families.
- Worktree queries do not implement the legacy vendor ranking penalty or lazy
  embedding warm-up. Tier-2 chunks without vectors still participate in text search.
- New-family default backend is Voyage; global local-backend selection is not
  inherited. Existing embedding-profile changes are unsupported.
- `dsn_override` and `max_connections` are parsed but unused; SSL modes and password
  lookup have limits detailed in [Configuration](configuration.md).
- Formal models contain abstractions and known runtime mismatches. See
  [the proof boundary](../spec/README.md); type-checking alone does not close them.

## Changing migrations

Existing migration blocks are immutable: their recorded identity/checksum matters.
Append semantically related blocks to the appropriate file, or introduce a semantic
filename for a distinct set. Do not rename existing files or introduce numerical
names merely to force ordering. Kryzhen orders by dependencies, including implicit
in-file predecessors.

`db.rs` embeds the public and repo directories and calls the Kryzhen library with
an explicit target schema. Each block commits with its record; the whole set is
not an outer all-or-nothing transaction. Preparation can resume after partial
completion. AGE lifecycle is coordinated separately through its API.

Normal startup/preparation applies pending migrations. Read-only inspect/check/
preflight do not. Users do not need a separate migration script for upgrades.
See [Upgrading](upgrading.md).

## Contributing to parsers, embeddings and specifications

Parser grammars, chunking and relationship extraction are in
[`parser.rs`](../crates/core/src/parser.rs). Test representative source and edge
cases, including generated/minified files; multiple symbols on one line must not
multiply identical source spans into thousands of chunks.

Embedding implementations live in [`embeddings.rs`](../crates/core/src/embeddings.rs).
Adding a model requires agreement on a stable dimension and corresponding policy
validation. Backend credentials belong in global configuration, not saved family
policy JSON.

Agda models live under `spec/`; [`spec/README.md`](../spec/README.md) distinguishes
abstract laws from implementation guarantees and lists current gaps. For a final
aggregate type check, from the source root:

```sh
nix develop --command sh -c 'cd spec && agda Muninn.agda'
```

Type-checking proves statements of that model, not a refinement proof of the Rust,
SQL, Git detector or AGE implementation. Do not weaken a model just to describe an
implementation defect. Historical plans are retained as records and marked as such;
use this guide and current source for implemented behavior.
