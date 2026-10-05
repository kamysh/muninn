# Muninn 1.0.0: storage and interface design for review

> Core storage/search revision: the approved moving-base and file-delta design
> in [runtime integration](2026-10-04-runtime-integration-plan.md) supersedes
> retained-baseline and shared-family-graph recommendations below. Configuration
> work remains deferred; historical sections are retained for their evidence.

Status: proposed implementation design, 2026-10-03. This document makes the
[agreed specification](2026-10-02-worktree-indexing-proposal.md) concrete. The
recommendations below need review before implementation. No SQL migrations,
Rust code, database resources, or installed services were changed by the original
design stage. Subsequent implementation evidence is identified below. The
2026-10-04 [family/checkout persistence plan](#familycheckout-persistence-implementation-plan)
was approved for additive implementation; its source-only progress is recorded
in that section. Database execution and runtime activation remain separate gates.

## Focused rollback — 2026-10-04

The custom prefix/radix storage implementation and its dependent analysis/capture
code, tests and unshipped storage migrations have been removed at the user's
request. Registration, configuration and Git helpers remain. No replacement
storage implementation is authorized here. Historical implementation evidence
below pertains to the retained registration/configuration stages unless stated
otherwise. See the [current status](2026-10-04-runtime-integration-plan.md).

## Decisions already settled

- One application schema and one AGE graph schema per repository family; linked
  worktrees share the pair. Each independently registered non-Git directory has
  its own pair. This approved revision replaces the literal one-schema rule.
- Retain AGE for code relationships and their visibility attributes. The proposed
  external graph catalogs and membership trees are withdrawn. Structural results
  must belong to the selected checkout before ordering/limits.
- Muninn calls the **Kryzhen Rust library**, already a dependency, for application
  schema creation and migrations. **AGE owns graph lifecycle and its internal
  schema through its API**, independently of Kryzhen. Muninn coordinates both
  operations and requires both to be ready before using a family. Graph lifecycle
  has no Kryzhen migration directory or migration-history association.
- Unchanged chunks, embeddings and reusable analysis remain shared. Membership
  associations may reference them from multiple checkouts. Pulling main must not
  change another worktree's indexed results. No custom storage tree is required.
- First-family indexing is explicit. Subsequent worktree discovery and indexing
  are automatic, subject to pause and Git-operation state.
- Merge/rebase in progress or unresolved conflicts retain the affected
  checkout's last snapshot, explicitly stale. With no snapshot, report pending.
  Resume reconciliation automatically after completion or abort.
- Hooks are optional hints. Watching and reconciliation provide correctness.
- DB policy, human TUI, agent JSON, cheap preflight, and no per-repo config files.
- Existing migration blocks remain unchanged; new filenames are semantic and
  group related blocks. The user's eventual migration script stays outside Git.

## Review summary

| Choice still proposed | Recommendation | Cost or alternative |
| --- | --- | --- |
| File/chunk membership | Physical design withdrawn; ordinary relational associations are the direction for review | Repeated association rows do not require copying chunk data or embeddings. |
| Vector retrieval | Exact ranking over visible candidates initially | Potentially slower on large families; approximate retrieval requires measured recall and an explicit contract. |
| Policy and curated knowledge | Family-schema tables, public registry for routing only | Moves existing public knowledge during cutover, preserving IDs and recovery copies. |
| Command/JSON shape | Path-based add/config, complete revision-checked JSON policy updates | Keep existing get/set operations as DB adapters; replace editor-based configuration with the TUI. |
| Required analysis failures | Retain the old view, mark stale/error, retry | First indexing can remain pending on a problematic included file; preflight/configuration must make that actionable. |

The separate tree-based AGE/snapshot design has been withdrawn. The retained
schema ownership and configuration decisions do not approve a replacement
membership representation.

## Evidence from the current code

- [db.rs](../../crates/core/src/db.rs) embeds separate public and repo migration
  sets and calls `kryzhen::migrate`, explicitly targeting `public` or the supplied
  application schema. Manual application-schema creation has been removed.
  The pinned v2.0.1 library, commit `bb93e4f`, creates
  the target schema in `postgres::apply_one`, executes a block, and records it
  in one transaction. Each block commits separately; the whole migration set is
  not one transaction.
- [repo-chunks](../../migrations/repo/001_chunks.sql) derives the existing UUID
  from `repo_<uuid>` and reads `public.repos.embedding_dim`. Preserve that UUID,
  schema name, and registry row through migration.
- [store.rs](../../crates/core/src/store.rs) creates `code_graph_<uuid>` outside
  migrations through its existing AGE API path. The separate registration
  validation helper was withdrawn as unrelated to worktree support; the existing
  registration behavior is retained. [graph.rs](../../crates/core/src/graph.rs) serves the current
  structural operations with name-based, one-hop relationship queries.
- [pipeline.rs](../../crates/core/src/pipeline.rs) reparses files in its second
  graph pass. The incremental watcher does not perform that cross-file pass.
  Reuse requires persisting unresolved reference facts as well as definitions.
- The walker deliberately disables standard ignore filters. Git status alone
  would miss Git-ignored files that Muninn policy currently includes. Preserve
  Muninn's selection semantics in both inventory and reconciliation.
- [repo_resolver.rs](../../crates/core/src/repo_resolver.rs) now has a Git checkout
  discovery helper returning canonical checkout-root and common-directory paths.
  It does not depend on a config marker, branch name, or commit. Existing MCP
  routing still uses the legacy resolver; database family lookup and selected
  checkout snapshots are not yet connected to this helper. Family enumeration
  now uses `git worktree list --porcelain -z` from the common directory. It
  preserves Git-reported paths (including missing checkouts), attached/detached
  state, bare entries, and lock/pruning annotations. Enumeration never prunes
  metadata or changes watchers; a successful list is discovery evidence, not
  authorization to retire a snapshot. Available paths still need checkout
  identity validation before watcher integration.
- [search.rs](../../crates/core/src/search.rs) currently ranks one schema's flat
  chunks, and hybrid fusion deduplicates solely by chunk UUID. Shared analysis
  at multiple paths requires a path-sensitive result identity.

Historical Mimir release notes concern older schemas and library versions; the
current source and the user's decisions above govern this design. Muninn search
located the actual pipeline graph pass; a returned `.direnv` source copy was
excluded from the evidence.

## Family registry and schema lifecycle

Keep `public.repos.id` as the family ID, `repo_<simple-uuid>` as its application
schema, and `code_graph_<simple-uuid>` as its AGE graph/schema. Preserve existing
identities. Propose additive registry columns:

| Column | Meaning |
| --- | --- |
| `family_kind` | Git or independent directory |
| `family_key`, `path_encoding` | Lossless canonical Git common-dir or independent root; unique with kind/encoding among non-retired families |
| `schema_state` | Pending, migrating, ready, or failed for the whole application/AGE pair, with diagnostic text |
| `storage_generation` | Legacy or snapshots; explicit cutover selector |
| `indexing_enabled_at`, `indexing_enable_origin` | Explicit first authorization, or an identified import of prior indexing authorization; initially null |
| `registration_intent`, `registration_completed_at` | Approved JSON-add recovery refinement: immutable creation provenance and initial policy/defaults, plus irreversible completion. Current policy remains in the family schema. |

Existing `path` remains a compatibility/provenance field, not the authority for
which worktree is selected. Keep its value through cutover. New checkout roots
live inside the family schema. Recommend removing the legacy `path` uniqueness
constraint in a later cutover migration: reusing an abandoned directory for a different
family must not collide with historical provenance. Registration serializes live
root ownership checks across families; one root cannot select two live checkouts.
The initial additive migrations retain path uniqueness: the existing registration
query uses `ON CONFLICT (path)` and would fail without it. Do not ship the later
constraint change while any current registration caller remains enabled.
This constraint change needs an explicit recovery check before old binaries are
restored. If multiple existing registrations resolve to
one Git family, the migration plan reports their IDs/schemas and stops that
family for a consolidation decision; it does not elect a winner or drop data.

Registration reserves the family key/UUID. Recommend one application advisory
lock for all migration calls in the registry, including ledger initialization,
public migration, and family templates. This also serializes shared canonical
bookkeeping across different families. Run public migrations first,
then call `kryzhen::migrate(client, repo_migrations, Some(schema), false)` for
application objects. Separately, Muninn uses AGE's API to create or validate the
family graph. AGE creates its internal schema; it is never a Kryzhen target.
Mark ready only after all required application blocks succeed and AGE graph
readiness is verified. A crash can leave committed early blocks and a non-ready
registry row. Retry application migrations using Kryzhen's per-schema history;
recheck AGE independently and preserve an existing valid graph. Do not introduce
an outer transaction over the whole migration set: retain Kryzhen's per-block
commit/retry semantics. Coordination and concurrency still need runtime tests.
Worktree discovery only inserts checkout metadata into a ready family schema.

For an existing graph, Muninn validates its expected name, namespace, and family
association as separate AGE readiness evidence, with no Kryzhen completion record.
Do not recreate or clear it. An orphan namespace, mismatched graph, or missing
expected legacy graph requires diagnosis; do not treat it as an empty new family.
Template replay, AGE initialization failure, and retry after either operation
require integration tests against the installed combination before deployment.

The public and repo sets are separately passed to Kryzhen. Cross-set `requires`
references are not valid: its topological sort requires dependencies in the
supplied set. Public-before-repo is a caller-level ordering requirement; each
repo template also checks the registry inputs it needs. Public calls should
explicitly target `Some("public")` to avoid connection-search-path ambiguity.

Keep identifiers derived from validated UUIDs and quoted as identifiers; paths
and other values are bind parameters. Schema-qualified runtime queries prevent
pooled connection search-path state from selecting another family.

## Family/checkout persistence implementation plan

Status: **additive implementation and isolated database verification completed,
2026-10-04**. The two migration files below and typed metadata helpers exist in
source and passed the disposable database test described below. No live database
resources, registry rows, or installed binaries were changed. The helpers are
not connected to CLI, daemon, or MCP call paths.

Implemented in [family_store](../../crates/core/src/family_store/mod.rs): lossless
path encoding; typed family/checkout records; family lookup and reservation;
checkout lookup and registration; generation-checked observation updates and
invalidation. Reservation detects an unimported legacy registration belonging to
the same Git family instead of assigning it a second UUID. Discovery also returns
the canonical per-checkout administrative directory. All metadata mutations use
explicit family schema names; registration mutations use the registry transaction
lock. These metadata helpers do not mark a family ready, enable indexing, or
select a snapshot; the separate coordinator owns readiness transitions.

The separately approved preparation coordinator is now implemented and tested
as described below. Still deferred: legacy import, explicit suppression/reactivation/
relocation operations, and runtime routing. Existing `store::register_repo` and
its AGE preparation remain unchanged. No new formal lifecycle transition is
activated by this slice; the existing abstract schema/readiness and snapshot
contracts remain unchanged.

### Source findings and their consequences

| Current source | Consequence for this slice |
| --- | --- |
| `store::register_repo` inserts/upserts by unique `public.repos.path`, checks dimension, then prepares the application schema and AGE graph. | Preserve the old function for the legacy route. Add a separate family registration path; do not make a linked checkout call the old function. |
| `repo-chunks` derives the UUID from `current_schema()` and reads `public.repos.embedding_dim`. | Keep the existing row ID and `repo_<uuid>` naming. Reserve and commit a new registry row before calling the repo template. |
| `Repo`, `REPO_COLUMNS`, and `row_to_repo` use explicit columns. | Additive columns need not change the existing DTO or queries. Introduce `Family` and `Checkout` records separately. |
| CLI add normally starts indexing; the daemon uses `ever_indexed`; pause and preemption operate on repo IDs. | The new path must use explicit family authorization plus checkout eligibility. Do not derive authorization from registration, schema readiness, or worktree discovery. |
| MCP `tools::resolve_repo` returns a `Repo`; searches and graph queries accept only its ID. | Finding a family is insufficient to search a linked checkout. The new route must also select its checkout and published view. Never fall back to the main checkout's flat chunks. |
| `delete_repo` drops the application schema and AGE graph, then deletes the registry row. | It cannot implement checkout removal or non-destructive family retirement. Add those operations separately; prohibit the legacy deletion path for converted families. |
| CLI, daemon, and MCP startup call `run_migrations`; CLI indexing and daemon jobs also call `run_repo_migrations`. | Merely installing/running a binary containing new embedded SQL can apply it. Writing migration sources is not permission to install or invoke a new binary against the user's database. |

Sources: [store.rs](../../crates/core/src/store.rs),
[types.rs](../../crates/core/src/types.rs),
[db.rs](../../crates/core/src/db.rs),
[CLI](../../crates/cli/src/main.rs),
[daemon](../../crates/indexer/src/main.rs), and
[MCP tools](../../crates/mcp/src/tools.rs).

### Proposed migration groups

Only the following two semantic files are needed for this slice. Each contains
related blocks in the order below; subsequent blocks have the implicit in-file
dependency on their predecessor. Names are globally unique. Every repo block is
the same template text in every application schema.

| File | Block | Explicit initial dependency | Effects |
| --- | --- | --- | --- |
| `public/families.sql` | `public-family-identity` | `init` | Add nullable family identity and retirement columns, their checks, and a partial unique identity index. |
| same file | `public-family-lifecycle` | In-file predecessor | Add readiness, storage selector, and indexing-authorization columns/checks. Defaults leave existing rows on the legacy route. |
| `repo/checkouts.sql` | `repo-checkout-registry` | `repo-chunks` | Create the checkout registration table and uniqueness constraints in the target application schema. |
| same file | `repo-checkout-observations` | In-file predecessor | Add generation, availability, and Git observation columns/checks to that table. |

`public/` and `repo/` remain independent dependency graphs. The repo blocks have
no `requires` reference to public blocks; caller sequencing supplies that order.
Kryzhen creates each application schema and applies its template. There is no
AGE SQL, AGE graph creation, or AGE schema target in either new file. AGE
preparation continues through the existing application/API path, with readiness
checks added when that path is connected to family registration.

The two historical SQL files, including existing block bodies and headers, remain
byte-for-byte unchanged. New blocks do not backfill filesystem-derived identities,
enable indexing, change policy, copy chunks, update graphs, drop tables, or relax
legacy path uniqueness. Data import is a distinct, reviewed operation.

### Exact registry additions proposed for `public.repos`

Unspecified defaults below are SQL NULL. Existing columns and constraints remain.

| Column | Type/default | Contract |
| --- | --- | --- |
| `family_kind` | `text` nullable | `git` or `directory`; null until identity is imported. |
| `path_encoding` | `text` nullable | `unix-bytes` or `windows-utf16le`; see path contract below. |
| `family_key` | `bytea` nullable | Nonempty canonical common-directory/root bytes. |
| `retired_at` | `timestamptz` nullable | Logical family retirement; never schema deletion. |
| `schema_state` | `text NOT NULL DEFAULT 'pending'` | `pending`, `migrating`, `ready`, or `failed`; readiness is for the required application/AGE pair. |
| `schema_error` | `text` nullable | Sanitized preparation diagnostic; never credentials. |
| `storage_generation` | `text NOT NULL DEFAULT 'legacy'` | `legacy` or `snapshots`; changed only by the later verified cutover. |
| `indexing_enabled_at` | `timestamptz` nullable | Time authorization was recorded in this model, not an invented historical first-index time. |
| `indexing_enable_origin` | `text` nullable | `explicit-start` or `legacy-import`. |

Constraints/index:

- Identity columns (`family_kind`, `path_encoding`, `family_key`) are either all
  null or all present. Use explicit null checks so SQL's unknown truth value
  cannot permit a partially populated identity. Check allowed values and
  nonempty bytes independently.
- Unique index `repos_live_family_identity_idx` on
  `(family_kind, path_encoding, pg_catalog.sha256(family_key))` where `retired_at IS NULL` and
  `family_key IS NOT NULL`. Retired UUIDs/schema pairs remain historical; a new
  family can reserve the locator only after retirement is confirmed.
- Authorization timestamp and origin are both null or both present; check
  origin values. Registration/discovery never populate them.
- `schema_state = 'ready'` requires a complete identity. A `snapshots` selector
  requires a complete identity, but does **not** require the current state to
  remain ready: a later schema upgrade may fail while the selector must still
  prevent an unsafe fallback to legacy storage. Runtime gates deny access until
  required schema readiness is restored.
- Preserve `repos_path_key`. Its later removal must be a separately appended
  block after all path-upsert callers have been replaced. Do not insert that
  future block into an earlier dependency position.

These checks constrain metadata; they cannot prove that migrations or AGE
preparation actually succeeded. Only the coordinator may mark ready after
checking both. A later release rechecks its required template before use; a
stored `ready` value is not evidence that future migrations have run.

**Path contract.** Use native bytes on Unix and little-endian UTF-16 code units
on Windows, with the encoding tag. Do not case-fold, Unicode-normalize, trim, or
use lossy strings as lookup keys. Validate absolute canonical paths before
encoding. `public.repos.path` remains the original human-readable provenance
string; it never overrides the lossless identity. A future machine/OS relocation
is explicit, not a lookup under a different encoding. Byte-key storage avoids
losing the non-UTF-8 and newline paths already covered by discovery tests;
Windows path aliases/case behavior still require platform-specific verification.
Use fixed-size SHA-256 expressions for the identity indexes, retaining full bytes
in the rows. This avoids indexing arbitrarily long raw paths. Every lookup and
uniqueness conflict must compare the full bytes: equal digests with unequal bytes
produce an explicit collision error, never identity reuse. PostgreSQL 16 provides
[`sha256(bytea)`](https://www.postgresql.org/docs/16/functions-binarystring.html)
without a new extension. This does not relax the pre-cutover length/uniqueness
limits of the legacy text `repos.path` index; enabling new registration semantics
still waits for its separately reviewed cutover.

### Exact checkout table proposed for each application schema

`checkouts` initially contains only registration and observation metadata. Do not
add an unconstrained snapshot UUID placeholder: add the published-view column
with its real foreign key when the snapshot tables are introduced.

| Column | Type/default | Contract |
| --- | --- | --- |
| `id` | `uuid PRIMARY KEY DEFAULT gen_random_uuid()` | Stable DB checkout ID. |
| `root` | `bytea NOT NULL` | Nonempty canonical working-directory bytes, using the family's path encoding. |
| `git_dir` | `bytea` nullable | Canonical per-checkout administrative directory reported by Git; absent for an independent directory. |
| `incarnation` | `uuid NOT NULL DEFAULT gen_random_uuid()` | Registration token captured by jobs; a replacement cannot publish through a previous registration token. |
| `registration_state` | `text NOT NULL DEFAULT 'active'` | `active`, `suppressed`, or `retired`. |
| `paused` | `boolean NOT NULL DEFAULT false` | User pause, independent of Git blockers and first-family authorization. |
| `created_at` | `timestamptz NOT NULL DEFAULT now()` | Registration time. |
| `retired_at` | `timestamptz` nullable | Present exactly when registration state is `retired`. |
| `dirty_generation` | `bigint NOT NULL DEFAULT 0` | Nonnegative; increment on changes invalidating a build, including lifecycle changes. Never reset or wrap. |
| `availability` | `text NOT NULL DEFAULT 'unknown'` | `unknown`, `available`, or `unavailable`; missing files do not mean retirement. |
| `git_state` | `text NOT NULL DEFAULT 'unknown'` | `unknown`, `clear`, `blocked`, or `not-git`. |
| `merge_in_progress`, `rebase_merge_in_progress`, `rebase_apply_in_progress`, `unmerged_index` | `boolean` nullable | One detector observation, persisted atomically with its status and timestamp. |
| `observed_at` | `timestamptz` nullable | Time of latest inspection attempt. |
| `last_seen_at` | `timestamptz` nullable | Last successful filesystem/identity validation; not merely an enumeration hit. |
| `observation_error` | `text` nullable | Sanitized diagnostic for unknown/unavailable status. |

Constraints/indexes:

- Nonempty root; nonempty `git_dir` when present. Allowed enum-like values are
  CHECK constraints, not new database enum types. `incarnation` is unique within
  the schema. Paused/suppressed rows keep data; no cascade deletion is introduced.
- `checkouts_live_root_idx`: unique `pg_catalog.sha256(root)` where state is not
  `retired`. `checkouts_live_git_dir_idx`: unique `pg_catalog.sha256(git_dir)`
  where `git_dir IS NOT NULL` and state is not `retired`.
  Use the full-byte comparison/collision-error contract above for both indexes.
  Suppressed registrations retain their identity claim.
- `git_state = 'clear'` requires four non-null false blocker flags;
  `blocked` requires four non-null flags with at least one true. `unknown` and
  `not-git` require null flags. Clear/blocked/not-git require `observed_at`.
  Unknown is never schedulable. An indexing job must inspect again, not trust
  this historical observation as a publication guard.
- The registry transaction checks `git_dir` presence against the family's kind
  and permits only one non-retired checkout for an independent-directory family.
  Those are application invariants, **not** claimed as cross-table CHECKs.
  Root/identity uniqueness indexes provide the per-schema database backstop.
- Ownership comes from the target `repo_<family UUID>` schema. No redundant
  caller-supplied family ID is stored in each checkout row, and no query searches
  another family's tables for a checkout UUID. Family retirement keeps that
  schema; physical deletion remains a separate operation.

### Registration, lookup, and concurrency

Add narrowly scoped store entry points alongside the legacy functions:
`lookup_family`, `reserve_family`, `prepare_family`, `register_checkout`,
`lookup_checkout`, and `record_checkout_observation` (working names). Use new
`Family`, `Checkout`, and `ResolvedCheckout` types; the latter carries both IDs,
root, incarnation, readiness, and storage selector. Keep schema names derived
from validated family UUIDs and qualify every runtime table reference.

1. Resolve the supplied directory. For Git, discover canonical root/common-dir
   and additionally ask `rev-parse --absolute-git-dir` for the checkout's
   administrative directory. The `GitCheckout` helper now exposes and tests
   that field. Branch and HEAD
   are never identity keys. Non-Git registration uses its explicit canonical root.
2. Reserve or find the family under a registry transaction lock. A repeat request
   returns the same UUID; an incompatible dimension or policy is reported for
   configuration, not implemented by deleting/re-registering. Never silently
   merge two legacy rows with the same discovered family key.
3. Commit the reservation before template preparation. For a new family, use
   its fixed UUID/schema names throughout retries. Mark migrating, call Kryzhen
   for application templates, then prepare/check AGE independently. Preserve an
   existing graph; missing legacy graphs and namespace mismatches are errors.
   Mark ready only after both succeed; a crash leaves retryable non-ready state.
   The approved [JSON registration refinement](2026-10-04-family-policy-json-contract.md#12-json-registration-and-policy-writes--2026-10-04)
   stores creation intent with that reservation and retains the preparation lock
   through checkout registration and atomic policy-initialization/completion.
   Retry uses the stored initial policy/defaults; completed registrations never
   gain permission to recreate a missing AGE graph.
4. Under a registry transaction lock, revalidate family readiness, path identity,
   and live root ownership before inserting a checkout. Repeated discovery is
   idempotent. New checkout creation changes no chunks, graph, policy, or start
   authorization, and creates no schema or AGE graph.
5. Once the new runtime is connected, eligibility requires family authorization,
   a non-retired/unpaused family (using the existing `public.repos.paused` gate),
   ready schema pair, active/unpaused checkout, available directory, and a fresh
   clear/not-git inspection. Suppressed, retired, blocked, and unknown states
   cannot start work. The existing family-wide indexing lock can serialize jobs
   initially; checkout-level concurrency is not required by this slice.

Keep two distinct coordination scopes: a session advisory lock around **all**
Kryzhen invocations, including public/ledger initialization, and a transaction
advisory lock around registry/root-ownership mutations. Allocate documented
two-integer lock keys, distinct from the existing one-integer UUID-derived job
locks. Proposed lock order when scopes overlap: family job lock, migration lock,
registry transaction lock. Reservation uses the registry lock alone and releases
it before waiting for preparation; startup public migration holds only the
migration lock. Never acquire a family job lock while holding either global lock.
Use the migration connection itself to hold its session lock; cancellation must
release/drop that connection. Do not wrap Kryzhen's migration set in one outer
transaction. Concurrency and cancellation need integration tests.
PostgreSQL documents the disjoint one-integer/two-integer key spaces and lock
lifetimes in its [advisory lock API](https://www.postgresql.org/docs/16/functions-admin.html#FUNCTIONS-ADVISORY-LOCKS).

Observation/lifecycle updates match `(id, incarnation, dirty_generation)` and
return whether the update was accepted. A worker with an old token/generation
cannot overwrite an observation or publish after removal/re-registration. A new registration gets
new IDs; a verified move of the same checkout preserves its ID but rotates the
incarnation and increments generation. Explicitly lifting suppression also
rotates that token. All such transitions keep old snapshot roots until the later
publication/retention machinery can retire them safely.

Because checkout roots live in separate schemas, a global unique root index is
not available without another public routing table. Recommend keeping the
approved routing-only public registry: under the registry transaction lock,
check non-retired checkout roots across prepared families and unresolved legacy
paths. This costs a scan on registration/relocation, not on every Git lookup.
All mutation callers must use that lock; report this as an application guarantee.
An inaccessible/unprepared candidate family makes an ownership check unresolved,
not permission to claim the root. No SQL trigger into AGE is involved.

For non-Git `cwd` resolution, select the nearest registered ancestor by path
components after canonicalization, not a string prefix. A registered nested Git
family takes precedence over an enclosing directory registration; do not merge
their data. A read/search resolves existing registration only. Daemon discovery
handles automatic linked-checkout registration; an as-yet-unregistered checkout
gets an explicit pending/discovery-needed response, never another checkout's
results. Final response spelling remains part of the interface review.
If an independently registered directory later becomes a Git repository, report
that identity change and require explicit reassociation; do not silently allocate
or merge a family during lookup.

**Incarnation limitation.** Git administrative paths can be reused after prune
and recreation. A database UUID does not make that reuse detectable. Recommend
retiring an incarnation only after successful enumeration plus filesystem
reconciliation confirms disappearance. A newly observed registration after that
gets new UUIDs and no inherited published pointer. When an offline replacement
at the same root/admin paths is ambiguous, do not clear suppression or declare an
old snapshot current merely from matching paths/HEAD; verify the selected files
before publishing. An ambiguous suppressed checkout requires explicit `add`.
This slice writes no identity stamp into Git metadata. Guaranteed detection of
every unobserved same-path repository replacement would need a separate identity
mechanism; it is not a property of the current path-based discovery API.

### Compatibility, import, and recovery

The additive slice does not activate family routing. A compatibility build must
keep legacy registrations on their existing path until identity, policy, reader,
and snapshot support are ready. Preparing empty checkout tables alone must not
send multiple worktrees through the old flat pipeline. The old search API cannot
serve checkout-correct results merely because the family has been resolved.

The eventual external migration script first inventories registered paths,
settings, identities, graph/schema existence, and duplicate-family groups. It
stops on inaccessible/ambiguous identities and preserves existing UUIDs, chunks,
knowledge, config, and graphs. No filesystem identity is guessed by SQL. A
duplicate-family consolidation requires its own reviewed survivor/data plan.
This stage neither writes nor runs that script and does not inspect live data.

Recommended import rules, pending approval:

- Import the single existing checkout and preserve the existing family pause. For a family with
  `ever_indexed = true`, record `indexing_enabled_at` at import time with origin
  `legacy-import`. This preserves prior authorization without fabricating the
  first-index time. `ever_indexed = false` remains disabled unless explicitly
  started. Preserve the existing `public.repos.paused` value as a family-wide
  gate, so newly discovered worktrees cannot bypass it. The imported checkout's
  separate `paused` flag starts false; the family gate already preserves its
  effective pause, without introducing a second pause that would survive a
  family resume. Final pause/resume command semantics require interface review
  before enabling discovery.
- Initialize Git observation as unknown and re-inspect. Do not import
  `indexed_at` as proof that a new snapshot exists. Leave `storage_generation`
  as legacy until candidate snapshots and every reader are verified.
- Keep policy/knowledge migration, snapshot pointers, shared file-map DDL,
  embedding storage, and graph membership DDL out of this identity slice. Their
  existing review decisions are not implicitly resolved by this plan.

Before user-database execution: name the exact database, target schemas, service
quiescence, verified backup, expected writes, and recovery actions. No new
database/container is required. Kryzhen `dry_run` is not a read-only inventory:
the pinned library calls `ensure_schema` before checking that flag.

For a failed additive application, keep the legacy selector and retry through
Kryzhen; successfully committed blocks remain applied. Preserve the ledger—no
checksum edits, down-migrations, or manual history deletion. Before restarting
an old binary, verify that only additive metadata changed, legacy uniqueness
still holds, no conversion/new-format AGE objects or new-family writes occurred,
and old config/data are intact. After cutover or graph-format writes, that simple
recovery route no longer applies; use the reviewed compatibility reader or backup
procedure described below. Stopping new writers precedes any recovery.

### Decisions accepted for the additive implementation

| Decision | Recommendation in this plan | Tradeoff / alternative |
| --- | --- | --- |
| Scope of initial SQL | Add identity/lifecycle columns and checkout metadata only; retain legacy uniqueness and routing. | More than one implementation stage, but no premature reader or data cutover. |
| Path representation | Tagged native bytes in `bytea`. | Lossless paths; requires a small codec and platform tests instead of text-only SQL keys. |
| Existing indexing authorization | Import successful prior indexing as `legacy-import`; never-indexed families stay disabled. | Preserves working behavior; alternative is requiring explicit start again for every family. |
| Paused-family migration | Preserve the existing pause as a family-wide scheduling gate; new checkout-local pause flags start false. | Avoids an unexpected new worktree bypassing an existing pause or retaining a duplicate imported pause after family resume. |
| Root ownership coordination | Registry transaction lock and cross-schema metadata checks; no duplicate public checkout table. | Registration cost grows with family count; the alternative adds a public root-routing/ownership table. |
| Same-path recreation ambiguity | Require explicit add for ambiguous suppressed registrations; verify files before reusing any view. | Conservative rediscovery; guaranteed offline incarnation detection needs a separately agreed mechanism. |

### Implementation sequence and verification

Implement in bounded stages; stages 1 and 2 below are complete:

1. **Additive definitions and typed store operations.** Add the two migration
   files, path codec, admin-directory discovery, new DTOs, and metadata access
   methods. Preserve legacy call paths. Update formal contracts only for the
   approved identity/lifecycle refinements. Verify both migration sets parse and
   sort independently, names are globally unique, historical checksums remain
   unchanged, path codec round-trips, and the workspace compiles. These checks
   do not prove SQL execution or concurrency.
2. **Database verification with a separately agreed resource plan.** Test two
   independent application schemas and several checkout rows in one family;
   identical template replay/no-op retry; uniqueness and checks; concurrent
   reservation; readiness failures and retry; generation/incarnation rejection;
   and legacy register/read compatibility with the additive schema. Name the
   exact test database/schema/graph resources and cleanup before creating or
   changing them. Do not use existing tests that default to user configuration.
3. **Registration/configuration and snapshot integration.** Connect the new
   commands and daemon only after the relevant policy/view contracts are ready.
   Replace every path-upsert caller before appending the uniqueness-relaxation
   block. Worktree indexing/search requires actual snapshot support, not just
   metadata. Installation, user-data import, and service changes remain separate
   reviewed execution stages.

Verification: 27 focused Rust tests passed, including independent migration DAGs,
historical migration-file hashes, lossless native paths, admin-directory discovery,
and Git operation detection. Workspace compilation and diff checks passed. Tests
ran on Linux; the Windows-specific codec test has not been executed here. At that
stage SQL execution remained unverified. The subsequently approved isolated
database verification and its results are recorded below.

### Database test-resource inventory and execution proposal

Inventory completed read-only on 2026-10-04. The connection was taken from
`~/.config/muninn/config.toml`: `localhost:5450`, database/user `muninn`.
Catalog queries used `default_transaction_read_only=on`, bounded connection and
statement timeouts, and no application startup or migration calls. No database,
container, schema, role, config, or service was created or changed.

Observed resources:

| Resource | Observation |
| --- | --- |
| Running server | Container `postgres-ai`, PostgreSQL 16.11, published at `127.0.0.1:5450`. |
| Exact installed image | `sha256:79fb863620098b1e443338075bb65f6775130cbcb381f115d4272719256e334d`. |
| Application database | Nine registrations and nine AGE graphs; `public.repos` still has its original eight columns. |
| Installed extensions | AGE 1.6.0 in `ag_catalog`; pgvector 0.8.1 and pgcrypto 1.3 in `public`. |
| Application role | `muninn` is not superuser and cannot create databases or roles. It can create schemas in its database and has AGE usage privileges. |
| Other databases on that server | `ai_mem`, `chiron`, `mimir`, and `postgres`; no dedicated Muninn test database. These were identified from the database catalog, not inspected for application data. |
| Migration history | Existing `mallard` tables; `init` has one target association and `repo-chunks` has 239. Counts alone do not establish which historical associations should be removed; ledger repair is outside this task. |
| Proposed host port | `127.0.0.1:5451` was free at inventory time; recheck immediately before creation. |

The existing `graph_integration` and `tiered_indexing` tests load the global
configuration and write to the configured database. Do not run them as the
verification harness for this stage. The development shell's `muninn_test` URL
is a default string, not evidence that such a database exists.

**Approved and executed: create a disposable test server and database.** The user
approved these resources separately from the read-only inventory, then approved
using a shell runner and Rust tests. No Python files are to be added to the repo.
Testing only temporary repo schemas in the live database cannot exercise the
public migrations without altering its shared `public.repos` and Kryzhen ledger.
An outer rollback also does not verify the intended committed, multi-connection
retry/concurrency behavior. Recommend the isolated target below. Using the live
database instead would require a different plan with backup and service handling;
it is not authorized as a fallback.

#### Approved resources and lifetime

| Resource | Exact identity or allocation rule |
| --- | --- |
| Disposable container | `muninn-persistence-test-20261004`, created from the exact image ID above, with no pull or rebuild. Fail if the name already exists; do not replace another container. |
| Connection | `127.0.0.1:5451`, mapped to test-container port 5432. Never use port 5450. |
| New test database | `muninn_persistence_test`; created only inside that disposable container. |
| New test application role | `muninn_persistence_test`, LOGIN, database owner, non-superuser, no CREATEDB/CREATEROLE. |
| PostgreSQL data | Container-local tmpfs at `/var/lib/postgresql/data`, owned by image user 999:999; no host data directory or Docker data volume. Limit tmpfs to 512 MiB and container memory to 1 GiB. |
| Host fixtures and credentials | One newly allocated `/tmp/muninn-persistence-test-*` directory, containing temporary Git repositories and restrictive-permission test credentials. Record its exact path before use; never edit the user's global config or `.pgpass`. |
| Application schemas | `repo_<family UUID>` for fixture registrations only. UUIDs returned by reservation are recorded in a run manifest before calling repo migrations. At least two independent families plus a legacy compatibility fixture; linked checkouts share their family's schema. |
| AGE graphs/schemas | `code_graph_<same family UUID>` for those fixtures only, created through AGE's API. No graph per worktree and no Kryzhen migration into AGE schemas. |
| Other DB objects | Test-local `public` registry, extension objects, and `mallard` migration history; narrowly named failure/retry fixture objects if required by a test. All remain inside this test database. |

The image has a custom entrypoint, not the standard PostgreSQL Docker entrypoint.
For this test instance, override it with an explicit initializer using its
installed `initdb` and `postgres` binaries. Do not run its bundled application
initialization SQL. Initialize a fresh cluster with generated test credentials,
start PostgreSQL with AGE preloaded, and create the named test database/role.
Install the exact extension versions observed above. Grant the non-superuser
test role the public/AGE permissions used by Muninn's setup script. Administrative
credentials are used only for this bootstrap; migrations and store tests run as
the application role. Credentials are neither printed nor committed.

Creation includes the standard PostgreSQL maintenance/template databases produced
by `initdb`; no databases on the existing server are involved. The disposable
server has no restart policy and exists only for the verification run.

#### Test harness and expected writes

Add an explicitly invoked persistence integration test with an explicit test
connection configuration. It must not load `GlobalConfig` or fall back to a
development URL. Before any writes, verify the provisioned container identity,
endpoint, database/user names, versions, and expected initial catalog. Default
test runs must not start a container or connect to any database.

1. Use Kryzhen to apply the historical public template to the test database.
   Seed legacy fixture registrations, then apply the historical repo template to
   their UUID-derived schemas through Kryzhen. Seed small sentinel chunks and AGE
   objects through the existing data helpers/AGE API. Do not create application
   schemas manually.
2. Apply the new public and repo blocks through the library. Verify preservation
   of IDs, legacy data, path uniqueness, and legacy query behavior. Verify each
   application schema receives its own application records and no AGE graph is
   registered as a Kryzhen target. Reapply to verify no-op behavior.
3. Exercise family reservation, shared-family checkout registration, distinct
   non-Git families, lossless paths, constraints, suppression preservation, and
   rejection of unresolved legacy family collisions. Concurrent reservations must
   return one family ID; concurrent registration must not duplicate a checkout.
4. Exercise generation invalidation and outdated incarnation/generation rejection,
   unknown/blocked observations, and readiness refusal. Test-only setup may mark
   fixture readiness after verifying application migration and AGE preparation;
   this does not claim that the deferred runtime coordinator is implemented.
5. Inject a failure in a separate test-only migration suffix, leaving production
   block bodies unchanged. Check committed earlier blocks, non-ready state, and
   successful retry with the same body after repairing its test prerequisite.
   Keep migration invocations serialized as designed; concurrency tests concern
   the currently implemented registry operations.

This verifies persistence primitives and compatibility, not snapshot publication,
shared-file reuse, the future readiness coordinator, or end-to-end worktree
search. Defects in these primitives must be reported with failing evidence and
fixed within the accepted design; architectural changes require realignment.

#### Cleanup and verification

Capture test results and sanitized failure diagnostics before teardown. On normal
completion or failure, stop and remove only the manifest-identified disposable
container, then remove only the allocated host fixture/credential directory.
Deleting that container discards the entire test cluster and its migration
ledger together; do not manually repair `mallard` or run broad schema-drop loops.
If interrupted before cleanup, report the exact surviving container/directory
and finish that narrowly identified cleanup before calling the stage complete.

Verify the container is absent, its listener on port 5451 is gone, and temporary
credentials/fixtures are removed. A final read-only check of the configured
database must confirm the original registry column set and no new migration
names from this test. Registration/graph counts may change through independent
user activity, so counts alone are not proof of a mutation by the test.

No user-data backup/restore is needed for the proposed isolated run because it
does not write to the configured database. If the pinned image, port, credentials,
or permissions prevent this setup, stop and report the blocker; do not substitute
the live database, create a different persistent resource, or restart services.

#### Isolated verification results — 2026-10-04

Runner: `muninn-setup/test-persistence.sh`. Integration test:
`crates/core/tests/family_persistence.rs`. Explicit invocation:

```sh
nix develop --command bash muninn-setup/test-persistence.sh
```

The Rust test is ignored in ordinary test runs. It requires a private JSON
connection file from the runner, validates the exact test endpoint, database,
non-superuser role, PostgreSQL/extension versions, and per-run marker before
writes. It never loads global Muninn configuration. The runner verifies the
pinned container image, identifying label, port binding and absence of data
volumes. Its exit trap removes that identified container and allocated fixture
directory on success or failure.

Compilation, shell syntax and diff checks passed. A normal invocation of this
specific Rust test target reported one ignored test and made no database
connection. Historical SQL files and `store.rs` still match Git HEAD byte for
byte. Comparison with the stage-start file hashes found changes only in this
document and the metadata module's coverage comment, in addition to the two new
test files.

One sequential integration test passed, covering:

- Historical schema creation through Kryzhen; additive migration and replay.
- Preservation of legacy IDs, pause state, chunk content/hash/vector, full-text
  search and AGE symbol data; unchanged legacy path-upsert behavior.
- Refusal to duplicate an unresolved legacy family; explicit fixture identity
  import; main, linked and detached checkouts sharing one family schema/graph.
- Concurrent family reservation and checkout registration on separate
  connections returning the same identity, with no duplicate rows.
- Committed production migrations surviving a failing test-only suffix, then
  successful retry of the unchanged suffix after repairing its prerequisite.
- Readiness refusal, identity/lifecycle and observation constraints, generation
  invalidation, outdated incarnation/generation rejection, preserved suppression,
  and retirement retaining the old row while replacement gets a new incarnation.
- Separate directory families, including a Linux non-UTF-8/newline path;
  identical repo templates applied to three application schemas, with no AGE
  schema recorded as a Kryzhen migration target.

The first startup attempt exposed missing authentication rules for Docker's
bridge address in the fresh cluster. Editing the runner while it was still
running also caused a shell parsing failure; its exit trap completed cleanup.
The stopped runner was corrected and syntax-checked before the successful run.
The disposable cluster now explicitly permits SCRAM-authenticated connections;
its published host endpoint remains loopback-only. No production migration body
or persistence implementation required a fix from this run.

Both runs' allocated directories and the disposable container were confirmed
absent, and port 5451 had no listener. A final live read-only query reported
`transaction_read_only=on`, the original eight `public.repos` columns, zero new
migration names, nine registrations and nine AGE graphs. No installation,
service restart, user-data import or live migration was performed.

These results cover additive persistence only. Snapshot publication, actual
shared-file reuse, CLI/indexer integration and end-to-end worktree search remain
unimplemented. The subsequent coordinator stage is recorded next.

### Family preparation coordinator — 2026-10-04

Implemented in
[`family_store/preparation.rs`](../../crates/core/src/family_store/preparation.rs),
under the existing `Muninn.Schema` contracts; no formal model changes were
needed. The CLI, daemon and MCP still use their existing paths. Installing these
sources or routing existing callers through the coordinator is outside this
stage. Historical migration files and `store.rs` remain unchanged.

`PreparationConnection` owns a dedicated client and connection driver. Both
`prepare_public` and `prepare_family` consume it and acquire the session advisory
lock `(0x4d554e49, 2)` before any Kryzhen call. Family preparation commits
`migrating` under the registry transaction lock `(0x4d554e49, 1)`, then replays
public and application templates with Kryzhen's per-block transactions. It
verifies the required migration associations for that application's schema and
its physical namespace, then checks AGE separately. Stored `ready` never skips
these checks. The coordinator does not enable indexing, change storage
generation, import identities, register checkouts or publish snapshots.

Graph provenance is explicit at the API boundary:

- `GraphRequirement::Existing` is for imports, upgrades and revalidation. A
  missing graph is an error, with no empty replacement.
- `GraphRequirement::NewReservation` is only for a newly reserved family and
  retries of its initial preparation. The registration caller must retain this
  provenance; `storage_generation='legacy'` does not distinguish new from old.
  AGE creates a graph only if neither its expected catalog entry nor an orphan
  namespace exists. An existing valid graph is preserved.

Both paths verify the UUID-derived graph name maps through `ag_graph.namespace`
to the expected namespace. AGE alone creates the graph/schema; Kryzhen never
targets it. This stage establishes the model's graph mapping readiness; it does
not introduce future snapshot graph structures or replace legacy graph setup.

Only completion of application and graph preparation permits the registry
transition to `ready`. Failures record `failed` and a fixed stage diagnostic;
raw SQL/connection errors are not stored in `schema_error`. A lost connection or
interruption may leave `migrating`, which remains non-ready and retryable.
Earlier migration blocks stay committed. Lifecycle writes acquire the registry
lock after the migration lock; reservation releases its own registry lock before
calling preparation.

Cancellation owns both the driver and an unpolled cancellation future from the
same client's cancellation token, using the caller's transport/TLS policy.
Dropping an interrupted operation aborts the driver and sends a bounded
PostgreSQL cancellation request. The first implementation only aborted the
driver; the integration test demonstrated that a server waiting for an advisory
lock could outlive socket closure. The cancellation request corrected this.
Cancellation delivery is best effort if transport or the Tokio runtime is gone;
future runtime connection factories must preserve bounded server timeouts. The
test target uses statement/lock timeouts and NoTls; TLS cancellation has not been
exercised here.

The extended disposable integration test passed, including existing-graph data
preservation, two concurrent preparations of one family, missing-existing-graph
refusal, a real application-template failure, an AGE catalog lock failure after
application commits, successful retries, and cancellation both while holding
and waiting for the migration lock. Blockers stayed held while cancellation
release was verified. Retrying the interrupted `migrating` family succeeded.
No AGE schema appeared in Kryzhen's target ledger.

Workspace compilation (`cargo check --workspace --locked --offline`) and diff
checks passed. The unchanged formal model was read as the implementation
contract; no Agda proof or specification source was edited in this stage.

All coordinator test containers and temporary credential/fixture directories
were removed, with port 5451 free. The final live read-only check still found the
original eight registry columns, none of the new/test migration names, nine
registrations and nine graphs. No live migration or service change occurred.
The global locking guarantee applies to calls through this new coordinator;
legacy call sites are not yet routed through it and must be handled during the
separately approved runtime integration stage.

## Indexed-data storage: implementation withdrawn

The custom file maps, graph membership trees, object catalogs, snapshot builds,
and dependent capture/analysis implementation have been removed. The unshipped
`snapshots.sql` and `structure.sql` templates are removed, not replaced with new
migration definitions. Existing chunks/vector storage and AGE graph access remain.

Configuration and checkout tables from the retained stages are unchanged.
A replacement membership schema and its publication/search behavior require a
separate concrete review. The latest discussion favors ordinary relational chunk
associations and visibility attributes inside AGE; it is not an implementation.

One AGE graph/schema continues to accompany each family application schema.
Muninn prepares AGE through its API, separately from Kryzhen application-schema
migrations. The rollback does not drop graphs or alter live database objects.

The required behavior remains: independent checkout results, reuse of unchanged
analysis, visibility filtering before ranking/limits, all same-name resolver ties
with caller-file preference, and retaining the last completed view during an
incomplete Git operation. No physical tree or root layout is prescribed here.

## Detecting Git operations

Use native Git to resolve common/per-worktree administrative paths; do not
assume `.git` is a directory or parse loose refs exclusively. Observe source
changes and relevant per-worktree metadata, and periodically rediscover worktrees
and inspect their state. Proposal: a 60-second reconciliation interval plus
immediate event scheduling; tune the debounce after measurement.

Detect in-progress merge/rebase state through the paths resolved by
`git rev-parse --git-path` for `MERGE_HEAD`, `rebase-merge`, and `rebase-apply`,
and detect unresolved index stages using porcelain-v2 status or `ls-files -u`.
Detector tests must cover both rebase backends, paused edits, conflicts, continue,
skip, abort, missing metadata, and Git's per-worktree path routing. Treat an
inspection error as unknown: keep the previous view stale and retry.

The discovery module now exposes `inspect_git_operation_state`. It resolves each
marker with Git, checks markers before and after reading the unmerged index,
and verifies that the checkout root/common-directory identity still matches.
Its result records merge, each rebase backend, and unresolved-index blockers
separately. A missing operation marker is normal; Git failures, filesystem
inspection errors, and a missing or mismatched checkout return an error, not a
clear state. The `rebase-apply` marker also conservatively covers `git am`.

This is a read-only observation, not an atomic view of Git or a publication lock.
Runtime integration must retain the last snapshot as stale while blocked or
unknown, remain pending if no prior snapshot exists, and recheck Git state and
checkout generation before publishing. The detector alone does not implement
snapshot retention or eliminate races with Git operations. It is not yet wired
into the watcher or indexer.

Temporary-repository tests cover both rebase backends with continue/skip/abort,
interactive edit stops, merges with and without conflicts, resolved-but-unfinished
operations, conflicts remaining after `merge --quit`, ordinary local edits,
per-worktree isolation, corrupt-index errors, and lost checkout metadata.
Git's documented interfaces are
[`rev-parse --git-path`](https://git-scm.com/docs/git-rev-parse#Documentation/git-rev-parse.txt---git-pathltpathgt)
and [`ls-files --unmerged`](https://git-scm.com/docs/git-ls-files).

A normal fetch only schedules a lightweight state comparison. If neither actual
files nor the selected view context changed, it performs no analysis. Pull follows
its integration result. A commit/rebase that changes history but preserves bytes
can reuse compatible indexed data. Dirty-generation changes invalidate work even if
HEAD did not move, as with an uncommitted merge result.

Optional hooks send only a checkout-specific wake-up notification. They do no
parsing, embedding, or schema work and must not delay Git. Hook installation is
explicit and must coexist with existing hooks. Absence or failure of a hook
cannot disable reconciliation. Users see stale/suspended results during an
operation and automatic resumption afterward; normal local edits remain indexed.

## CLI, JSON, and TUI contract

The [family policy and JSON contract](2026-10-04-family-policy-json-contract.md)
refines the proposed storage, identity guards, validation, impact categories,
preflight bounds and implementation sequence below. Its remaining concrete
choices were approved for the core policy implementation recorded there. Runtime
activation remains separate; no behavior changes merely because it is described.

Command spellings here are proposals for review. All JSON commands are
noninteractive, emit one JSON response on stdout, and put diagnostics/progress on
stderr. Requests and responses carry `api_version: 1`; unknown fields and invalid
policy keys fail validation. Paths resolve to a checkout and then its family.
No operation reads or writes a per-repository `.muninn.toml` after cutover.
Existing `config get/set --repo` operations route nonsecret family fields through
the same DB validation/update service. A single-field set reads the revision,
constructs the complete candidate, and fails on a concurrent update. Requests
to edit a repository file explain the migration and point to the native TUI.

| Proposed command | Contract |
| --- | --- |
| `muninn add PATH` | Register a family if absent, associate the checkout, then open the initial-policy TUI/preflight. Registration itself never indexes. Existing family: reuse its policy/schema. |
| `muninn add PATH --json` | Register with stored/default policy, return IDs, policy revision, preflight, and actual indexing state; new families are unstarted. An optional `--input -` accepts an initial complete policy for a new family only. No implicit start. |
| `muninn config PATH` | Open the same TUI with the current family policy; display the family-wide effect of changes. |
| `muninn config PATH --json` | Inspect the current policy, immutable defaults revision, IDs, and indexing state. No writes or migrations. |
| `muninn config PATH --check - --json` | Validate a candidate JSON policy and run preflight without saving or indexing. Also usable against an unregistered directory with defaults supplied. |
| `muninn config PATH --apply - --json` | Validate and atomically replace policy against expected revision; increment revision only on an actual change. Existing started checkouts become stale and are scheduled for reconciliation. |
| `muninn preflight PATH --json` | Inventory under current/default policy without parsing/embedding; works before registration. |
| `muninn start PATH --json` | Explicitly enable the family's first indexing and queue the selected checkout; discovery schedules its other eligible checkouts automatically. Git suspension and user pause remain effective; report pending/suspended truthfully. |
| `muninn reindex PATH` | Explicit indexing request; can serve as first start for compatibility. `--all` only visits already-started families. |
| `muninn pause/resume PATH` | Affect the selected checkout's background work. Resume does not bypass Git suspension or enable a never-started family. A separate explicit family scope may affect all checkouts. |
| `muninn status [PATH] --json` | Show family and checkout state, published snapshot, policy revisions, freshness, reason, progress, and actionable diagnostics. No writes or migrations. |
| `muninn remove PATH --checkout/--family` | Require explicit removal scope. Preview affected data before deletion; JSON requires an explicit confirmation argument. Never infer family removal from the original checkout's path. |

A config apply request is a complete nonsecret policy document, not JSON Patch
or a pseudo-file editor. For example, the proposed request shape is:

```json
{
  "api_version": 1,
  "expected_family_id": "ad2d18aa-c26b-45f1-9b31-8f8232be5d7f",
  "expected_revision": 7,
  "policy": {
    "name": "example",
    "index": {
      "exclude": ["**/node_modules/**", "**/target/**", "**/.direnv/**"],
      "vendor": ["vendor/**"]
    },
    "watcher": {"debounce_ms": 500},
    "embeddings": {"backend": "voyage", "model": "voyage-code-3", "batch_size": 64}
  }
}
```

The values illustrate the wire shape, not a proposed change to the user's
settings or a guarantee that a specific backend is configured. DB credentials,
API keys, machine-local cache paths, and vector dimension are rejected as family
policy fields. They remain in the local bootstrap/credential mechanisms, or in
the migration-controlled schema contract. Agents obtain valid backend/model
choices and field constraints from the inspect response.

The refined contract proposes requiring `expected_family_id` alongside
`expected_revision` when applying changes to an existing family, preventing a
request from targeting a replacement registration at the same path.
Initial-policy input to `add` omits it; if the family already exists, supplying
that input returns a conflict and directs the caller to inspect/configure it.
Validation for an unregistered directory also omits it. Candidate validation
never reserves a revision; apply/start must still check the current revision.

The response to inspect includes `policy`, `effective_policy`, `revision`, and
`defaults_revision`. Preserve ordered last-match-wins exclude/vendor semantics;
exclude wins over vendor. Migration freezes the effective existing defaults and
user rules so an upgrade does not silently change selection. The update path
performs its revision comparison and write in the same DB transaction. A stale
revision returns `revision_conflict` with the current revision, without a write.
Malformed globs fail validation, rather than silently producing an empty filter.

All successful JSON responses use `{api_version, ok: true, data}`; failures use
`{api_version, ok: false, error: {code, message, details}}` and a nonzero exit.
Proposed stable error codes include `invalid_policy`, `revision_conflict`,
`not_registered`, `schema_not_ready`, `dimension_migration_required`,
`git_state_unknown`, and `scope_required`. Suspension and an incomplete preflight
are explicit state/results, not successful completion of indexing. Agents can
provide `expected_policy_revision` on start to reject a stale preflight decision.

The TUI exposes actual controls for exclude/vendor lists, name, watcher settings,
and backend/model choices. It shows the effective rules and preflight, and offers
Start, Edit policy, Ask an agent, and Leave unindexed. Ask an agent displays the
JSON workflow; it does not launch an agent or send messages. For a started family,
show that a policy change affects all linked worktrees and will schedule reindexing.
Bootstrap initialization remains a separate local-connection workflow.

### Preflight

Use the same filesystem selection rules as indexing, but only enumerate and stat
files; no parsing, hashing of full content, graph construction, or embedding.
Report discovered/eligible/excluded counts, tier counts, total eligible bytes,
largest files, costly directories, unsupported/unreadable paths, scan completeness,
and an advice code with reasons. Counts are observations, not a locked snapshot.

Proposed initial advisory triggers, to measure before release: over 10,000 eligible
files, over 100 MiB eligible content, any eligible file over 10 MiB, or substantial
eligible `node_modules`, build output, `.direnv`, or virtual-environment content.
These are advice thresholds, not hidden exclusions or indexing limits. An
incomplete or unreadable inventory recommends review, never an unqualified
"start now". A time-bounded inventory labels its counts as lower bounds.
TUI and JSON use the same report. No advice automatically starts indexing.

## Search response compatibility and user documentation

Retain existing `results`/`symbols` fields and result item shapes. Add a `snapshot`
object to every code search response; for example:

```json
{
  "results": [],
  "snapshot": {
    "family_id": "00000000-0000-0000-0000-000000000001",
    "checkout_id": "00000000-0000-0000-0000-000000000002",
    "id": "00000000-0000-0000-0000-000000000003",
    "freshness": "stale",
    "indexing": "suspended",
    "reason": "git_rebase",
    "policy_revision": 7,
    "indexed_at": "2026-10-03T12:00:00Z"
  }
}
```

The example's empty results do not imply an absent snapshot; stale searches still
return matching retained chunks. With no published view, `id`/`indexed_at` are
null, freshness is `pending`, and code results are empty. Distinguish Git
suspension, user pause, indexing in progress, missing checkout, and analysis
failure. The snapshot's policy revision/profile describe the data actually
served; expose a newer desired policy revision separately when catching up.
Knowledge responses identify their family scope and do not imply that a code
snapshot's staleness invalidates curated notes.

The shipped worktree/configuration/troubleshooting docs must explicitly say:

> During a merge, rebase, or unresolved conflicts, Muninn keeps serving the last
> indexed snapshot and marks it stale. It does not index intermediate conflict
> files. Results and line numbers may differ from the files on disk. Indexing
> resumes automatically after completion or abort. Other worktrees are unaffected.

Also explain no-snapshot pending behavior, optional hooks, the explicit first
start, family-wide policy, and how an agent inspects and applies JSON policy.
Existing clients that ignore new fields keep their result shape, but agent setup
instructions must teach the meaning of stale results. No silent claim that old
clients will understand the added freshness information.

## Worktree disappearance and explicit removal

A failed scan, inaccessible mount, or prunable Git entry is not proof of deletion.
Keep the snapshot and report unavailable/unknown. Confirm disappearance with a
successful Git worktree enumeration and filesystem reconciliation. Retire the
checkout mapping only after that evidence; retain roots needed by readers,
other checkouts, or recovery. Moving the Git common directory requires an explicit
registry relocation decision; do not adopt another repository based on basename.

An explicit checkout removal records a suppression entry for its Git identity
and registration incarnation, so automatic discovery cannot immediately undo the
user's action. `add PATH` can explicitly clear that suppression. A newly created
worktree with a distinct identity is discovered normally. Identity reuse after
Git prune/recreation needs a reconciliation test; path equality alone must not
revive the removed registration's snapshot.

Explicit family removal stops new jobs/queries for that family, quiesces existing
work, lists policy/knowledge/snapshots affected, then retires the family. Actual
schema/data deletion is a separately confirmed destructive action. AGE graph
deletion uses its API; its internal schema is not dropped through Kryzhen.
Any cleanup of application-schema Kryzhen associations must use the library's
supported bookkeeping functions, not direct writes to `mallard`. A new family always receives a fresh
UUID; never reuse a dropped schema identity with stale migration associations.

## Migration organization and cutover

Suggested semantic files, with multiple related migration blocks in each:

| Location | Group and dependency |
| --- | --- |
| `public/families.sql` | Add family identity, readiness, and generation fields. First block requires existing `init`; append path-uniqueness relaxation only in the later compatible cutover stage. |
| `repo/checkouts.sql` | Checkout registration and observation metadata; first block requires existing `repo-chunks`. No snapshot placeholders or AGE objects. |
| `repo/configuration.sql` | Retained family policy revisions; first block requires `repo-checkout-observations`. |

The three files above remain in the working tree and have earlier disposable-test
coverage. The unshipped storage templates were removed by the focused rollback;
no live database migration or rollback is performed by that source removal.
Existing `001_init.sql` and `001_chunks.sql` stay byte-for-byte unchanged. Newly
appended blocks have globally unique semantic names, with `repo-` names for
repo templates. Dependency ordering comes from `requires` and within-file
implicit dependencies, never numerical filename prefixes. No ledger repair,
checksum override, or rewriting already-applied blocks is part of this plan.
Each directory is loaded independently as one dependency graph for one target
schema. There is no graph-schema migration directory: AGE manages that schema
through its API. New and existing family graphs are prepared and checked by
Muninn separately from these application migrations.

### Proposed user-specific migration procedure

The script is later created outside the Git repository. Before execution it must
show exact target DB identity, family IDs/schema names, affected services, backup
paths, expected writes, and recovery actions. This document authorizes none of
those effects. No additional database or container is needed for the migration.

1. **Read-only inventory and plan.** Read registrations, existing settings,
   schema/graph names, version compatibility, and duplicate-family collisions.
   Produce a local reviewable plan with secrets omitted. Do not call
   `kryzhen::migrate(..., dry_run=true)` for this phase: it calls `ensure_schema`
   and may initialize its ledger despite skipping migration bodies.
2. **Quiesce old binaries and take a verified backup.** Old binaries do not know
   the new generation selector and their unrestricted graph reads can see the
   new format. Name every CLI/daemon/MCP reader and writer in the execution plan.
   Keep original config files,
   old binaries, old chunks/AGE graphs, and old knowledge for recovery. Verify
   backup readability and document the restore command before writes.
3. **Apply new template blocks through the library.** Public first, then each
   existing family schema under migration serialization. Check canonical
   checksums and each target's application report. Partial block completion is
   resumable. Separately validate the existing AGE graph through its lifecycle
   path, preserving contents. A family stays non-ready until both operations
   succeed; a Kryzhen application report alone cannot establish graph readiness.
   The proposed compatibility reader can serve old data after schema gates pass;
   it must explicitly exclude the new graph format. Review and test that path
   before backfill, or obtain approval for a maintenance interval.
4. **Backfill independently per family.** Import effective nonsecret policy and
   notes preserving UUIDs. Read stable files; legacy chunk hashes cannot recover
   whole-file identity. Do not relabel old chunks as current without validation.
   The exact backfill procedure depends on a replacement storage design; the
   previous shared-root implementation is withdrawn. Preserve legacy tables.
   Collisions between policies/IDs from separately registered worktrees require
   a reviewed resolution, never last-write-wins merging.
5. **Verify candidates and switch explicitly.** Compare visible paths, sampled
   chunk contents/ranges, all graph relation modes, policy/preflight equivalence,
   and reuse counts. Transactionally select the new storage generation and
   checkout snapshot pointers after generation/Git-state checks. Start the
   reviewed new binaries only after all required schema gates pass.
6. **Recovery and cleanup.** A pre-cutover failure leaves legacy data selected.
   After cutover, stop new writers before restoring old binaries/configuration.
   The original binaries cannot safely read a graph containing both formats;
   use the reviewed compatibility reader or restore/clean up new-format objects
   before restarting those binaries. The specific graph-format cutover remains
   undefined following withdrawal of the previous AGE snapshot design.
   New configuration or knowledge writes require export/reconciliation; old
   recovery copies do not contain those later changes. Prefer forward repair
   or the reviewed backup restore over pretending rollback is lossless. Removal
   of legacy tables, obsolete graph contents, config copies, and recovery pins
   is a later, separately approved cleanup. The retained family AGE graph/schema
   must not be dropped while it serves current snapshots.

The proposed relaxation of legacy path uniqueness is a compatibility change,
even though existing migration bodies and indexed data are preserved. Recovery
must check for duplicate provenance paths before restoring that constraint or
running an old binary that treats `public.repos.path` as authoritative.

Fresh registrations still pass through immutable historical templates before new
blocks. Empty legacy tables may therefore remain initially; AGE continues to be
required. Eliminating that history is outside the append-only migration
agreement. Do not create a different DB or bypass Kryzhen to avoid it.

## Verification gates for implementation

No database or benchmark was run for this design stage. The later test stage must
first name its existing or proposed resources, lifetime, and recovery plan.

| Gate | Required observation |
| --- | --- |
| Family schemas | Two independent families have distinct application/AGE pairs; several worktrees of one family create no additional schema or graph. Kryzhen creates application schemas; AGE creates graph schemas through its API. |
| Template replay and AGE readiness | Same bodies apply independently to each family's application schema. Repeat application is a no-op. AGE preparation is separate and preserves existing graphs. Failure in either path leaves the family non-ready; retry handles committed earlier operations without falsely recording graph work in Kryzhen. |
| Unchanged reuse | A clean worktree reuses chunk data and embeddings with zero new parse/embed calls; membership references may be recorded separately. |
| Checkout updates | Change, rename, delete and revert affect only the selected checkout; no prefix/radix tree is permitted. |
| Main advances | Pull in main changes none of another checkout's results, ranges or graph. Referenced data remains available. |
| Git suspension | Both rebase backends, paused edits, conflicts, abort/continue, and operation starting during a build retain prior roots and expose stale/pending; no known-blocked publication. |
| Local-file truth | Dirty/untracked/Git-ignored-but-included files, filters, sparse checkout, and selection changes produce the actual selected filesystem view. |
| Graph context | An unchanged caller changes its resolved edges when a visible callee changes; new definitions also update formerly unresolved callers without reparsing them. |
| Search | Visibility precedes limit/ranking; same version at two paths is not collapsed. Compare exact retrieval with independent visible-only queries; measure latency. |
| Concurrency/GC | Readers and active builds survive publication and GC; stale workers cannot publish; interrupted builds can be retired safely. |
| Configuration | TUI and JSON produce the same validated policy; stale revision fails without writes; preflight never starts/parses/embeds; explicit start is preserved. |
| Migration/recovery | Old blocks/checksums unchanged, policy and note IDs preserved, collisions reported, interrupted backfill resumable, rollback limitations exercised. |

The rejected physical storage design is withdrawn. Registration/configuration and
schema ownership remain; replacement membership and runtime implementation need
a fresh bounded proposal. The Agda model expresses logical contracts and does
not justify the deleted storage representation.
