> **Historical design/stage record.** This document preserves proposals and
> progress reports from its date, including superseded decisions. It is not
> a current installation procedure or completion report. For implemented 1.0 behavior,
> see [Development](../../docs/development.md); for installation, see
> [Getting started](../../docs/get-started.md) and [AGENTS.md](../../AGENTS.md).

# Muninn 1.0.0: family policy and JSON configuration contract

Status: **policy persistence, JSON read/write and native configuration TUI completed, 2026-10-04; start/runtime integration pending**.
The remaining dependencies and next proposed stage are mapped in the
[runtime integration plan](2026-10-04-runtime-integration-plan.md).
The initial stage specified this contract in documentation. The user then
approved the formal model, core JSON validation and policy persistence, with
verification in the agreed disposable database. Implementation results and
remaining runtime boundaries are recorded below. No live migration or installed
configuration change is authorized by this stage.

This refines the accepted [worktree proposal](2026-10-02-worktree-indexing-proposal.md)
and the [storage/interface design](2026-10-03-worktree-storage-design.md).
Accepted product requirements remain authoritative; the concrete choices below
were approved for this implementation sequence. No user-specific migration script belongs
in Git.

## 1. Accepted requirements and current evidence

- One policy per Git family, shared by all worktrees; one policy per independent
  non-Git directory. Store it in that family's application schema.
- One local bootstrap file, `~/.config/muninn/config.toml`, supplies the database
  connection, credentials and machine-local settings. No per-repo config file
  remains after cutover. This is not a change to the connection currently used.
- Human configuration uses native TUI controls. Agents inspect, validate and
  submit JSON. Both use the same policy service; neither edits a pseudo-file.
- `add` and `config` remain separate commands. Registration/configuration never
  enables first indexing. TUI asks whether to start; JSON requires explicit start.
  Worktrees of an enabled family are discovered/indexed automatically.
- Preflight enumerates files and reads metadata cheaply, recommending start or refinement.
  It performs no parsing, full-content hashing, embedding, or graph construction.
- Ordered exclude/vendor rules retain last-match-wins negation; exclusion wins
  over vendor classification. Vendor content is still indexed.
- Changes use atomic revision comparison. Preserve old views until their valid
  replacements are published; never change another checkout's snapshot in place.

Evidence read for this contract:

| Current source | Consequence |
| --- | --- |
| `config.rs`: `EffectiveConfig::merge` | Currently merges shipped, global and repo rules on every load. Stored family defaults must replace that evolving input after cutover. |
| `pipeline.rs`: `build_excludes` | Currently trims rules, skips empty rules and warns/continues on invalid globs. New policy validation must reject invalid/empty rules before persistence. |
| `pipeline.rs`: `index_repo` | Disables standard ignore filters, always skips `.git`, and prunes excluded directories. Preflight must expose the same selection, including Git-ignored content. |
| `config.rs`: shipped vendor defaults | `node_modules`, build outputs and virtual environments are vendor content, not excluded. Preserve these defaults; expose their cost and let the human/agent choose exclusions. |
| `embeddings.rs`: `expected_dimension` | Dimension is currently inferred from backend, not independently verified for every arbitrary model string. Do not present arbitrary model names as validated compatible selections. |
| `spec/Muninn/Config.agda` | Models shared policy, glob ordering, frozen dimension and increasing revisions. Its effective-config function currently reads module constants rather than a per-family defaults snapshot. |
| `spec/Muninn/Cli.agda` | Models common TUI/JSON intents, read-only preflight, stale-write refusal and explicit first start. Exact flags and wire shapes remain implementation refinements. |

## 2. Policy document and frozen defaults

A complete editable policy contains exactly these fields:

| Field | Contract |
| --- | --- |
| `name` | Nonempty display string. Does not rename filesystem paths, schemas or family identity. |
| `index.exclude` | Ordered array of glob strings appended to that family's stored default exclude rules. |
| `index.vendor` | Ordered array appended to stored default vendor rules. Applies only to files surviving exclusion. |
| `watcher.debounce_ms` | Nonnegative integer milliseconds, representable by the runtime duration type. Zero means no debounce. |
| `embeddings.backend` | Supported backend identifier (`voyage`, `openai`, `local`). |
| `embeddings.model` | Required nonempty string for remote backends; JSON `null` for the bundled local model. Its actual bundled model identity appears in effective policy/capabilities. |
| `embeddings.batch_size` | Positive integer within the selected backend adapter's supported range. |

Reject unknown fields recursively, duplicate JSON object keys, wrong types,
missing required fields and numbers outside the published ranges. Connection
settings, API keys, cache paths, family IDs, dimensions and lifecycle flags are
not editable policy fields. Do not silently coerce strings to numbers.

`policy` contains explicit scalar settings and family rule arrays. An empty
array means no family additions; it does not erase stored default rules. To
reverse a default, add an explicit negation. `effective_policy` includes the
stored defaults followed by these arrays and reports each rule's origin/order.
Preserve array order and duplicates. Object key order is irrelevant to equality.
Pattern matching keeps the existing outer-whitespace trimming semantics, but
validation rejects a rule whose trimmed form is empty or a bare `!`, and reports
its JSON field/index. Preserve submitted strings for inspection.

Excluded directories are pruned. A child negation alone does not reopen a pruned
parent: the parent must also be included. `.git` administration entries remain
unconditionally outside inventory/indexing, independent of negated rules. Use
one strict rule compiler and classifier for candidate validation, preflight,
full indexing and watcher checks; do not maintain a second glob interpretation.

Each family stores an immutable defaults snapshot, identified by a semantic
`defaults_revision`. New families use the current shipped snapshot. Existing
families never re-read a newer binary's defaults automatically. Scalars are
materialized in the initial policy, rather than dynamically inherited.
The reviewed import later freezes the old effective selection: preserve old
shipped defaults and append the old global and repo rule arrays in their
original order. No import runs in this implementation slice.

Recommendation: defer user-wide DB policy overrides and an explicit
adopt-new-defaults operation. They are not needed for initial family policy;
changing global bootstrap settings must not silently update registered families.

## 3. Storage and initialization

Add semantic migration file `migrations/repo/configuration.sql`, with a
`repo-family-policy` block depending on `repo-checkout-observations`. It belongs
to the existing repo template DAG. Apply identically to each application schema
through the Kryzhen library. No AGE objects or public policy tables are added.

| Table | Proposed contents |
| --- | --- |
| `policy_defaults` | `revision text` primary key, immutable nonsecret defaults document, document format version. |
| `policy_versions` | Positive revision primary key, complete validated policy JSONB, defaults revision FK, format version, recorded timestamp. Stores the initial version as well as every changed version. |
| `family_policy` | Exactly one current-policy row (constant singleton key), current revision FK to `policy_versions`. No duplicated mutable policy JSON. |

The registry UUID/schema binding supplies family identity; policy JSON cannot
select a different family. The existing `public.repos.name` remains a legacy
compatibility field until routing/import is implemented. New policy readers use
`policy.name`; this slice does not rewrite legacy registry names.

Migration creates tables/constraints only. It does not invent a policy for old
registrations or import TOML. A typed initialization operation explicitly creates
the defaults row, policy revision 1 and current pointer in one transaction.
A repeated initialization with identical defaults/policy is a no-op; different
initial input returns `policy_already_initialized`. Serialize initialization and
updates with the registry transaction lock, acquired after any preparation lock.
An initialized policy is an additional runtime prerequisite: schema `ready` alone
does not mean a family has been configured.

History/default rows are append-only through the service, with database triggers
rejecting ordinary UPDATE/DELETE. Future retention requires a separate reviewed
operation respecting snapshot references. JSONB storage does not substitute for
strict typed validation; SQL constraints also check basic document shape,
allowed fields, revision bounds and FK consistency.

## 4. Apply transaction and effects

Recommended wire revisions are positive JSON integers no larger than
9,007,199,254,740,991; SQL uses bigint with the same bound. This keeps comparisons
exact in common JSON clients. Overflow fails without wrapping or writing.

For an existing family, require both `expected_family_id` and
`expected_revision`. The extra identity guard prevents an old request from
updating a replacement family at a reused path whose revision happens to match.
Resolve the path again and check identity under the registry transaction lock.
A stale revision fails even when the supplied document equals today's policy.

1. Parse/validate the complete candidate without database mutation or network
   embedding calls. Read-only check can report missing credentials separately.
2. In one transaction, check non-retirement, schema readiness, policy presence,
   expected family ID and current revision. Revalidate dimension/profile guards
   against authoritative stored values.
3. Compare typed documents. Exact equality returns `changed: false`, with no new
   history row, generation bump or notification. No-op is not a `PolicyUpdate`
   transition in the formal model.
4. For a change, insert revision `N+1` and advance the singleton pointer
   atomically. Include the impact classification in the response.
5. Every real policy change invalidates active/suppressed checkout build tokens
   by incrementing their dirty generation in the same transaction. Retirement
   is preserved. Do not erase existing snapshots or enable/clear pause flags.
6. Emit a transactional notification after successful changes. A notification is
   only a wake-up hint; persisted revision/generation drives reconciliation after
   a missed notification or daemon restart.

Recommended impact distinctions:

| Change | Effect after runtime integration |
| --- | --- |
| Name | Display metadata reconciliation; reuse existing file/graph artifacts, with no reparse/re-embedding. |
| Debounce or embedding batch size | Reload runtime settings and reconcile policy metadata; reuse existing file/graph artifacts. |
| Exclude/vendor rules | Invalidate selection/tier views for all live checkouts; reconcile enabled eligible checkouts. Reuse compatible content/embeddings. |
| Backend/model | Require an explicit reindex acknowledgement; dimension changes remain a separate migration. Never reuse incompatible vectors. |

Keep the existing publication guard against an obsolete captured policy
revision, even for metadata-only edits. Such edits may require a cheap new view
referencing unchanged roots; they do not justify reparsing/re-embedding content.
Do not weaken publication checks or claim a snapshot was produced under a
revision it never used. Freshness reporting continues to show actual and desired
policy revisions until reconciliation completes.

For started families, propose `acknowledge_reindex: true` on a request changing
the embedding profile, even at the same dimension. Without it, return
`reindex_required` without writes. For an unstarted family there is no old view
to rebuild, but dimension compatibility still applies. An acknowledgement never
starts an unstarted family. Until profile-aware snapshot writers/readers are
integrated, the policy service refuses backend/model changes with
`profile_change_not_supported`; initial selection remains available at creation.
This prevents the isolated persistence slice being mistaken for a working model
migration. Capability responses expose this restriction.

## 5. JSON and command contract

Retain the proposed path-based command forms in the storage design:

| Operation | Behavior |
| --- | --- |
| `muninn add PATH --json [--input -]` | Register using defaults or complete initial policy, initialize only a new family, return state and preflight. Existing family without input is idempotent; initial input for it conflicts. |
| `muninn config PATH --json` | Inspect stored/effective policy, revision, defaults and capabilities. Read-only: no migrations, registration or filesystem writes. |
| `muninn config PATH --check - --json` | Validate candidate and return impact/preflight without saving. For an unregistered directory, supply complete policy and current shipped defaults. |
| `muninn config PATH --apply - --json` | Compare-and-swap the complete policy. No file editor or JSON Patch. |
| `muninn preflight PATH --json` | Inventory with current policy, or creation defaults before registration. |
| `muninn start PATH --json` | Explicit start; accepts expected family/policy identity from preflight and rechecks it before recording authorization. |

An apply request, illustrating shape rather than user configuration:

```json
{
  "api_version": 1,
  "expected_family_id": "ad2d18aa-c26b-45f1-9b31-8f8232be5d7f",
  "expected_revision": 7,
  "acknowledge_reindex": false,
  "policy": {
    "name": "example",
    "index": {"exclude": ["**/node_modules/**", "**/target/**"], "vendor": []},
    "watcher": {"debounce_ms": 300},
    "embeddings": {"backend": "local", "model": null, "batch_size": 64}
  }
}
```

An inspect result is `{api_version: 1, ok: true, data: {...}}`; data includes:
`family_id`, selected `checkout_id` if registered, `revision`, `defaults_revision`,
`policy`, `effective_policy`, current indexing/pause/readiness state, and
`capabilities`. Capabilities identify allowed fields, integer ranges, rule
semantics, supported backend/model selections, immutable dimension, credential
availability (never values), and operations not yet supported. Do not hard-code
an arbitrary remote model list or claim network/model validation during inspect.

Apply returns the same authoritative policy identity plus `changed`, impact and
whether reconciliation is needed/eligible. It never reports indexing completed.
Errors use `{api_version: 1, ok: false, error: {code, message, details}}` and a
nonzero exit. Recommend exit 2 for request/validation errors, 3 for identity or
revision conflict, 4 for lifecycle/capability refusal, and 1 for operational
failure. Emit one JSON document on stdout; progress goes to stderr.

Codes include `invalid_request`, `invalid_policy`, `family_conflict`,
`revision_conflict`, `not_registered`, `policy_not_initialized`,
`policy_already_initialized`, `schema_not_ready`, `dimension_migration_required`,
`reindex_required`, `profile_change_not_supported` and `revision_exhausted`.
Validation details identify field/index and reason; conflict details identify
current family/revision. Do not echo arbitrary rejected request bodies or keys'
secret values. Candidate check does not reserve a revision or authorize a start.

Input comes from stdin; arbitrary file editing is not a configuration mechanism.
`acknowledge_reindex` is optional and defaults to false; it is never inferred from
a prior check operation. Initial input is `{api_version, policy}`. A registered
check/apply request carries `{api_version, expected_family_id, expected_revision,
policy}` plus the optional acknowledgement. `--check` reports missing required
acknowledgement as an impact requirement without pretending it has been supplied.
Initial add omits expected revision/family because these do not exist yet;
registered candidate checks use both guards. Unknown API versions fail before
mutation. Single-field legacy adapters must call this same service and surface
conflicts rather than silently retrying against another version.

## 6. Preflight and TUI details

Preflight is scoped to the selected checkout; policy is family-wide. An inventory
of one worktree is not an inventory of all worktrees. Report that scope plainly.
Candidate validation need not persist a checkout record to inspect a worktree.

For reported paths, include a human-readable display value and a lossless native
value: `{display, encoding, hex}`, with the existing `unix-bytes` or
`windows-utf16le` encoding. File/directory entries are checkout-relative; the
report's root is absolute. Display strings are never round-tripped as identity.

Use bounded enumeration/stat, with no symlink traversal, standard Git ignore
filters disabled, and the shared exclusion classifier. Report visited regular
files, policy-selected tier 1/tier 2 files and bytes, individually observed
excluded files, pruned directories, large files and unreadable entries. Do not
count every file under a pruned `node_modules` merely to obtain an excluded total;
that total is unknown. Unsupported language is not automatically unsupported
text: today's indexer has a text fallback. Stat-only inventory cannot promise
UTF-8 decoding, parser success, actual chunks/tokens or embedding cost.

Recommendation for the initial interactive budget: stop at 2 seconds or 100,000
visited entries, whichever comes first; retain the largest 20 files and 20 costly
directories. These are proposed inventory limits, not indexing limits or hidden
exclusions. Check the deadline between filesystem operations; a blocked stat can
exceed it, so do not claim a hard wall-clock guarantee. Report `complete: false`,
stop reason and lower-bound counts when limited or partially unreadable.

Keep the earlier proposed advice thresholds: over 10,000 selected files, over
100 MiB selected content, a selected file over 10 MiB, or selected dependency/
build/environment directories warrants refinement advice. Incomplete scans also
recommend review. List concrete reasons and candidate exclusions without
applying them. The current indexer skips files over 10 MiB and limits structural
parsing above 1 MiB; expose applicable capabilities rather than promising every
selected file is fully indexable. Future snapshot failure semantics remain a
separate implementation gate.

TUI shows the initial/current document, default and family rules separately,
family-wide effects and selected-checkout preflight. Controls edit lists and
scalars directly. After saving, offer Start, Edit more, Ask an agent, or Leave
unindexed for a new family. Ask an agent shows copyable inspect/check/apply
commands; it neither launches an agent nor sends a message. On a revision
conflict, retain the user's draft and offer reload/review; do not overwrite a
newer policy. Re-run preflight after changes; never treat the old scan as current.

## 7. Formal refinement and verification plan

Before implementing policy state transitions, extend the governing model to
represent the stored defaults snapshot instead of implicit current-binary
constants. Prove general laws for: unchanged effective policy across binary
updates with the same stored inputs; family/checkouts sharing policy; CAS conflict
preserving the entire state; no-op preserving revision; successful changes
appending a version atomically; and policy updates preserving first-start
and pause authorization. Model generation invalidation for every actual change
and distinguish the analysis work required by each impact category.
Do not weaken the existing dimension or last-match-wins constraints to fit code.

Rust tests should verify invalid/duplicate/unknown fields and malformed globs,
ordered negation and directory pruning, frozen defaults, equality/no-op behavior,
family-ID and revision conflicts, and refusal of unsupported profile changes.
DB tests must verify atomic initialization/update/history, concurrent CAS with
one winner, rollback including generations on failure, immutable history, and
isolation across two family schemas. TUI/preflight tests belong to their later
implementation stage, using the same services.

## 8. Bounded implementation stages for approval

**Next executable stage — policy model and persistence only:**

1. Refine the relevant Agda configuration transitions and prove the general laws
   above using the existing formal-methods workflow.
2. Add typed policy/defaults and strict JSON request/response validation, a strict
   rule compiler, and capability/impact types in core. Preserve current runtime
   config readers; no CLI, daemon or MCP routing changes.
3. Add the semantic repo migration and a family-scoped store for initialize,
   inspect, validate and CAS apply, including history and generation effects.
   Keep the existing historical SQL and current migration blocks unchanged.
4. Verify focused Rust tests, the aggregate Agda specification and workspace
   compilation. Reuse the already-reviewed disposable container/database runner
   for persistence/concurrency tests, then verify teardown and live read-only
   catalog invariance.

The disposable resource names, pinned image, port 5451, tmpfs limits and cleanup
are unchanged from the approved test plan. Do not substitute the live database.
Migration/coordinator testing must be extended to the new repo block while
retaining existing compatibility and cancellation coverage.

**Excluded from that stage:** CLI activation, TUI construction, filesystem
preflight implementation, embedding-profile migration, policy import from actual
TOML, installation, service changes, live migration and publication. Policy APIs
are callable primitives under test, not a completed configuration user flow.
Newly added rows/notifications occur only inside the disposable test database.

Later bounded stages: implement the shared preflight and agent CLI; implement
native TUI; integrate scheduling and snapshot/profile-aware runtime paths; then
perform separately reviewed user-data import and deployment.

## 9. Decisions accepted with implementation approval

1. Store immutable defaults and policy history in each family schema, with an
   atomic current-version pointer; defer user-wide overrides/default adoption.
2. Require expected family ID as well as revision on updates, protecting against
   path reuse; keep complete replacement JSON rather than patch semantics.
3. Avoid reparsing/re-embedding for display/runtime-only changes while retaining
   revision publication guards. Profile changes require
   explicit acknowledgement and remain refused until profile-aware runtime
   support exists; frozen dimension still requires its separate migration.
4. Use the proposed bounded preflight/report semantics in the later preflight
   stage; thresholds remain advisory and never start indexing or edit policy.

The documentation stage did not activate these decisions. The subsequent core
implementation remains disconnected from runtime callers.

## 10. Core implementation evidence — 2026-10-04

Status: **core stage completed and verified**. Later runtime stages remain pending.

Implemented in `crates/core/src/family_policy/`, the additive
`migrations/repo/configuration.sql`, and `spec/Muninn/Policy.agda` with the
corresponding Config/Cli refinements. Existing CLI/config readers, indexer and
MCP routes remain unchanged. The new repo migration creates policy tables and
validation/immutability functions only; it initializes no family or defaults.
The preparation coordinator automatically includes this additional repo block.

Available core operations: strict initial/apply JSON parsing, typed defaults and
policy validation, strict rule compilation, capability/error envelopes, explicit
initialization, read-only inspection and candidate validation, and atomic CAS
apply. Inspection exposes stored/effective rules and defaults separately, with
explicit per-rule origin and position in `effective_rules`. It
does not read bootstrap secrets: credential availability remains explicitly
unchecked until the command layer supplies that local information. Candidate
validation does not yet run filesystem preflight.

The adapter catalog is deliberately the existing three canonical selections:
Voyage `voyage-code-3` (1024), OpenAI `text-embedding-3-small` (1536), and the local
bundled `minishlab/potion-base-32M` (512, JSON model null). Unknown model strings
are refused rather than assumed dimension-compatible. Batch size is bounded by
the adapter's positive u32 representation; this does not certify remote-service
limits. Existing custom model import requires explicit compatibility review.

Every real policy change writes immutable history, advances the current pointer
and increments all non-retired checkout generations in one transaction. Only
commit delivers `muninn_family_policy_changed` with the family UUID. No-op,
conflict or rollback delivers no notification. The existing daemon does not yet
listen to this new channel. `reconciliation_needed` in the core write receipt
means this update invalidated work; it is not a report of daemon completion or
the absence of previously pending work after a no-op.

### Rule-matcher finding and import boundary

Tests exposed a mismatch in the existing `pipeline::build_excludes` path:
`ignore::overrides::Override` implicitly marks unmatched files ignored whenever
there is a whitelist rule. Muninn's negation inversion creates such whitelist
rules, so a negation can unexpectedly exclude or vendor unrelated files.
The new strict compiler uses `ignore::gitignore::GitignoreBuilder`, with explicit
unclosed-class rejection, to implement the approved default-false, last-match
semantics. It retains ancestor pruning and the unconditional `.git` exclusion.
This does not change the installed indexer or the old source call path.

Freezing old pattern arrays alone cannot preserve this erroneous legacy behavior
for affected configurations. Before actual TOML import/cutover, compare old/new
selection and present differences for review; do not silently call a semantic
change an exact import. Repairing legacy runtime callers is outside this stage.

### Verification and limits

- Nine focused Rust tests passed: strict/duplicate/unknown/missing JSON fields,
  rule syntax/index diagnostics, ordering/negation/pruning, frozen defaults,
  scalar/model bounds, impacts, and migration DAG/history checks.
- Interactive Agda checking finished with no goals/constraints, and the final
  aggregate `agda Muninn.agda` check passed. General initialization/update laws
  include expected family identity, version history, frozen defaults, CAS refusal,
  generation invalidation and preservation of start/pause authorization.
- Workspace compilation and diff checks passed. Historical migration files and
  the legacy config, pipeline and store modules remain byte-for-byte unchanged
  from Git HEAD. All changes remain uncommitted.
- The extended disposable integration test passed, retaining earlier metadata
  and coordinator coverage. Policy scenarios verified concurrent idempotent
  initialization, one CAS winner, conflict/no-op refusal, commit notifications,
  family isolation, generation invalidation, immutable history/defaults,
  transaction rollback after generation overflow, dimension refusal and revision
  exhaustion. Paused/suppressed/retired state and first-start authorization were
  preserved.
- The disposable container and allocated fixture/credential directory were
  removed and port 5451 was free. The live check was read-only and still showed
  the original eight registry columns, none of the new/test migration names,
  nine registrations and nine AGE graphs.

This is core persistence, not a completed CLI/TUI or indexing feature. No
preflight, actual TOML import, embedding-profile migration, installation or
service change was performed. No Python files or dependencies were added.

## 11. Read-only CLI and preflight implementation — 2026-10-04

The subsequent approved stage implements these three source-build commands:

```sh
muninn config PATH --json
muninn config PATH --check - --json < candidate.json
muninn preflight PATH --json
```

`candidate.json` is a transport document, not a configuration file or editor
interface. Its complete request shape is defined in section 5. Registered
candidate checks require both expected family UUID and revision; unregistered
checks use the initial request shape. Check returns the current stored policy
and a separate `candidate` object, with the inventory calculated using the
candidate. It saves nothing. Profile/dimension incompatibility is reported by
`candidate.validation.apply_supported: false` rather than hidden by a successful
syntax check. CLI capabilities list only inspect, check and preflight.

The commands dispatch **before** legacy startup's migration calls. The shared
`family_policy::readonly::query` service resolves identity, reads policy and
checks candidate guards in a PostgreSQL read-only, repeatable-read transaction.
It releases that transaction before filesystem inventory. Neither a successful
check nor its reported revision reserves a later write or authorizes indexing.
Resolution and inventory are observations, not an atomic Git/filesystem snapshot.

Git paths resolve to the checkout root and common-directory family identity;
worktrees share the family policy even before a checkout row exists. Such reads
report a null checkout ID without registering it. A plain directory resolves to
its nearest registered directory ancestor. Inspection includes family and
checkout pause/registration state separately. No path marker is written or read
as policy, and no legacy TOML is imported.

A reachable, prepared registry is required even for creation-default preflight:
connection failure cannot prove that a directory is unregistered. An old registry
or missing policy tables returns `schema_not_ready`; an existing registration
without initialized policy returns `policy_not_initialized`. If unimported legacy
identity cannot be established, `legacy_identity_unresolved` requires inventory
review. Defaults are never silently substituted for these cases. An actually
unregistered directory can use preflight/check with creation defaults;
`config PATH --json` returns `not_registered`.

The installed service/database have not been upgraded. The current live registry
therefore intentionally produces `schema_not_ready` with these new commands
until a separately approved preparation/import stage. Existing legacy commands
remain available with their existing write/migration/indexing behavior; the
read-only guarantee applies to the three forms listed above. No new apply/add,
start, native TUI, watcher routing or service deployment is included here.

### Inventory report

`family_policy::preflight::scan` uses the strict family rule compiler, including
its directory-aware classifier. The default scan stops enumeration at two seconds
or 100,000 visited entries. Filesystem calls can block beyond the budget. Git/DB
identity resolution happens before inventory and is outside that inventory
budget. The command makes no embedding/model-network calls.

- Reports selected tier counts/bytes, visited regular files, individually
  observed excluded files, pruned directories, skipped symlinks/special entries,
  unreadable entries and bounded samples. Git ignores do not filter selection;
  `.git` entries are always excluded. Symlinks encountered during enumeration
  are skipped. The explicit root is canonicalized, including a root alias.
- Directory pruning does not enumerate descendants. Their excluded total is
  unknown (`excluded_descendant_count: null`), even on a complete policy scan.
  Limited/unreadable scans set `complete: false`, `counts_are_lower_bounds: true`
  and a stop reason. Entries can change during traversal; this is not a filesystem
  snapshot or a promise against concurrent path replacement.
- Retains the largest 20 selected files and the 20 directories with greatest
  observed selected bytes (then file count). Directory totals include descendants
  and can overlap: do not sum them as a checkout total. Other diagnostic samples
  are also capped at 20, with full observed counts reported separately.
- All reported paths include display, native encoding and hex. The report root
  is absolute; file/directory samples are checkout-relative. Display text is not
  an identity or a shell command.
- Advice uses section 6's thresholds. Selected dependency/build/environment
  directories include proposed family-wide exclusion globs such as
  `**/node_modules/`; these are suggestions for review, never applied rules.
  `advice: "start"` means the inventory found no size/selection concern. It does
  not override pause/registration state, verify credentials or enable indexing.
- Metadata alone cannot validate file contents, estimate actual embedding costs
  or prove parse success. The report exposes the current 10 MiB indexer file
  limit and 1 MiB structural-parse limit. Unknown extensions remain eligible for
  text fallback. Credential reporting exposes availability for the selected
  policy/candidate backend only, never the key or a claim of remote validation.

### Verification

The existing disposable database harness was extended to execute the actual
shared read-command service. It verified nested Git paths, newly discovered
unregistered worktrees, suppressed/paused checkouts, directory ancestors,
creation defaults, candidate selection/preflight and family/revision conflicts.
Before/after snapshots of registry rows, checkout rows, policy history/pointers,
migration records and AGE graph counts were identical. Reads also refused the
historical eight-column registry without migrating it. The earlier persistence
and coordinator scenarios continued to pass. Test resources were removed and
port 5451 was free afterward.

Focused filesystem tests cover pruning and reinclusion, individually observed
exclusions, Git-ignored/unknown-extension content, entry/time limits, sparse large
files, bounded samples, symlink exclusion, native path bytes and ordinary-user
permission failures. CLI tests cover new/legacy parsing and a single sanitized
JSON error document with the specified exit status. Workspace compilation,
formatting and diff checks passed. The final Rust run passed 140 core unit tests,
two CLI parsing tests and one process-level JSON test. The existing test that
requires writes to the live database remained ignored. The disposable integration
test passed separately; its container, listener and credential directory were
confirmed absent after cleanup.

A final read-only live catalog check still showed the original eight registry
columns, zero new family/policy migrations, nine registrations and nine AGE
graphs. This stage added no migrations or formal state transitions; the existing
read-only preflight model continues to apply. All changes remain uncommitted.

## 12. JSON registration and policy writes — 2026-10-04

The approved source implementation, now verified, adds:

```sh
muninn add PATH --json
muninn add PATH --json --input - < initial-request.json
muninn config PATH --apply - --json < apply-request.json
```

These routes dispatch before the legacy startup path. JSON `add` cannot be
combined with legacy key=value arguments or `--no-index`; JSON registration is
always unstarted. Existing legacy command behavior remains available. No command
listed here imports existing TOML, starts indexing, installs binaries, restarts a
service or creates a database. All write verification uses the reviewed disposable
container/database; no live preparation or configuration write is authorized.

### Approved recovery refinement

Implementation review identified that the existing coordinator's
`GraphRequirement::NewReservation` needs explicit creation provenance after an
interruption. Existing registry fields cannot establish that provenance, and an
interruption could otherwise lose an agent-supplied initial policy. The user
explicitly approved persisting creation provenance plus initial policy/defaults
with the reserved UUID before this refinement was implemented.

One **appended** block, `public-family-registration-intent`, extends the existing
semantic `migrations/public/families.sql` file. All older blocks remain unchanged.
It adds immutable `registration_intent` JSON and an irreversible
`registration_completed_at` marker to the registry. The intent contains format
version 1 and the complete initial policy and defaults snapshot. It is only a
creation/recovery record: authoritative current policy and version history still
live in each family's application schema. An old row cannot acquire an intent by
UPDATE, and neither intent nor a completed marker can be reset by ordinary SQL.
The public template remains a single Kryzhen migration DAG. Repo templates and
AGE namespaces remain separate; no AGE objects were added to any SQL template.

### Registration sequence and recovery

1. Validate input and filesystem identity before preparation. Without input, use
   shipped creation defaults only when resolving a genuinely new family.
2. Prepare public metadata through a dedicated coordinator connection. Under the
   registry lock, resolve family/root ownership again and atomically reserve a
   UUID with its initial policy/defaults. Never infer or import legacy identity.
3. Prepare application templates through Kryzhen and the separate graph through
   AGE. `RegistrationIntent` graph mode rechecks stored intent, incomplete
   registration and absence of indexing authorization under the registry lock.
   Completed registrations require their existing valid graph; a missing graph
   is an error, not permission to create a replacement.
4. Retain the preparation lock through checkout registration and completion. This
   prevents another preparer from setting the family to migrating between those
   operations. The existing lock order remains preparation then registry; the
   initial registry reservation is committed before preparation begins.
5. Revalidate filesystem/family identity and readiness. Initialize revision-one
   policy from the **stored intent** and mark completion in one transaction.
   Failure rolls back both initialization and completion; earlier reservations,
   checkout registration and committed Kryzhen blocks can remain for retry.
6. Return a committed receipt with identity, policy, actual authorization state,
   `family_created`, `recovered_registration`, `registration_complete` and
   preflight. If post-commit inventory fails, return `preflight_error` on that
   successful receipt rather than claiming registration rolled back.

An existing completed family without input reuses its policy and associates the
selected checkout idempotently. It preserves suppression/pause and does not reset
an edited policy to its creation intent. Supplying initial input after completion
returns `policy_already_initialized`. While an intent is incomplete, identical
initial input can resume it; differing input returns `registration_intent_conflict`.
Retrying without input always retains that intent's policy and defaults, even if
binary defaults have changed. An imported/bound family without an intent must
already have initialized policy; this command does not invent one.

Failures after reservation include the reserved family UUID and
`reservation_persisted: true`. Diagnose the reported failure and retry `add`
without input; do not delete the family, ledger or graph to restart. A lost
connection during commit can leave the outcome uncertain, so a retry still
rechecks authoritative state. The command does not promise rollback of previously
committed preparation. Missing legacy/import identities, ambiguous root ownership
or unrelated unprepared families can still require diagnosis under the existing
registry invariants; the command does not skip those checks.

The production coordinator connection factory uses the global bootstrap DB
settings and matching transport for query cancellation. It bounds preparation
statements to 60 seconds and lock waits to 15 seconds, with a 10-second connection
timeout when none is configured. The guard owns the connection until completion;
all failure/cancellation paths release it. TLS construction follows the existing
connection policy; no plaintext cancellation is substituted for a TLS connection.

### Apply semantics

The path-based apply service validates the complete request, then holds the
registry transaction lock while resolving the path and checking family UUID,
revision, readiness and registration completion. It uses the existing policy
CAS transaction for history, current pointer, generation invalidation and commit
notification. It never prepares schemas, registers a checkout or imports policy.
Missing registration metadata returns `schema_not_ready` without migration.

The receipt contains the policy actually committed by this operation, not a
subsequent reader's possibly newer policy. No-op remains no-op; stale family or
revision fails without writes. Existing dimension/profile restrictions remain.
`reconciliation_needed` reports invalidation. `reconciliation_scheduled` is true
for a changed policy on an already enabled family: the daemon receives a policy
notification and also checks on its fallback poll. Paused families retain the
request until resumed. New-family indexing authorization stays absent; apply
preserves existing indexing/pause authorization.

### Verification and scope

The formal refinement in `Muninn.Registration` proves general preservation of
creation intent and indexing authorization, irreversible completion, refusal to
create a missing graph with absent/completed intent, and retention of the stored
initial policy through recovery. It supplements the existing schema and policy
laws without weakening them. Interactive checking reported no goals/constraints;
the aggregate specification passed.

The disposable integration scenarios exercise concurrent main/worktree adds,
one shared schema/graph pair, idempotent checkout registration, completed-input
refusal, path-based CAS conflicts/no-op, policy preservation after repeated add,
immutable intent/completion, missing completed-graph refusal, and interrupted
reservation recovery retaining its UUID and initial policy. They assert no chunks,
no `.muninn.toml` creation and no first-index authorization. A targeted completion
failure checks that initial policy/default rows and the completion marker roll
back together. The old-registry fixture checks that apply refuses without
migrating. Existing coordinator and policy persistence scenarios remain in the
same harness. The extended integration test passed, including the completion
failure/rollback scenario, and its container, port-5451 listener and temporary
credential/fixture directory were removed. Focused policy/filesystem tests,
three CLI parsing tests, two process-level JSON tests, three migration-history
tests, workspace compilation, formatting and diff checks passed. The final live
read-only check retained the original eight registry columns, nine registrations,
nine AGE graphs and zero new family/policy/intent migrations.

This stage does not provide native TUI, explicit start, runtime policy cutover,
profile migration, user-data import or deployment. All source changes remain
uncommitted. The live service continues using its installed version and schema.

## 13. Native configuration TUI

The approved TUI stage implements policy viewing/editing and preflight review
through the services above. Explicit start, indexing integration, deployment and
live changes remain separate stages. The accepted post-save Start choice in
section 6 remains pending until its runtime action is implemented; this editor
currently offers edit more, agent instructions or leaving without starting.

### Entry points and controls

- `muninn add PATH` opens an initial or existing family policy. Opening and
  checking do not register anything; an explicit Save registers a new family or
  associates the selected checkout with an existing family.
- `muninn config PATH` opens an existing family's policy. An unregistered family
  receives an instruction to use `add`. An unprepared schema receives the shared
  service's readiness error; opening the editor does not migrate it.
- `--json` retains the noninteractive protocol. Explicit legacy `add` assignments
  or `--no-index`, and scoped legacy config subcommands, retain their previous
  routes during the staged runtime transition. Plain interactive forms dispatch
  before legacy migration/indexing startup. A pipe is refused before global
  configuration or DB access, with an instruction to use JSON.

The editor uses native keyboard controls from the already locked `console`
library. It does not launch an external editor or create a pseudo-file. Views:

| Key | View/action |
| --- | --- |
| `1` / `e` | Policy: name, debounce, embedding batch size and ordered rule lists. |
| `2` / `d` | Frozen defaults and family rules shown separately, with ordering/pruning semantics. |
| `3` | Most recent preflight for this draft; edits invalidate it. |
| `4` / `a` | Copyable JSON inspect/check/save commands for an agent. No agent is launched or contacted. |
| `5` | Current-versus-original-versus-draft review after loading current policy. |
| `m` | Full status/error message, including recovery instructions. |
| Arrows / Tab | Select a field or scroll a view. Page Up/Down moves by several rows. |
| Enter | Edit selected scalar/rule; accept an edit inside its control. |
| `x`, `J`, `K` | Delete a selected family rule, move it down, or move it up. |
| `p` | Validate the draft and refresh selected-checkout preflight. |
| `s` | Validate/preflight, then request a separate Enter confirmation to save. |
| `r` | Load current policy for review while retaining the draft and its original guard. |
| `q` / Escape | Leave; a dirty draft requires discard confirmation. Ctrl-C aborts without saving. |

New families have a native backend selector with canonical model/dimension
combinations. Registered embedding profiles remain fixed while runtime profile
migration is unavailable. Batch size remains editable. Validation failure keeps
both the field buffer and the previous valid draft. Ordered rules use the shared
policy validator; read-only defaults cannot be edited accidentally.

The terminal needs at least 52 columns by 14 rows. Long review/default/preflight
lines wrap and scroll; long field values keep the editing cursor visible.
Control characters are escaped for display. Agent command arguments use
Bash/Zsh quoting, including lossless native byte quoting for unusual Unix paths.
Alternate-screen/cursor state is restored on normal exit, Ctrl-C and returned
errors. Resize is picked up on the next keypress. Drafts are in memory and are
not recovered after exiting the process.

### Save and conflict behavior

Checks and saves reuse the same JSON request types, family UUID/revision guards,
policy history and registration services. No new storage transition or migration
is introduced by the TUI. Every save has a preflight check and a confirmation
that policy is family-wide. Saving never enables or unpauses indexing. Already
enabled families reconcile changed selection rules through the daemon. After
saving an unstarted family, the TUI asks whether to start now, edit further, ask
an agent, or leave; the metadata inventory supplies its recommendation.

A stale check/save retains the draft and original revision. `r` loads a review
snapshot without rebasing the draft. In Review, `l` asks for confirmation before
discarding the draft and loading current policy. Lowercase `k` explicitly keeps
the draft against that reviewed revision of the **same** family; another check
and save are required. A different family UUID cannot receive that retained draft.
Concurrent edits after review still fail the normal CAS guard.

For `add` on an existing family, policy saving and checkout association are two
operations. The association revalidates the family identity. If it fails after
policy commit, the editor reports that the policy was saved and the checkout
association failed; it does not claim rollback. Saving again retries association.
New-family registration uses the durable creation intent described in section
12. An interrupted registration reports retained reservation/recovery information
and directs the user to the existing idempotent JSON retry without new input.

Preflight displays selected tiers/files/bytes, scan completeness, pruning and
unreadable counts, costly directories, large files, credential availability,
reasons and proposed exclusions. Advice never applies exclusions automatically.
It describes only the selected checkout; metadata inventory cannot guarantee
parser or embedding success. The global bootstrap file supplies connection and
credential settings; the TUI does not rewrite it.

### Verification

Focused tests cover ordered rule editing and validation, stale-draft retention,
explicit review/rebase guards, profile restrictions and terminal-safe long text.
A real pseudo-terminal runs save, discard and Ctrl-C interactions against an
in-memory backend, checks that no index authorization changes, and compares
terminal attributes before/after. Process tests reject nonterminal entry before
config/DB access; parser tests distinguish native, JSON and legacy forms.

The approved disposable runner additionally exercises the actual TUI database
adapter: read-only open/check, initial policy registration, a conflicting JSON
edit, explicit review followed by successful CAS, no-op save, and worktree
association in the same family. It asserts no chunks, no first-index authorization
and no `.muninn.toml` creation. Both the existing core integration suite and this
TUI persistence test passed; container, listener and temporary credentials were
removed. The CLI suite passed eight unit/terminal/parser tests and three process
tests (the two explicitly ignored fixture tests ran separately through the PTY
parent and disposable runner). The live read-only check retained eight registry
columns, nine registrations, nine AGE graphs and zero new family migrations.
Workspace compilation, formatting and diff checks passed. Both historical SQL
files retain their original hashes; this stage added no migration blocks and
changed no formal state transitions. No live migration, service change,
installation or publication occurred.

### Explicit start and runtime integration

`muninn start PATH` enables the saved family and indexes in the foreground.
`--json` returns a receipt; agents can supply `--input -` with
`{"api_version":1,"expected_family_id":"<uuid>","expected_revision":1}` to
refuse a stale family/revision. The TUI uses this same guarded operation after
its separate Start confirmation. Neither form silently unpauses a family.

Authorization commits before indexing, so interruption can be retried by the
daemon. `indexing_enabled` and `indexing_completed` are separate receipt fields;
a skipped checkout/file makes completion false. A failed pass reports
`indexing_incomplete` with persisted authorization in its error details.

Runtime and preflight share the policy classifier and directory pruning rules.
Preflight is metadata-only: binaries, invalid UTF-8, and oversized content can
still be skipped during indexing. Legacy registrations continue reading their
existing file configuration until explicit import. Stored-policy families use
global connection/credential settings and their saved embedding selection.
Policy publication is serialized against an indexing transaction's current
policy row, preventing older rules from publishing after a save commits.
