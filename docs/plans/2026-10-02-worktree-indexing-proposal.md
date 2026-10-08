> **Historical design/stage record.** This document preserves proposals and
> progress reports from its date, including superseded decisions. It is not
> a current installation procedure or completion report. For implemented 1.0 behavior,
> see [Development](../../docs/development.md); for installation, see
> [Getting started](../../docs/get-started.md) and [AGENTS.md](../../AGENTS.md).

# Git worktrees as views of one indexed repository

> Core storage/search revision: the approved moving-base and file-delta design
> in [runtime integration](2026-10-04-runtime-integration-plan.md) supersedes
> retained-baseline and shared-family-graph recommendations below. Configuration
> work remains deferred; historical sections are retained for their evidence.

Status: revised design and formal specification, 2026-10-03. This document
records the agreed family-schema, shared-snapshot, configuration, and Git-operation
semantics. The earlier implementation was rolled back. These are requirements
for the next implementation stages, not claims about the installed version.
Concrete SQL layout and migration/cutover details are proposed in the
[storage and interface design](2026-10-03-worktree-storage-design.md) and still
require review before implementation.

## Problem and objective

Muninn currently registers a directory path as a repository. A registration owns
one chunk table, one structural graph, and one watcher. MCP search resolves a
path to that exact registration. A Git worktree is a different directory, often
on a different commit, so its contents are neither visible through the original
registration nor safely represented by the original directory's index. Adding
each worktree as an independent repository duplicates most parsing and
embeddings, and requires manual registration of short-lived directories.

The objective is for any linked worktree of a registered Git repository to be
searchable as its own *current file view*, without manual `muninn add` and
without indexing unchanged file content again. Search results must use paths
and line ranges in the selected worktree. Edits, additions, renames, and
deletions in one worktree must not change results in another.

This proposal preserves path-based behavior for registered non-Git directories.
Existing MCP search tool names should remain usable. Responses must expose
snapshot freshness and suspension; the exact compatible response extension is
to be specified before implementation.

## Current constraints in the code

- `repos.path` is unique, and its UUID determines both the per-repo PostgreSQL
  schema and the Apache AGE graph. `get_repo_by_path` requires an exact path.
- Chunk rows contain absolute `file_path` values. Search reads from one repo's
  chunk table and returns those paths directly.
- `content_hash` hashes *chunk text* for embedding backfill. It does not
  identify a complete file version or prove that two worktree files match.
- Graph nodes also contain absolute paths, and cross-file edges are resolved
  against the set of symbols in one indexed checkout. Reusing a chunk alone
  cannot make a worktree's structural graph correct.
- The daemon watches only registered paths. Its incremental watcher does not
  currently rebuild cross-file edges; full reindex does.
- Curated knowledge is keyed by `repo_path`, so it needs an explicit policy
  when multiple checkout paths refer to one Git repository.

These facts make a single extra column on the current chunk rows insufficient:
Muninn needs to distinguish reusable file analysis from the checkout-specific
mapping of paths and relationships.

## Agreed identity and storage model

**One application schema and one AGE graph schema per repository family.** A Git
repository and all of its linked worktrees share that pair. An independently
registered non-Git directory forms its own family and has its own pair. This
approved arrangement supersedes the earlier literal one-schema requirement;
AGE is retained. The main checkout has no special ownership of shared analysis.

| Identity | Meaning and ownership |
| --- | --- |
| Family | One Git common directory, or one independent non-Git registration; owns an application schema and an AGE graph schema, shared analysis, and indexing policy. |
| Checkout | One canonical working directory within a family; owns its root path, watcher/indexing state, and published-view reference. |
| Baseline snapshot | Immutable path-to-file-version mapping shared within the family; identified by a stable ID. |
| File version | Immutable analysis of exact complete-file bytes with compatible analysis configuration. |
| Published view | A baseline reference plus checkout-specific differences and structural relationships resolved for that view. |

A Git family is discovered using the canonical common directory reported by
`git rev-parse --path-format=absolute --git-common-dir`. A checkout has its own
identity independent of its branch name or current commit. Family identity must
remain stable when its original checkout changes branch or disappears. Exact
registry tables and handling of relocated Git common directories belong to the
storage/resolver design review.

### Shared analysis and checkout membership

File versions contain chunks, line ranges, parsed symbols, and file-local facts.
Identity includes exact full-file bytes, detected language, parser and chunker
versions, and relevant analysis configuration. A complete-file digest is a lookup
aid; the current chunk-text hash is insufficient. Embeddings have their own
backend, model, dimension, and configuration identity. Reusing parsing does not
authorize reusing an incompatible vector.

Unchanged chunk data, vectors and compatible analysis are stored once and may
be referenced by multiple checkouts. Separate relational membership rows are
permitted; recording a reference is not copying the chunk or embedding.
Changed, added, deleted and renamed files update only the selected checkout's
membership, with reuse of existing compatible data where possible.

The prior requirement to avoid every repeated path/membership entry is withdrawn,
as are the custom prefix/radix maps and their storage implementation. The latest
discussion favors ordinary relational chunk associations; a replacement schema
has not been approved or implemented. Baseline/difference language in the
remaining abstract model does not prescribe physical tree storage.

Cross-file relationships belong to a particular published view. A changed
callee can require updating relationships from an unchanged caller; the caller's
file analysis still remains shared. The graph representation must support those
contextual differences without copying unchanged file-local analysis. Endpoint
visibility and actual name resolution are separate correctness requirements.

### Stable baselines when main advances

A baseline reference identifies an immutable snapshot, never "the current main
index" or a moving branch name. For example:

| Event | Main checkout | Worktree A |
| --- | --- | --- |
| Both start at the same content | S1 | S1 plus A's differences |
| Main pulls new changes | S2 | Still S1 plus A's differences |
| A later updates its own files | S2 | A newly reconciled view of A's actual files |

Versions and baseline entries referenced by S1 remain available while A needs
them. Hidden baseline entries also remain reachable: removing an override may
expose them again. Updating main cannot mutate A's visible chunks or graph.

### Git interfaces

Use Git's existing immutable tree/blob identities and programmatic interfaces
for discovery and change detection:

- `git worktree list --porcelain -z`: enumerate checkouts.
- `git rev-parse HEAD^{tree}` and `git ls-tree -r -z --full-tree <tree>`:
  identify and inspect a committed baseline.
- `git diff-tree -r -z <old-tree> <new-tree>`: identify committed changes.
- `git --no-optional-locks status --porcelain=v2 -z --untracked-files=all`:
  inspect staged, unstaged, untracked, and conflicted paths.
- `git cat-file --batch`: retrieve objects efficiently when needed.

Git's object graph supplies baseline identity and structural sharing. Muninn
still needs a database representation of searchable membership and its derived
analysis. A Git tree ID alone is insufficient for the working-file view: filters,
line endings, encoding conversions, policy, sparse checkout, and untracked files
can affect what Muninn actually reads. Analyze actual working bytes and preserve
compatible reuse; Git status is a change-detection input, not a universal proof
of byte equality. A repository without a first commit or a non-Git directory
needs a Muninn-owned immutable baseline under the same view semantics.

Git reference: [worktrees](https://git-scm.com/docs/git-worktree),
[objects](https://git-scm.com/book/en/v2/Git-Internals-Git-Objects),
[ls-tree](https://git-scm.com/docs/git-ls-tree),
[diff-tree](https://git-scm.com/docs/git-diff-tree),
[status](https://git-scm.com/docs/git-status),
[cat-file](https://git-scm.com/docs/git-cat-file), and
[attributes](https://git-scm.com/docs/gitattributes).

## Schema ownership and migrations

- `public/*` applies only to the public schema. Public registry metadata may
  locate families and their schema pairs; shared indexed file data belongs
  inside the selected family's application schema and graph data in its AGE
  schema.
- `repo/*` is a template applied separately to every family's application
  schema. It manages file versions, baselines, overrides, and application-side
  graph membership metadata. All SQL files within this directory form one
  dependency graph for one target application schema; AGE graph lifecycle is
  outside that migration set.
  A linked worktree adds state within its family's existing pair; it creates
  neither another schema nor another AGE graph.
- **The Kryzhen Rust library owns application-schema creation and migrations.**
  Muninn calls its existing library dependency directly. Registration,
  indexing, daemon setup, and test fixtures must use it. Remove the current
  manual application-schema creation path during the implementation stage.
- **AGE owns graph lifecycle and its internal schemas through its API.** Muninn
  creates or validates the family's graph independently of Kryzhen. Do not
  precreate its schema, modify AGE catalogs manually, or add graph lifecycle
  migrations to `repo/` or another Kryzhen migration directory. AGE readiness
  is separate from Kryzhen's application history.
- Existing migration blocks, names, bodies, and checksums are immutable.
  Append new migration blocks to the appropriate existing semantic group or
  add a semantically named file, grouping related blocks together. Do not
  rename existing numbered files or introduce new numbered filenames.
- Migration dependencies establish order; filename order does not. Kryzhen
  records canonical migration bodies/checksums and application per target
  schema. Applying a template to family A never establishes readiness for B.
- A family becomes usable only after Kryzhen completes the required application
  template and Muninn separately verifies AGE graph readiness, including the
  expected graph name and namespace. Muninn coordinates these two lifecycles.
  Template DDL resolves against its application schema; references to public
  metadata and extension objects must be qualified as required. Failure must
  leave a retryable, non-ready registration.

Existing `repo_<uuid>` and `code_graph_<uuid>` schemas are retained. New families
receive their own pair. No new database or container is required by this design.
Any future testing or cutover that creates resources or changes existing data
requires a concrete resource and recovery plan before execution.

## Configuration source

Store repository-family indexing policy in the database, keyed by family ID.
This includes display name, exclude and vendor patterns, watcher settings, and
the selected embedding backend and model. Every checkout in the family uses the
same policy. Keep built-in
defaults in the program and, if user-wide policy overrides are needed, store
those in the database too. Record the analysis identity with file versions and
the model identity with embeddings so a policy change cannot silently reuse
incompatible results.

Keep a small user-level bootstrap file for the single database connection and
machine-local secrets and paths, such as embedding API keys and the local model
cache. Do not put API keys into the database or a worktree. Muninn must read
the bootstrap file before connecting to the database; all other family policy
is loaded from the database after connection. A family-selected embedding
backend uses the corresponding local credential. A backend/model change that
invalidates stored vectors needs an explicit reindex or migration, as it does
today. Configuration updates should be validated and committed atomically,
then notify the daemon which families need reindexing.

The unused per-repo database override is removed from the proposed model. One
bootstrap connection addresses one Muninn registry. This is a deliberate
compatibility change, not a claim that today's parser lacks the override.

## Registration and configuration workflow

Concrete policy storage and JSON details are proposed separately in the
[family policy contract](2026-10-04-family-policy-json-contract.md). That document
distinguishes these accepted requirements from details still requiring review.

`muninn add <path>` and `muninn config <path>` are distinct commands backed by
the same family-policy model. `add` registers a new Git family (or one non-Git
directory) and presents its initial policy; `config` presents or changes the
current policy. Both have a native TUI for a human and structured JSON
inspection/update operations for an agent. Neither edits a pseudo-file. JSON
updates carry the expected policy revision, are validated, and commit
atomically; stale revisions fail rather than overwriting another client's
changes. A path in any linked worktree addresses the same family policy.

Registration performs a cheap, read-only preflight before any indexing. It
counts candidate files and bytes under the effective exclude/vendor policy,
shows costly directories, and flags likely trouble such as `node_modules` or
build outputs. It does not parse, chunk, embed, or construct a graph. The TUI
shows the preflight and policy, recommends either starting now or refining the
policy, and asks the user to choose: start indexing, edit the policy manually,
or seek AI help. The recommendation is advisory. An agent receives the same
report as JSON, can inspect and apply policy through JSON, and must issue an
explicit start action. Saving policy or merely running `add` does not start the
first family index.

Once the first family index has been explicitly started, linked worktrees are
handled automatically. Discovery, first indexing, watching, and branch/file
changes need no separate registration or start action. A new worktree is another
checkout view of the family, even if it lives outside the primary tree. The
preflight may report its cost; ordinary indexing proceeds within bounded
resource use. If work exceeds a limit, Muninn reports that checkout's state and
resumes/retries within its limits, without silently substituting another
checkout's results or requiring a fresh setup decision.

## Discovery and indexing lifecycle

- When a search supplies `repo` or `cwd`, resolve the nearest Git worktree root
  first, find its common Git directory, then find the registered family. If
  neither applies, walk upward to the nearest registered non-Git path in the
  database. An explicit
  worktree path selects that worktree, not the primary checkout.
- The daemon discovers linked worktrees from registered families using `git
  worktree list --porcelain`, initially and on a bounded periodic scan. It
  watches each discovered checkout root. Worktree creation does not require
  calling `muninn add`.
- On first discovery, walk the worktree under the family's indexing rules and
  select or construct an immutable baseline and its sparse overlay, once Git
  is settled. Hash exact working-tree bytes, including ordinary uncommitted edits;
  a Git blob ID alone does not establish equality of the bytes Muninn parses
  when filters or local edits are involved. Reuse an existing file version when
  its full identity matches. Analyze and embed only missing versions.
- Watcher events schedule reconciliation of only that checkout's view and graph.
  The Git-operation gate below applies to discovery, full indexing, incremental
  indexing, and work queued before a suspension. A periodic
  reconciliation covers missed events and worktree creation/removal. Publish a
  new baseline reference, overlay, and graph atomically after their required
  versions are ready, so a query
  never combines half of an old file set with half of a new one. While a
  checkout is catching up, expose its stale/indexing state rather than silently
  returning another checkout's files.
- Removing a worktree removes its checkout mapping after discovery confirms
  removal. Shared file versions and baselines remain while any retained view, candidate
  build, or active query needs them. Removing a checkout must not drop the
  application schema or AGE graph. Garbage collection follows reference reachability and reader/job
  lifetime; it is a separately reviewed operation.

## Git operations and retained search snapshots

During a merge or rebase in progress, or while unresolved Git conflicts exist,
Muninn suspends indexing for the affected checkout and retains its last
published snapshot. It must not parse or embed transient/conflicted file
contents or publish an intermediate manifest or structural graph. Publication
must recheck the checkout's operation state so that an indexing job started
earlier cannot replace the retained snapshot after suspension is detected.

Search remains available against that retained snapshot. Both status and search
responses must explicitly report that the snapshot is stale and indexing is
suspended because of a Git operation or unresolved conflicts. Returned chunks,
line ranges, and relationships describe the last indexed state and may differ
from the files currently on disk. If there is no previously published snapshot,
report indexing pending and return no code results; never substitute another
checkout's snapshot.

After the operation completes or is aborted and conflicts are cleared, Muninn
automatically reconciles the actual working files, reuses compatible stored
analysis, and atomically publishes the updated view. The retained snapshot
remains marked stale until that publication succeeds. Suspension affects only
that checkout; other worktrees continue indexing and serving their own views.
Ordinary uncommitted edits outside an operation in progress remain eligible
for indexing.

- A normal `git fetch` changes remote refs and available objects without
  changing checked-out files, so it does not itself require code indexing.
- `git pull` follows the resulting fast-forward, merge, or rebase behavior in
  the affected checkout. Rapid file changes are coalesced before reconciliation.
- A pull in the main checkout must not advance another worktree's baseline or
  change its visible chunks. Each checkout retains its own immutable snapshot
  reference until its own files are reconciled.
- Completion and abort both trigger reconciliation of the resulting files;
  neither requires a separate user command to restart indexing.

Git hooks are optional notification accelerators. Filesystem watching and
periodic reconciliation must detect relevant changes, suspension, and resumption
without hooks installed. A hook notification requests a state check; it does
not by itself establish that the checkout is ready to index.

The user-facing worktree and troubleshooting documentation shipped with this
feature must explain this suspension policy, the stale-result indication, and
automatic resumption explicitly.

## Query semantics

Every text, semantic, hybrid, structural, and knowledge query resolves to one
family and one checkout. Text and vector retrieval consider only chunks whose
file versions are present in that checkout's manifest. Filter visibility
*before* applying result limits and ranking; filtering a global top-N afterward
can miss the checkout's actual best results. Hybrid fusion deduplicates visible
results by checkout path and version/chunk identity. Returned `file_path` is
the absolute path inside the selected checkout.

Structural queries use the selected checkout's graph. A changed or deleted
definition in one worktree must not leave a caller edge pointing to another
worktree's definition. Existing name ambiguity remains visible as it is today;
worktree support must not introduce cross-checkout edges.

Curated knowledge is family-scoped and visible from every worktree because it
describes the codebase rather than one directory. Existing `repo_path` records
can be mapped to a family during migration. Notes that apply only to a branch
or checkout need an explicit scope; they must not be silently presented as
universal facts. The first release can expose family notes with their origin and
defer checkout-specific writes; any later checkout-specific scope must be explicit.

## Migration and compatibility

Add application objects through Kryzhen repository templates and manage graph
objects separately through AGE APIs/Cypher. Preserve existing registrations and
index data during backfill; allocate a schema pair only for a genuinely new
independent family.
Backfill family/checkout identity for each existing registration. If multiple
registered paths already belong to one Git family, report that collision and
review consolidation before moving or deleting their schemas. Existing chunk
hashes are insufficient to reconstruct file-version identities, so read current files and verify their
content during backfill. Preserve the old index for queries until the new
manifest and search path are ready, then switch each ready checkout to its new
view atomically. Do not drop old chunk tables or graphs in the same migration; remove them only after
verification and a separately reviewed cleanup step.

Keep `muninn add`, `remove`, `reindex`, `pause`, `resume`, and MCP `repo`/`cwd`
interfaces working for existing registrations. Extend status output to show
family and checkout state. Removing one worktree must not delete the family;
family removal must be an explicit separate intent that states all affected
checkout views and shared index data. The exact command syntax and lifecycle
guards must be reviewed before implementation. Removing the original checkout
must not implicitly remove the family.

The user-specific migration utility will be a local script outside Git, as
requested. Its exact reads, writes, target schemas, backup/recovery steps, and
verification must be presented before running it. This specification stage
creates no migration utility and performs no database operations.

## Formal model and proof boundary

The aggregate `spec/Muninn.agda` imports the proposed model:

- `Worktree`: distinct family/checkout/snapshot identities, immutable versions,
  baseline-plus-overlay lookup, no redundant unchanged overrides, deletion
  masking, pinned-baseline stability, exact-byte reuse, and scoped results.
- `Schema`: distinct application/AGE schema pairs, per-application-schema
  template application, independent AGE graph creation/validation evidence,
  and readiness requiring both the application template and graph evidence.
- `GraphMembership`: explicit relationship selection, family-qualified graph
  identities, endpoint visibility, set-update laws, and retention of selected
  relationships when the immutable artifact store is extended.
- `Storage`: one schema pair assignment per family, isolation across both roles,
  independent checkout publication,
  graph membership and endpoint visibility, reference-valid publication, immutable artifact
  extension, and safe removal over both effective views and retained baselines.
- `IndexFsm` and `Index`: explicit first family start, automatic linked-worktree
  dispatch, ready-schema/Git-state gates, and retention of a whole published
  snapshot while Git is blocked. Suspended search explicitly reports stale or
  pending. The old daemon decision is named `legacyDaemonDecision` for comparison.
- `Config`, `Cli`, `Knowledge`, and `Search`: shared family policy and notes,
  TUI/JSON/preflight intents, explicit removal scopes, and checkout-visible code.

The Agda model covers pair ownership and readiness. The physical AGE/snapshot
representation was rejected and its implementation was rolled back. Logical
membership and file-map laws do not prescribe a tree representation or establish
an implementation. The remaining baseline/overlay abstractions require review
against the next accepted physical design.

The model is an abstract behavioral contract. It does not prove the SQL planner,
Git-state detector, canonical-path resolver, graph name-resolution algorithm,
physical allocation/sharing, or Rust implementation correct. Functional maps
specify lookup semantics, not a mandated SQL layout. Application migration
evidence represents Kryzhen's committed history; AGE evidence represents a
separately verified graph mapping. The model cannot certify actual API calls.
The detector supplies current Git state; a debounce interval or absent lock file
alone cannot prove that Git has finished changing the filesystem. Atomic DB
publication ensures a coherent indexed snapshot, not an atomic filesystem scan.

The implementation must revalidate captured input versions and the Git-operation
state, discard or retry superseded candidates, protect active query/build roots,
and eventually reconcile missed events. Those obligations require integration
and concurrency tests. Old indexed state must never be reported as current.

## Acceptance criteria

1. A newly created linked worktree is searchable without `muninn add`;
   results point inside that worktree.
2. Two worktrees at different commits return their own versions of a file.
   Editing, adding, renaming, or deleting a file changes only the affected
   worktree's results, including structural relationships.
3. Unchanged chunks, parsed facts and vectors are shared without copies of that
   data. Separate checkout membership references are permitted. Compatible
   content already available elsewhere in the family is reused.
   Instrumentation shows zero new embedding calls for those files when a worktree is first indexed.
4. Missing or stale manifests never cause results from the primary checkout
   to be returned as if they belonged to a worktree.
5. Search limits are applied after checkout visibility. Full-text, semantic,
   hybrid, and structural search agree on which files exist in the checkout.
6. Existing non-Git registrations and primary-checkout searches keep working
   through migration. The existing index remains recoverable until cutover is
   verified.
7. Worktree removal does not drop either family schema or delete versions or
   baselines still reachable elsewhere, including hidden baseline entries and
   active query/build roots. Family removal cannot race a watcher or indexing job.
8. A family policy set from any linked worktree is visible from all its
   checkouts. Search resolution uses Git and registered families. Migration
   preserves existing effective indexing settings and credentials.
9. `add` returns preflight advice without indexing. The TUI asks whether to
   start or refine the policy; JSON inspection and updates expose the same
   policy and preflight. Only an explicit first start indexes a new family.
10. New linked worktrees begin indexing automatically after the family has
    started. Curated knowledge is visible from all worktrees in that family,
    while code results are scoped to the selected worktree.
11. During a merge/rebase or unresolved conflicts, the affected checkout keeps
    its last published snapshot with explicit stale/suspended status and does
    not index transient files. With no prior snapshot it reports pending.
    Completion or abort automatically resumes reconciliation. Other worktrees
    remain unaffected, and this behavior works without Git hooks and is
    explicitly covered in user-facing documentation.
12. Pulling main leaves every other checkout's baseline, chunks, and graph
    unchanged. Updating or aborting an operation in one checkout affects only
    that checkout; a history rewrite with identical content reuses analysis.
13. Each independent family has exactly one application schema and one AGE
    graph schema. Kryzhen manages the application schema; AGE manages its graph
    and internal schema through its API. Muninn requires both to be ready. Linked
    worktree discovery creates no schema or graph. Repository templates apply
    separately to all family application schemas without rewriting old migrations.

## Implementation sequence for later approval

1. **Specification (this stage):** align the proposal, formal model, and proof
   coverage with the decisions above; type-check the aggregate specification.
2. **Storage and interface review:** specify tables and immutable baseline
   sharing, lookup/ranking plans, graph storage/AGE integration, registry and
   family-policy/knowledge placement, exact JSON and CLI contracts, query
   freshness fields, Git-operation detection, and migration/cutover/recovery.
   Review these concrete choices before Rust or SQL implementation.
3. **Storage and migration implementation:** append reviewed semantic migration
   groups for application schemas through Kryzhen, coordinate separate AGE
   graph lifecycle through its API, and implement
   family/checkout resolution without per-worktree configuration files.
4. **Views and workflows:** implement reusable analysis, discovery, operation
   suspension/resumption, atomic views, all search modes, DB policy, preflight,
   TUI, and JSON configuration according to the reviewed interfaces.
5. **Approved integration environment and cutover:** first present resource names,
   data effects, tests, and recovery. Then verify differential worktree results,
   zero copying/reanalysis for unchanged files, operation races, per-family
   migrations, and recovery. Prepare the user's local migration script outside
   Git. Actual migration, installation, service restart, and legacy-data cleanup
   require their own explicit authorization.

## Implementation parameters still to measure

Set initial-scan, memory, and query-latency budgets against representative
repositories. These measurements determine whether clean-file hashing and
checkout-filtered vector retrieval need specialized optimization. They do not
change the automatic-worktree or explicit-first-start semantics.
