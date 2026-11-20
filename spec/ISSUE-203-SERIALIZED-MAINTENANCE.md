# Issue #203: serialized selection maintenance

Status: approved design with a local runtime implementation; not released.
Baseline: published v1.3.0, commit 7fd9bd34023f50c766d676b6eb13aa3282463d7b.

## Objective and accepted compromises

A Git-ignore or explicit selection change updates the selected checkout views,
preserves shared content still needed elsewhere, and removes unused derived
index data. Curated notes are untouched. Keep the moving base/file deltas,
shared file versions, primary AGE graph and linked structural snapshots.

Serialize family operations, including searches, during maintenance. A family
can be unavailable for the full scan, embedding calls and cleanup. Interrupted
work may be repeated. A full selection scan after an ignore change is acceptable;
ordinary file events retain incremental reconciliation. No new global allocation
lock, logical identity catalog, reader pin registry, staged publication system,
receipt recovery protocol or concurrent garbage collector is required.

This is an intentional revision of the earlier concurrent-cleanup approach.
The specification does not promise a two-hour implementation deadline.

## Admission and persistence

Use the existing family advisory transaction-lock key as the common gate.
Index-backed searches take its shared form; writers and maintenance take its
exclusive form. A search tries the shared lock and returns `family_busy` if an
exclusive operation prevents admission. The gate lasts through result
materialization, not network response delivery. It is per family, not
installation-wide. Ordinary searches can therefore overlap outside maintenance.

Search execution preserves the existing moving-base view: every delta path masks
the base, including deletion tombstones, and only non-null versions referenced by
the selected checkout supply delta candidates. Resolve those version IDs first
and retrieve their chunks through the existing file-version index; do not eagerly
materialize full delta payloads through a family-wide chunk-table join. Full-text
search needs text vectors, semantic search needs embeddings, and hybrid search
evaluates both against the same statement snapshot. Fetch result content after
ranking. Preserve modality scores, candidate limits, result ordering and the
shared family gate. This is an execution constraint, not a change to the
`FileMap`/`Worktree` visibility laws or a new storage representation. Verify query
plans on retained data as well as replacement/addition/deletion and moving-base
isolation through the existing runtime tests; Agda does not prove SQL latency.

All family index readers and writers must participate: text/semantic/hybrid and
structural searches, ordinary reconciliation, direct file indexing, embedding
backfill, checkout registration/retirement, policy changes and removal. Acquire
the family lock before policy row locks. Operations that also require the
existing registry lock acquire registry then family; do not acquire registry
while holding family. Long maintenance holds no registry lock. Helpers use the
caller's transaction, never another connection to reacquire its lock.

A maintenance request waits for an active operation to finish, acquires the gate,
and durably records pending work before acknowledging acceptance. Operations
already completed before acceptance may have returned old results. Subsequent
index requests acquire the gate, see pending work, and return `family_maintenance`
instead of reading a partially reconciled family or starting ordinary indexing.

Add one small per-family `selection_maintenance` table by a NEW semantic migration:
`target uuid PRIMARY KEY, requested bigint NOT NULL, completed bigint NOT NULL,
last_error text NULL`, with `0 <= completed <= requested`. Target is an existing
checkout UUID, or the family UUID for an independent directory. These are existing
identities, not a new identity service. A request increments requested; pending
means requested > completed. Exhaustion refuses the request without wraparound.
A policy update and its target requests commit in the same transaction. No policy
format or operation-ID API change is required; retain expected-revision guards.

Status and configuration inspection remain available and report pending targets,
last error and pause/Git blockage. Pause/resume and explicitly requested removal
may acquire the gate while pending; they preserve pending work, except removing
a target also removes its request atomically with its index. Creating/reactivating
a checkout while pending records its required refresh before it can be searched.
Unrelated families and curated-note operations remain usable.

The daemon checks this table on startup and on normal scheduling wakes. It retries
pending work using the existing backoff, not a new background service. Pending
state is durable; lock ownership is not. No persisted reader or worker lease is
needed. A disconnected transaction rolls back and releases its lock.
If a family watcher's connection closes, it exits with that error so the existing
daemon dispatcher restarts it with a fresh connection. It must not repeatedly
retry through the closed client; pending generations survive the restart.

## Triggers and selection

* Creation, change, deletion or rename of any `.gitignore` schedules the affected
  checkout, even when that ignore file is not indexed. Shared Git exclude inputs
  and uncertain event coverage schedule all potentially affected checkouts.
* A family selection-policy change schedules every active/suppressed checkout
  with retained or authorized index work. A directory family has one target.
* Keep the agreed five-minute audit to discover missed filesystem events.
  An audit scans selection without declaring a policy change or requesting an
  unconditional graph rebuild. Unchanged selected versions retain their graph;
  observed manifest changes and existing explicit requests still reconcile under
  the same serialized path. Paused/blocked targets remain pending.

For a target, enumerate the union of previously published paths, current Git
tracked/untracked candidates, and paths reached by explicit Muninn inclusions.
Ask Git for default ignore answers in that checkout; ordered Muninn rules can
include ignored descendants without an extra parent-inclusion requirement.
Vendor classification alone does not unignore a file. Reuse the admitted rule
semantics, size limits and symlink boundaries already specified.

Git query failure, incomplete inventory or unreadable required data is an error,
not an empty selection. Directory families use the same explicit rules with no
Git default. File timestamps do not prove unchanged content. Retain existing
content/profile/tier compatibility checks; hashes only nominate reuse candidates.

## Reconciliation and cleanup

Each target is one database transaction under the family gate. Record its requested
generation, policy revision and Git context. Compute the new selected manifest:
retain unchanged compatible versions; add/reuse newly included content; remove
newly excluded references. Use the existing moving-base preservation logic when
updating the base so sibling views do not silently change.

Update chunks, embeddings and structural data consistently with that manifest.
Rebuild the target's structural view using existing AGE/snapshot operations;
do not migrate all structural data to a new representation. Structural results
must not contain excluded origins or endpoints. A full target structural rebuild
is acceptable for selection maintenance.

Graph setup is idempotent: existing labels are checked in the graph catalog,
not recreated with their errors suppressed. Missing labels are created through
AGE's API. A label or index setup failure propagates to the owning operation;
maintenance rolls back and retains pending work as with any publication failure.

For a full primary-graph replacement, recreate only that checkout-owned graph
through the graph lifecycle API, including its labels and property indexes,
inside the publication transaction. Rebuild its contents from the selected
manifest. Never commit the empty intermediate graph. Rollback must restore the
previous graph and manifest together. Chunk UUIDs remain the application
identities; graph-internal IDs are not durable identities. This does not change
the linked snapshot representation or ordinary incremental graph updates.

Structural edge batches resolve endpoints by equality of their chunk UUIDs
within the known symbol labels. Use scalar identity joins, not property-map
containment joins that rescan the vertex tables for each supplied edge. Preserve
the existing distinct endpoint/relation semantics and per-statement timeout.


Then remove derived data with no remaining uses. Resolve references across ALL
retained checkout views, including inheritance and explicit deletion overrides.
A base row shadowed in every retained view is not by itself a reason to retain
content forever: remove redundant base bindings before final version collection.
Retiring a target cancels its pending refresh; materialize its retained references
before detaching it from the moving base. Retired views intentionally retained
by existing retirement semantics count as
users; they are not searchable, and reactivation requires current reconciliation.
Do not add expiry or retirement-policy changes to this task.

Reuse file-version cascades for chunks and analysis caches. Reclaim obsolete
structural snapshots/legacy graph contents through their existing ownership
mechanisms; AGE owns its schemas. Do not delete shared versions or notes.
Collect unused file versions in bounded batches within that same transaction,
so one large backlog does not become a single unbounded cascading deletion.
There is no intermediate commit or partial-cleanup acknowledgement.
Because active readers have drained, no reader pin/GC coordination is needed.
No saved cursor may retain a live database reference across calls; an existing
continuation must rerun or report restart-required after a view change.

Before commit, recheck file/Git validity using the existing reconciliation rules.
Queued watcher changes cause another pass; Git edits are not stopped by Muninn's
lock. A change reported during scanning must not be acknowledged as processed by
that scan. Watcher events are recorded as later requests; missed events are
repaired by the five-minute audit. This is eventual freshness, not a filesystem
snapshot guarantee.

Commit the manifest, structural changes, cleanup, and completed=requested for the
captured target generation together. An error rolls back this whole target update,
leaves its durable request pending, and records a bounded error separately. A
crash after commit needs no replay of that target unless new work was requested.

Multiple targets commit one at a time. Searches remain refused while ANY target
is pending. This avoids a cross-checkout transaction and avoids exposing a family
partway through an explicit policy change. A blocked or paused target can therefore
make the family unavailable until it can reconcile. Preserve its old data during
that delay; do not silently bypass pause or index merge conflicts. Report this
inconvenience explicitly. Unpausing/retry is the recovery path.

Completion means all requested targets are current, their structural views match,
and all derived data no longer needed by retained views is removed. A saved policy
or completed scan alone is not completion. Commit/pending status determines the
answer after reconnect; ambiguous client replies require inspect/retry under the
existing revision guard, not a new exactly-once request system.

## Formal coverage and authority

`Muninn.SerializedMaintenance` proves general laws for blocked admission, drained
acquisition, pending recovery, selection/exclusion, unchanged sibling views,
reference-based reclamation, notes preservation, transaction outcomes and refusal
to reopen with stale/pending work. `policySelection` connects selection to the
existing `AdmittedSelection.classify`; it does not replace the rule language.
Existing `FileMap` moving-base laws and `GraphMembership` endpoint laws still apply.

For this operation, the serialized protocol replaces the previous runtime
obligations to implement concurrent cleanup worksets, durable reader holds,
cleanup receipt checkpoints and the associated generalized allocation framework.
Older cleanup modules remain mathematical contracts for that alternative; their
presence in the aggregate does not require implementing that alternative as well.
Other operations' contracts are not changed. Catalog/correspondence entries for
this operation must be updated with implementation, not claim dormant cleanup
helpers establish the new behavior.

The model abstracts a family as resolved manifests and derived payloads; natural
numbers name existing identities. It does not prescribe physical row IDs. Finite
manifest enumeration must supply the actual reference decision used by `prune`.
The transaction theorem describes allowed outcomes; it is not a proof of Rust,
PostgreSQL, AGE, Git correctness, lock coverage or event delivery. Liveness assumes
finite successful scans, eventual lock acquisition and eventual availability of
pending targets; no unconditional completion is claimed for a paused checkout.

## Implementation map and verification

| Obligation | Existing code to adapt | Required evidence |
| --- | --- | --- |
| Common family gate and pending admission | `worktrees::lock`; `search.rs`; `worktrees/search.rs`; `worktrees::query_related`; CLI/MCP callers | Two independent clients; reader/index request refused during maintenance; unrelated family usable |
| Durable requests and policy acceptance | `family_policy/store.rs::apply_locked`; new additive repo migration | Policy and request atomic; restart detects pending work |
| Git selection and wakeups | `indexer/watcher.rs::watch_repo`; `worktrees::reconcile_family_targets`, scan/changed-path helpers; `family_policy::runtime::Selection` | Ignore rename/deletion and explicit ignored-child inclusion; missed-event audit |
| Shared views and publication | `worktrees::manifest`, `reconcile_checkout`, `publish_base`, `rebuild_graph` | Two sharing worktrees; first exclusion preserves sibling; re-inclusion works |
| Directory path and other writers | `pipeline::index_repo`, `index_file`, `backfill_once`; checkout/removal paths | No bypass of gate; directory policy refresh works |
| Reclamation | `worktrees::garbage_collect`; file-version foreign keys; graph/snapshot replacement | Last reference removal deletes unused chunks/cache/structural data; notes preserved |
| Failure/status | transaction boundaries, watcher retry, existing status/config responses | Inject failure before commit; old view intact; pending survives; retry succeeds |
| Formal/correspondence | `SerializedMaintenance`; `FileMap`; `GraphMembership`; catalog manifests | Agda aggregate and relevant manifest checks; no false runtime-proof claim |

Implement as one bounded change after specification approval. First wire the gate
and durable requests, then selection/reconciliation and cleanup, then run the
focused two-worktree/disposable-database scenario plus existing required checks.
No new generic framework, broad unrelated refactor, deployment or push is included.
If the implementation needs a behavior absent here, amend this specification first.
