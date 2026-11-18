# Incremental reconciliation and compatible analysis

This specification defines logical requirements for reducing unnecessary file
reads and reusing structural analysis. It does not prescribe a cache table,
filesystem API, watcher implementation, or migration. It extends the existing
exact-input reuse rules in `Muninn.ReusePolicy` and the publication and
selection boundaries in `Muninn.ContentPublication` and `Muninn.CheckoutState`.

## Observations and change detection

The user approved an event-driven fast path with periodic full audits.
For an initialized checkout, normal reported file changes may be published
without rereading every unchanged file. The fast path reads and validates the
reported selected paths, preserves unreported paths from the last published
view, and retains changes reported during processing for another pass. An
unreported change can remain stale until the next successful full audit.
`Muninn.IncrementalEventual` specifies these two publication modes and their
checkout isolation. A full audit is due after 300 seconds since the previous
full audit; scheduling, in-progress work, Git suspension and failures can
delay completion. Lost events, unavailable watcher coverage, directory changes
that cannot be expanded reliably, and unknown baseline content trigger a full
audit rather than being treated as complete change information.

`Muninn.IncrementalObservation` distinguishes an absent file, an unreadable
file, and a readable file with exact bytes. Device, inode, size and modification
time are observation metadata, not content identity. A zero/epoch timestamp is
ignored as a timestamp hint; a nonzero timestamp change may request a content
read, but an unchanged timestamp is never proof of unchanged bytes. The model
does not assert that a nonzero timestamp is truthful.

A complete event trace relates actual before/after snapshots to every affected
path. `traceCovers` derives the coverage certificate from that trace; it does not
assume that a watcher is complete merely because it has returned events. The
adapter must establish completeness before claiming the complete-observation
guarantee, expand directory, rename, symlink and
hard-link effects to all affected selected paths, and detect lost or uncertain
events. A full audit uses `uncertain`, which reads all paths in the affected
scope. The approved fast path does not claim complete coverage; initial
observation also cannot assume an existing complete baseline.

For a truthful complete trace, `observationCorrect` gives the actual current
file at every path. A reported change is read; an unreported path with no
metadata hint can avoid a read. `changedBytesMustBeReported` applies even when
size, inode and timestamp match. Rename laws require both affected paths to be
accounted for. These are consequences of the trace/coverage assumptions, not
proof that a particular operating system delivers or retains every event.
For a finite selected path list with complete coverage and no additional
metadata hints, `IncrementalWorktree.readsMatchReported` specifies that the
number of reads is exactly the number of reported selected paths. This is a
conditional work bound, not a claim that the current watcher establishes the
coverage needed to use it.

## Exact identity and structural reuse

`Muninn.IncrementalIdentity` permits a hash to narrow candidates but requires
equality of the entire `ReusePolicy.AnalysisInput` before reuse. That input
includes family, exact bytes and versioned parser, grammar, extractor, chunker,
normalization and analysis settings. An arbitrary hash collision cannot make
different inputs reusable. Device/inode, file size, and timestamps do not alter
this semantic identity.

`Muninn.IncrementalStructure` stores symbols and unresolved call candidates in
the abstract completed-work cache. A compatible cached analysis remains valid
and does not invoke the analysis provider again. Resolution uses symbols of the
selected checkout: matching local symbols take precedence, otherwise matching
nonlocal symbols are candidates. A new target can resolve an existing retained
candidate without reanalysing the unchanged source. The selected-edge boundary
requires the source and target to belong to the selected symbol list and both
analyses to be valid, cached, family-matched and associated with the selected
file inputs and observed exact bytes. Parser correctness and the adapter's
construction of the selected symbol list remain implementation obligations.
`IncrementalWorktree.unaffectedResolution` also states that a retained call's
resolution is unchanged when the checkout's set of matching target symbols
is unchanged, even if unrelated symbols change. Changes to matching targets
must be reconsidered, including a newly added local symbol that takes priority.

## Publication, isolation and retry

`Muninn.IncrementalPublication` describes complete publication when stability
evidence exists for the actual prepared and publication-boundary observations.
For the approved event-driven fast path, that full-view evidence is not
assumed: reported paths are read and validated and unreported paths retain the
prior view until reported or audited. A current policy revision and settled
Git state are required for a replacement; stale policies, ongoing Git
operations and conflicts do not publish it. If validation is invalidated, the
prior published views are retained. Other checkout views remain unchanged.

Unreadable content is hidden and remains pending; it is not a successful file
deletion. Current exclusion rules also hide content even when a previous view
is retained. The adapter must connect these logical visibility and pending
states to the existing policy, transaction, filesystem, and storage operations.

## Operating-system file cache

Worktree scanning uses ordinary filesystem reads and does not request eviction
of cached file pages. The cache may be shared with other processes. This design
reduces unnecessary reads rather than attempting to control kernel cache size.

## Boundaries

The theorems quantify over all modeled snapshots, paths, inputs and event traces.
They are conditional on the supplied filesystem observations, complete event
trace, parser validator and policy revision corresponding to reality. They do
not prove a filesystem offers atomic snapshots, establish a numerical cache or
CPU limit, or prove that the present Rust implementation follows the model.
Those are separate implementation and measurement obligations. The fast path
must not assert that unreported paths are current. Full audits and recovery
address changes that were not reported.
