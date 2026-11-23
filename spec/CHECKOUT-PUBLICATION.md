# Checkout publication and sharing for 1.4.0

The checkout's published selector identifies a stable view of its paths, file
versions, and structural relationships. Views share immutable file versions,
chunks, and compatible analysis across the family. A checkout derived from an
existing view reuses its unchanged path bindings. Sparse differences against a
specific retained manifest are one way to share those bindings. Advancing a
branch cannot change the meaning of that manifest or require adjustments to
any sibling checkout's selector, overlay, or graph.

This contract supersedes moving-base publication in
[the issue #30 content publication contract](CONTENT-PUBLICATION.md) and the
ordinary search, indexing, and selection-maintenance admission rules in
[issue #203](ISSUE-203-SERIALIZED-MAINTENANCE.md). Those describe the earlier
storage and availability model. Existing ownership, exact reuse, exclusion,
Git suspension, and removal requirements still apply.

## Ordinary work

- **Observe.** Compare the selected checkout's recorded Git tree and observed
  paths with its current Git state. Include changed commits, staged and
  unstaged changes, deletions, and eligible untracked files. Track selection
  inputs as well. Use checks from the selected checkout for fresh evidence.
  Existing inherited evidence retains its original provenance. Matching
  metadata and a matching HEAD alone cannot certify working file contents.
  Uncertain coverage calls for verifying the affected paths or auditing when
  the affected set is unknown.
- **Prepare.** Use exact bytes and compatible analysis settings to find
  reusable family versions. A verified hit must reuse completed work. Prepare
  missing content and structural work without holding a family-wide gate.
  Persist completed work so changes to one path and a restarted request leave
  other compatible work available. An unreadable selected file remains
  outstanding and its older contents are hidden. Other selected files continue.
  Incomplete merge, rebase, or conflict retains the last completed checkout
  snapshot, subject to current visibility restrictions.
- **Publish.** Atomically advance just the selected checkout's selector and its
  coherent file and structural view. Check the selected checkout's expected
  generation, family storage generation, and current policy revision in the
  publication transaction, along with current Git observation and reference
  validity. A stale observation leads to reconciliation of the affected inputs
  while preserving compatible prepared work. Two valid publications to distinct
  checkouts can commit in either order while the policy and storage generation
  stay current.
  A new view can use an existing family's retained versions before its sibling
  has processed later branch changes.
- **Search.** Read the selected committed view while preparers or publishers
  work. An admitted read captures a coherent snapshot for content and structural
  results. Apply current selection and applicable per-file visibility guards
  before materializing results. The first authorized search with no view
  arranges indexing for that checkout and retains the query until results can
  be produced. Text and structural readiness are independent of vector
  generation. Ordinary index updates, background cleanup, and pending work on
  sibling checkouts cannot produce a family-busy response.

Ordinary publication affects one checkout. Explicit changes to family policy
have family scope and become visible to searches when accepted, including on
paused or Git-suspended checkouts. Search filters exclusions immediately under
the current policy. Background cleanup reclaims derived data safely as readers
and other live references release it. Pending cleanup never acts as a search
admission gate. Reclamation covers retained manifests, checkout references,
preparations, and in-flight readers. Recheck liveness when deleting to prevent
concurrent reference acquisition from racing with reclamation.

## Exceptional coordination

Schema replacement and destructive family removal may require quiescing the
storage they invalidate. Any family-wide lock must name the invariant it
protects, the operations that can violate it, and the point at which users can
proceed. Require that restriction only when the invariant cannot be protected
by a narrower transaction, ownership check, or retained storage generation.
Use recoverable lifecycle state and resume or give operation-specific status
and required action to affected requests. A stalled preparer, embedding
provider, or checkout never acquires this right over a family.

## Initial deployment

An empty index store must support registration, indexing, publication, and
search with the new checkout format. Each checkout publishes independently.
An existing family version is reusable as soon as its compatible file work
is committed. A search of a published checkout must continue while another
checkout is indexing. Test the complete path on a real linked worktree,
including both text and semantic results and observable version reuse.
An authorized search can initialize its requested checkout before any sibling
has published. Vector preparation continues in bounded batches while runnable
work remains, independently of the cadence of Git discovery.
Cold file preparation may commit a bounded batch together. Report a file as
prepared only after its batch commits. A restart reuses every committed
version, including versions from batches preceding an interrupted batch.

Converting previously populated index stores is outside this release's
acceptance criteria. A clean deployment builds the derived index from Git
and the current filesystem.

## Formal and implementation obligations

[`CheckoutPublication`](Muninn/CheckoutPublication.lagda.md) proves preservation
of the entire sibling slot, independence of distinct commits, admission under
unchanged checkout and storage generations and policy, use of a published snapshot
while storage is online, current-policy filtering of a pinned snapshot, and
preservation of compatible prepared inputs. It uses
[`Storage`](Muninn/Storage.agda) and [`Worktree`](Muninn/Worktree.agda) for
immutable references and coherent graph membership. The existing
[`FirstSearch`](Muninn/FirstSearch.lagda.md),
[`IncrementalObservation`](Muninn/IncrementalObservation.agda),
[`CheckoutState`](Muninn/CheckoutState.agda),
[`ReusePolicy`](Muninn/ReusePolicy.agda), and
[`StagedContent`](Muninn/StagedContent.agda) supply the other observation,
visibility, reuse, and continuation laws.

The runtime must supply truthful Git and filesystem observations, atomic
selector updates, safe reader retention and reclamation, and scheduling that
continues ready work. These are implementation obligations. Verification must
exercise a primary advance with untouched sibling references, overlapping
search and publication, initial edits with reusable checkpoints, Git
suspension, and immediate exclusion during deferred cleanup.
