# Current published views and retained snapshots

A checkout has one current published structural view. Older snapshot versions
can remain for running searches or other accepted work; storage alone does not
make them current or permanently needed.

## Explicit state and domain invariant

`OwnedState.publishedView selected snapshot` is a family-owned logical
association. Its strong references identify the checkout and structural
snapshot with their expected kinds. It does not require a new SQL table.

`PublishedViews.Valid` states one publication association per family/checkout
and agreement between that checkout and the stored target snapshot.
`currentUnique` proves that two current-view observations for the same checkout
identify the same snapshot. `currentMatchesCheckout` exposes the matching
stored snapshot rather than accepting an unrelated checkout's version.

These domain conditions must be preserved by the assembled publication/catalog
operation in addition to shared ownership/reference admissibility. This slice
defines them; it does not yet implement that publication transition or assert
that the complete dispatcher enforces them.

## Reachability follows publication

A live registered checkout's published-view association is a permanent root;
`currentSnapshotNeeded` derives the target snapshot's need from actual stored
references and store admissibility.

A structural snapshot itself has artifact role. `storedSnapshotNotRoot` proves
that storing it does not independently root it. Permanent references to snapshot
records come only from published-view associations; this is checked for every
owned constructor by `onlyPublishedReferencesSnapshots`.

Running readers still retain their exact saved snapshot references and
dependencies. The existing protection and productive cleanup contracts remain.
An old snapshot can therefore survive while a reader needs it, then become
reclaimable after the published association has moved and its active uses end.

The published association has cleanup rank above its snapshot target.
Unneeded associations are reclaimed before their targets; a still-needed
association prevents removal of its current snapshot through ordinary
reference soundness.

## Preservation proofs

General forward and backward resolution laws now support snapshot targets that
are projected during cleanup. The earlier blanket exclusion of such targets
cannot apply to explicit publication references.

Snapshot checkout identity is preserved directly by `projectCheckout`,
`projectionCheckout` and the actual trace-ancestry law. Cleanup history no longer treats a snapshot's root role
as its checkout identity. The full content, isolation, admissibility and
productive-completion requirements are retained.

`validAfterCleanup` proves that every actual cleanup trace preserves the
current-view domain invariant: surviving associations remain unique and still
identify a stored snapshot of the same checkout. This uses trace ancestry and
reference soundness, not an assumed successful association check.

## Boundary

This is #108 under #84. The safe aggregate checks the corrected reachability
alongside existing cleanup, admission, allocation, reader-release and original
request finalization laws. Constructing a fresh filtered version, atomically
switching publication, and enforcing the domain invariant in the closed
catalog remain subsequent slices.

These are specification laws. Rust correspondence, live data, binaries,
installation and deployment are unchanged.
