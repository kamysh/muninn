# Preparing a fresh filtered snapshot

`SnapshotPreparation.prepare` is a component of the eventual atomic publication
transaction. It reads the actual source record, checks its family, allocates a
fresh incarnation from the same transaction snapshot and inserts the independent
outcome model's filtered copy. It then invokes the publication continuation.

There is no commit inside this component. The caller must switch the published
association and seal receipt progress before committing. This helper is not a
separately dispatched mutation and does not claim standalone replay safety.

## Actual source and continuation

The component follows the stored source snapshot rather than accepting
caller-supplied node/edge contents. A missing source or another family's
snapshot takes the supplied existing context-recovery continuation without
inserting a copy. General laws establish both paths.

`prepares` proves the actual evaluator behavior for any transaction continuation.
`preparesCopy` specializes it to the current stored view. Allocation uses the
existing complete live/weak reservation set, so old tracked IDs are not reused.

## The copy is canonical in its resulting store

The current source is identified by the actual published association and stored
snapshot. Its need follows from that reference, registration and checkout state.

General filter and projection idempotence laws establish that repeating the
same independent selection does not change its result. The existing visibility
preservation and projection-absorption laws show that inserting the snapshot
does not change its selected contents. `copiedCanonical` proves the copied
snapshot is canonical in the resulting store, not merely before insertion.

The proof instantiates general cleanup/projection laws over the actual source
world. It neither creates a cleanup task nor replaces a saved task's workset.

## Preservation

Every original record retains exactly its prior logical value.
This includes old snapshots and readers, their saved data, cleanup captures and
request receipts. Store admissibility is preserved using the source's resolved,
private-safe references and the existing projection subset law.

Current-view associations remain unchanged. `viewsAfter` preserves uniqueness
and snapshot-checkout agreement; `receiptFrame` preserves the complete existing
receipt population in both directions.

## Boundary

This is #110 under #84, following #108 / #109. The safe module is imported by the
aggregate. Switching the current association, receipt-controlled replay,
new-reader admission and full lifecycle assembly follow separately. The
original request remains active through those steps.

These are specification laws. Rust correspondence, live data, binaries,
installation and deployment are unchanged.
