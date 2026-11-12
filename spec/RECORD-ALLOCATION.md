# Fresh tracked record incarnations

`Muninn.RecordAllocation.allocate` constructs an unreserved logical incarnation
for every finite owned world. `freshId` selects one above the largest reserved
ID. `fresh` proves it is absent from the complete reservation set, and
`reservedSmaller` covers every currently reserved identity.

Reservations include live row IDs and weak IDs retained by saved work. An ID
whose indexed row has been deleted is therefore still unavailable while a
cleanup task or continuation tracks it. This uses the existing shared
reservation semantics rather than a new counter or identity registry.

## Allocation belongs to the transaction

The reader `admit` entrypoint selects its ID from the same shared transaction
snapshot used by the existing guarded admission. `admits` discharges freshness
internally; the existing resolution, canonical-root and cleanup-footprint
requirements remain. Admission still preserves admissibility and receipts.

The task `create` entrypoint also allocates inside the shared transaction.
`creates` proves that task creation commits for every world without requiring a
caller-provided freshness proof. Its `effect` uses the existing receipt protocol.
There is no allocator wire error or request for an agent to supply storage IDs.

`Current.commits` proves the actual automatic-allocation transaction and its
checkpoint result. `retryObserved` suppresses old-checkpoint replay even when
unrelated work has changed the world. `atomicCapture` and `converges` establish
the same interrupted-attempt/completed-retry guarantee for this entrypoint.

The persisted capture, admissibility, original-workset preservation and
productive cleanup proof are the existing durable-capture laws instantiated
with the constructed fresh ID. Those outcomes are not weakened or replaced.

## Boundary

This is #98 under #84, following #96 / #97. The safe module is imported by the
aggregate. It does not choose the pending search-footprint or completed-task
privacy/removal rules. Current-view production and full lifecycle integration
remain unfinished. These are specification laws; Rust correspondence, live
data, installation and deployment are unchanged.
