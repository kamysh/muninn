# Durable follow-up cleanup capture

`Muninn.CleanupScheduling` saves a fresh, fixed family capture in an existing
`cleanupWork` record. The business transaction is sealed by the shared receipt
update, so the capture and checkpoint commit together. No separate operation-ID
or task-status registry is introduced.

The capture contains the current family records and the new task's bookkeeping
ID. This covers the complete accepted family store without changing an older
task's saved IDs. Bookkeeping is retained by the existing cleanup contract.

## Atomic acceptance and retry

The internal allocator supplies a proposed incarnation ID. Creation checks all
current row IDs and tracked weak IDs in the same transaction. An unavailable
ID cannot overwrite a record or advance the checkpoint: the shared abort and
continuation semantics preserve the prior work. This helper does not introduce
a wire error or require an agent to choose storage IDs.

`commits` proves the actual receipt-controlled transaction's result and final
store. `afterValid` preserves the shared admissibility invariant, including
private readers. `savedCapture` identifies the exact persisted capture, and
`savedOriginalWorkset` retains the original task's record and ID list.

`retryObserved` proves that an old checkpoint is skipped whenever its saved
successor is found, including worlds changed by unrelated indexing since the
commit. The whole observed world is preserved. `retryKeepsCapture` gives the
saved task's exact ID list after a lost-acknowledgement retry.

`atomicCapture` uses the shared interruption semantics: an interrupted attempt
leaves the original world or the world containing both task and checkpoint.
`converges` proves that a completed retry reaches that same accepted world.

## The saved capture drives productive cleanup

The worker's `Intent.keys` is the saved task's actual captured list. Its coverage
proof covers every owned record in the accepted world, including orphaned
index records. The model does not substitute a new capture when work resumes.

`cleanupComplete` applies the existing productive pass and unchanged full
cleanup contract once pending active use has ended. `persistsThroughCleanup`
preserves the saved task and capture across every actual cleanup trace.

This is #96 under #84. Automatic scheduling choices, current-view production,
policy supersession and full request lifecycle integration remain unfinished
under that parent. Both the receipt and worker use the shared database model.
The safe module is imported by the aggregate. Rust correspondence, live cleanup,
binaries, installation and deployment are not established by this slice.
