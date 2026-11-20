# Selection-maintenance interruption checks

The active issue #203 adapter is serialized maintenance; see
[the approved contract](ISSUE-203-SERIALIZED-MAINTENANCE.md).
It uses PostgreSQL transaction rollback and durable pending requests.

## Registered boundaries

`CRASH-BOUNDARIES.json` and `maintenance.rs::CRASH_BOUNDARIES` describe three
commit boundaries:

- Request acceptance: pending targets commit with the selection-policy change,
  or before processing a Git-triggered refresh.
- Target publication: the manifest, structural view, unused-data cleanup and
  completed generation commit together.
- Failure metadata: a separate transaction records the error while retaining
  the pending request.

`scripts/check_crash_boundaries.py` checks that registration matches the manifest.
`muninn-setup/crash-injection-check.sh` invokes that registration check through
the guarded fixture. Registration alone is not crash-injection evidence.

## Observed coverage and limits

The `serialized_maintenance` disposable-database test injects a preparation
failure, checks that pending work and retained data survive, and retries using
a new connection. The existing worktree persistence scenario changes a file
during publication and checks that the transaction preserves the old view.
These are failure/rollback and reconnect tests, not process-kill tests at every
commit boundary. They do not prove PostgreSQL or the Rust implementation.

The earlier concurrent workset/reader-pin/receipt adapter in `cleanup.rs` is
superseded for this operation. It is not the active runtime maintenance path.
