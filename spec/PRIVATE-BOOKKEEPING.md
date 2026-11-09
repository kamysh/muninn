# Private execution bookkeeping

The user-approved privacy boundary covers readers, cleanup tasks, accepted work
queues, continuations and request receipts. These records describe execution;
search holds cannot target them. Status tools may read them normally. Code and
curated notes remain searchable.

## One invariant at the shared store boundary

`OwnedState.executionBookkeeping` classifies every record kind explicitly.
`PublicReference` admits only targets outside the private categories.
`Admissible.privateBookkeeping` requires that every stored strong reference
satisfy this condition. The previous private-reader property is derived from
this stronger invariant, so callers cannot silently retain the narrower rule.

Admission checks this predicate for each proposed reference. Shared insertion,
update and deletion preservation proofs retain it. Adding a new record kind
requires an explicit classification rather than inheriting a catch-all case.

`OwnedState.privateUnreferenced` derives the complete no-incoming-reference
deletion guard for any stored private record from admissibility and its actual
kind. It does not ask a caller to assume the record is unreferenced. Reader
release uses this same general proof.

This restricts strong references to execution bookkeeping, not references from
it. Accepted work and active receipts still retain required file versions;
readers still retain the exact saved-view footprint. Cleanup captures and idle
continuations keep their existing weak incarnation identities.

## Cleanup belongs to the accepting request

A `cleanupWork` body now contains a typed `OperationId`, its fixed captured
record IDs and its existing metadata. The shared receipt-controlled scheduling
transaction uses the same request ID for the task and its accepting checkpoint.
`ownedCapture` proves both are present after that actual transaction.

Automatic allocation uses that same owner ID. Replay preserves the accepted
capture rather than assigning a new owner or recapturing. Original-workset and
worker-trace preservation laws quantify over and preserve every task's owner ID
as well as its original record IDs. No second receipt or task registry is added.

## Boundary

This closes #104 under #84. The safe aggregate checks the strengthened store
invariant and all adapted cleanup, admission, allocation and release proofs.
The next lifecycle slice must verify cleanup completion, remove its private task
and finish/reclaim the existing receipt while keeping the agreed compact
request-ID marker. This slice does not implement that transition or claim
the full cleanup lifecycle is complete.

These are specification laws. Rust correspondence, live data, binaries,
installation and deployment are unchanged.
