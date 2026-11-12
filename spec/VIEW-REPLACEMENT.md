# Replacing a current-view selector

`ViewReplacement` changes a checkout's current association without rewriting
snapshot contents. It is a component of the eventual receipt-sealed publication
operation, not a separately dispatched mutation.

## Saved data and mutable selection are different

Searches retain their selected snapshot data, not the mutable association used
to select it. `OwnedState.privateTarget` extends the existing private-reference
boundary to published-view selectors. The existing admission rule checks it;
ordinary selection/status reads remain available.

`selectorNoIncoming` derives absence of incoming strong references from shared
admissibility. `selectorUnheld` additionally rules out direct and indirect
temporary search holds, including attachment paths. The caller does not supply
a promise that nobody holds the selector.

This lets the current association advance while old searches continue using
their unchanged snapshot versions and dependencies.

## Guard the actual association and target

The transaction checks the expected old association and a real target snapshot
of the same family and checkout in its current snapshot. A stale or unresolved
context takes the existing continuation path and aborts the transaction.

`committedReady` proves that any committed replacement passed those checks.
`unresolvedKeepsWorld` proves the exact rollback result and unchanged store.
An enclosing transaction can therefore roll back earlier tentative preparation
rather than leave a partially published view.

The new `writeResolvedAdmissible` law permits outgoing-reference replacement
only with resolved, private-safe references and unchanged record owner/kind.
It preserves the shared store invariant without pretending the new target was
already among the old selector's outgoing references.

## Preserve data and current-view consistency

The replacement preserves every other record. It retains all old snapshots,
reader data, captures and receipts. `protectedRecord` proves exact preservation
of any record retained by existing temporary use.

`viewsAfter` proves one current association per checkout and agreement with the
target snapshot. `currentVisible` identifies the actual new association.
`guardedReceiptFrame` proves receipt isolation for every committed component
execution, and `effect` supplies the existing ledger effect interface.

No separate task, status or operation-ID registry is introduced.

## Boundary

This is #112 under #84, following #108 / #109 and #110 / #111. The safe module is
imported by the aggregate. Composing filtered preparation with replacement,
canonicality across that completed publication step, receipt-controlled replay,
new-reader resumption and full lifecycle assembly remain subsequent work.
The original request stays active through those steps.

These are specification laws. Rust correspondence, live data, binaries,
installation and deployment are unchanged.
