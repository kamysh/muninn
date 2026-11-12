# Releasing completed readers

Reader records are private bookkeeping: no strong reference may target a
reader. The shared `OwnedState.Admissible.privateReaders` invariant states this
for the whole store. Reader admission checks the rule alongside canonical
roots. Existing deletion, projection and insertion proofs preserve it.

`Muninn.ReaderRelease.finish` checks the current record's owner and reader kind
in the same transaction that deletes it. An already absent reader returns the
same ready continuation without writing. A different record is preserved and
uses the caller's existing replanning continuation. There is no empty reader
record or new terminal result type.

`privateUnreferenced` derives the no-incoming-reference condition from the
shared store invariant and reference soundness. `admissible` therefore proves
that actual release preserves the whole admissible store. `idempotent` proves
that repeating the transaction preserves its reply and resulting world.
`finishedAbsent` proves actual removal of the finished reader record.

`indexedRow` preserves every indexed record exactly. `savedWorkset` preserves
each saved cleanup task and its captured identities; `receiptFrame` preserves
the shared receipt ledger in both directions. `otherRow` preserves every other
record, and `otherReaderHolds` preserves temporary protection from every other
holder, including indirect dependencies. `noNewProtection` proves that release
cannot create protection that was absent before.

## Productive cleanup after release

`ReaderReleaseCleanup.Current` executes the actual release transaction followed
by the existing finite cleanup transactions in one shared `Execution.Script`.
`workflowCompletes` proves a completed execution. `savedWorkset` preserves old
task captures across both parts.

`cleanupComplete` proves the existing full cleanup outcome when the finished
reader was the last holder of records still pending in the fresh pass. This is
the explicit `OtherUseReleased` condition: other holders may continue using
unrelated or canonical needed records. The proof derives the required released
condition after deletion; it does not assume the final cleanup result.

If another holder still needs pending records, its use remains protected and
the surrounding lifecycle must arrange its completion. This slice supplies
the release action and its preservation/progress connection. It does not add
another waiting-state or diagnostic protocol.

## Boundary

This is #94 under #84, following #92 / #93. The safe modules are imported by
the aggregate. Current-view production, durable follow-up scheduling and the
complete request/policy lifecycle remain under #84. The release helper belongs
inside the existing receipt-controlled request and incarnation lifecycle; it
does not introduce another operation-identity protocol.

These are specification changes and universally quantified proofs. Rust
correspondence, live cleanup, binaries, services and deployment are unchanged.
