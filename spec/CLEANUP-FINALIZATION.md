# Verified cleanup-task completion

`Muninn.CleanupFinalization` completes an accepted cleanup using the existing
shared transaction and receipt protocol. It does not add a task registry,
operation-specific failure state or replacement cleanup outcome.

## Decide completion from the current store

The task's stored family, typed owning request ID and original captured IDs
must match. Its payload remains uninterpreted metadata.

`noPending?` uses the existing exact classifier and independent
`CleanupCompletion.Pending` predicate. It checks the fixed captured IDs and
decides whether any record still requires deletion or projection. The decision
is complete because every pending record already carries its capture-membership
proof. Missing rows count as committed progress; needed shared data is retained.

`readyAfterCleanup` constructs this readiness from the actual finite cleanup
pass once pending use is released. It preserves the task's stored identity and
workset through that pass. It does not replace productive cleanup with a
caller-provided assertion that cleanup succeeded.

## One task-removal and receipt-completion transaction

The business effect rechecks readiness in its transaction snapshot. Only the
verified task can be removed. `committedReady` proves that any committed removal
was authorized by that check. The existing receipt update seals the removal
together with its completed result, after checking request identity and work
generation.

If work or task context remains unresolved, `unresolvedKeepsWork` proves that
the same receipt protocol returns its existing conversation continuation and
preserves the entire world. It cannot remove the task or report completion.

`checkedOutcome` establishes the unchanged full cleanup contract at the
verification boundary. The subsequent control step intentionally removes its
own private task and finishes its receipt; it is not misrepresented as a core
cleanup edit preserving every metadata row.

General laws prove:

- The actual transaction removes the task and saves the completed receipt.
- Admissibility, all indexed rows, other task records and other receipts remain.
- A completed-result retry preserves the observed world, including concurrent
  unrelated updates.
- An interrupted attempt followed by a completed retry converges to the same
  task removal and completed receipt.
- Existing history reclamation keeps the compact used-ID marker and leaves the
  task absent. It does not recreate a completed task.

The completion check runs again if indexing changes the store before the
transaction. It does not substitute a changed capture or trust an earlier check.

## Boundary

This is #106 under #84, following private bookkeeping #104 / #105. The safe module
is imported by the aggregate. Current-view production, scheduling integration,
policy supersession and the complete catalog dispatcher remain separate work.
The supplied rule is still the selected rule; this slice does not establish
that policy selection itself tracks a newer concurrent policy revision.

These are specification laws, not Rust correspondence or a claim of working
runtime cleanup. Live data, binaries, installation and deployment are unchanged.
