# Atomic current-view publication

`ViewPublication` composes the existing filtered-copy preparation, guarded
selector replacement and receipt ledger. Its operation commits the new snapshot,
the checkout's current association and the original request's checkpoint in one
shared database transaction.

## Actual effects and preservation

The business transaction uses `SnapshotPreparation.prepare` followed by
`ViewReplacement.replace`. Neither introduces an intervening commit. Its
receipt-isolation certificate is derived from the fresh snapshot insertion and
the guarded selector write over arbitrary worlds, not supplied as an operation
assumption.

For an admissible live current checkout, `Current` constructs the replacement's
readiness from the copied snapshot and preserved original selector. The actual
committed store satisfies:

- The selector identifies the fresh filtered copy.
- The copy remains canonical after both selector and receipt writes.
- Shared-store admissibility and current-view uniqueness/checkout agreement hold.
- Every previous snapshot, saved reader and captured cleanup workset is unchanged.
- The original request stays active at its next generation and retains its
  accepted version references.

`PublicationVisibility` derives the canonicality steps from the actual writes.
There is no caller-supplied unchanged-filtering premise.

## Interruption, retry and continued conversation

The generic interruption semantics admits either the original store or the
whole committed publication, including a lost reply. Retrying the old generation
resumes its existing receipt without allocating another snapshot or replaying
selector replacement. `converges` proves the completed retry reaches the same
committed store; `terminates` constructs a completed local script for any world.

If preparation or replacement needs more context, its existing abort continuation
rolls back the tentative copy and keeps the original receipt and store. The
ledger carries the same request forward through corrective dialogue.

## Boundary

This closes the #115 specification slice under #84, using #114's visibility law.
The policy argument is fixed. Linking publication to the latest stored policy,
constructing new-reader proposals and assembling the complete worker lifecycle
remain separate work. The broader catalog still must require these invariants
at dispatch; this module is not the completed product protocol.

Agda and documentation only. Rust correspondence, live data, installed binaries,
system configuration and deployment are unchanged.
