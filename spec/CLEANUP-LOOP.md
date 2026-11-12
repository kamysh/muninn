# Executable cleanup completion

`Muninn.CleanupLoop.Run.finishes` proves that the existing executable finite
cleanup pass reaches the unchanged full `ExclusionOutcomes.Complete` contract.
The inputs are an admissible store, its fixed covered workset, and evidence that
pending records are no longer in active use. It does not assume an eligible edit,
absence of pending work, or the final completion result.

## Productive work through completion

The pass executes the existing shared deletion/projection transactions. Each
transaction mutates at most one record, every actual edit strictly decreases
the existing record/member measure, and the total pass has a constructive
finite bound. That bound is a proof of termination, not a time limit or a
permission to discard unfinished work.

If an unneeded, unprotected record remains, its incoming dependencies belong to
the same candidate group. A needed canonical source would make the target
needed; an active holder would protect it. Both contradict the target's
reclamation conditions. The fixed reference ordering then gives an actual
eligible deletion in that nonempty group. Needed noncanonical snapshots
similarly provide actual eligible projections. Consequently, the pass cannot
stop with pending work once the released-use condition holds.

`completeTrace` applies this argument to arbitrary actual cleanup traces, and
`resumes` covers a committed prefix followed by a fresh pass from its observed
world. `CleanupAlignment` supplies the original-to-final preservation frame and
all other fields of the full completion contract.

## Existing use

`CleanupReleased.Released` concerns pending captured records only. Needed
canonical records may remain in use; unrelated readers do not have to stop.
The caller must establish that existing use of the pending records has ended.

The proof establishes this condition only once at the start. It then proves
that actual cleanup edits preserve it. Cleanup introduces no new protection,
needed content remains needed, and canonical needed snapshots stay canonical.
The proof therefore does not assume readiness at every intermediate world.

The admission rule preventing new direct or indirect holds on pending records,
and the scheduler's arrangement of existing-use release, remain integration
obligations under #84. This module supplies the productive computation and its
completion proof; it does not encode additional stopped or diagnostic outcomes.

## Bounded follow-up and the original task

`Followup.Current` takes a new fixed capture of the current family store for a
separate follow-up. `coversNewBlocker` includes every currently owned blocking
record, including records created after the original task was accepted. It
uses the same bounded transactions and proven executable pass.

`parentNoPending` proves that completing this follow-up also leaves no pending
cleanup for the original task's captured IDs. `savedOriginalTask` proves exact
retention of the original task record, including that unchanged ID list. A new
follow-up capture does not shrink or replace the parent's saved workset.

The follow-up's full before/after contract belongs to its own capture. The
parent's final no-pending condition checks its original IDs in the actual final
world; it does not attribute the follow-up's separately authorized mutations
outside that parent capture to the parent's own frame.

## Verification boundary

Both new modules use `--safe` and are included in `Muninn.agda`. The independent
outcome, keeper semantics, eligibility rules and database effects are unchanged.
The laws quantify over arbitrary admissible stores, identities and actual
traces. No fixtures, postulates or new diagnostic result layers are included.

This is #88, a productive-completion slice of #84. Admission, durable follow-up
scheduling and external availability/use integration remain unfinished under
that parent. Rust correspondence, live cleanup and deployment are not established
by this proof and are not changed by this specification slice.
