# Resuming readers after cleanup

`Muninn.CleanupResumption.Current` connects a fresh family cleanup pass to the
existing guarded reader-admission transaction. It captures the current family
once, executes the existing finite pass, then admits the original request's
reader using its current-view proposal.

`noFence` derives that the resulting world has no pending admission claim,
including claims in older saved cleanup tasks. It does not assume that the
admission guard is satisfied: the fresh capture covers every remaining family
row, and the executable pass removes unneeded rows and projects needed
snapshots after their pending use is released. This supplies the guard's
`Allowed` obligation.

`workflow` compiles the actual deletion/projection trace and reader admission
into the shared `Execution.Script`. `finishes` proves a completed execution
from the initial world to the stored reader and the caller's ready continuation.
Both continuation callbacks receive the same original `Catalog.Request`.
`savedWorkset` preserves every saved cleanup task and its original captured IDs
through both parts of this execution.

The remaining admission prerequisites are explicit: an unreserved reader
identity and resolving, canonical current-view references. This module does
not produce those references or schedule external work. Existing use of pending
records must have ended before this finite pass; unrelated use may continue.

This is specification slice #92 under #84. Current-view production, durable
follow-up scheduling, holder release and request/policy lifecycle integration
remain unfinished. The safe module is imported by the aggregate. These laws
do not establish Rust correspondence, live cleanup or deployment.
