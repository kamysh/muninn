# Cleanup completion and constructive progress

`Muninn.CleanupCompletion` establishes the existing
`ExclusionOutcomes.Complete` contract from actual stored records. It preserves
the outcome, fixed workset, eligibility rules and shared database effects.

A pending record still requires reclamation or canonical snapshot projection.
Absence of pending records constructs the completion certificate. A concrete
pending record excludes that certificate, so cleanup cannot claim completion
while requested work remains. `CleanupAlignment` connects this condition to
the full original-request outcome across actual cleanup traces and retries.

`Muninn.CleanupOrder` proves that correctly resolved references from indexed
records strictly decrease a fixed rank. Such references cannot form a cycle.
The finite maximum-rank argument in `closedComponentProgress` then constructs
an actual eligible deletion from a nonempty closed group of unneeded,
unprotected records. It establishes productive cleanup work rather than
describing a stopped outcome.

The speculative bad-store cycle validator, duplicate assessment layers and
stopped-state diagnostic trees have been removed. They were not used by the
completion, preservation or constructive deletion proofs. Generic request
dialogue, shared transaction semantics and interruption/convergence obligations
remain because they prevent incorrect writes and require work to reach its goal.

[CleanupLoop](CLEANUP-LOOP.md) now connects the executable bounded operations
to that full completion condition once pending use is released. Existing readers may finish safely, and needed
shared data must remain available. The runtime worker and its integration remain
unfinished under #84. These Agda proofs are not a runtime cleanup fix.
