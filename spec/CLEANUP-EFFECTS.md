# Bounded cleanup transactions

`Muninn.CleanupEffects` defines current-snapshot cleanup transactions over the
shared `OwnedState.DB`. It uses the exact `ExclusionClassifier` decisions and
the independently specified `ExclusionOutcomes.Safety`; neither the keeper
predicate nor the world can be replaced by an operation.

## Decision and effect

The accepted workset contains immutable record-incarnation IDs. Each transaction
scans the current complete world and assesses one requested ID. It can:

- Remove a captured, family-owned indexed record that has neither lasting need
  nor temporary protection, once no strong reference points to it.
- Replace a captured, needed, unprotected mixed snapshot with its independent
  projection, provided that projection actually changes its members.
- Leave the store unchanged when neither edit is currently eligible.

The decision includes proof of eligibility or proof that neither edit is
eligible. Universally quantified execution laws establish the actual committed
delete or projection whenever its eligibility conditions hold. A transaction
cannot silently retain an eligible record and still satisfy those laws.

The shared scan and its selected mutation belong to the same transaction.
Assessment is not frozen at policy acceptance or supplied by an earlier caller.
An aborted transaction retains the original world by the shared database
semantics; this module introduces no alternative commit or rollback model.
The shared interruption relation also proves safety and admissibility at every
observable boundary of this one-transaction script, including a lost acknowledgement.

## Preservation

The general transaction laws establish:

- The existing complete-world safety contract: unrelated data, metadata, needed
  content and temporarily protected records survive.
- Unchanged records outside the accepted workset and no newly created IDs.
- Unique identities, placement and every strong reference remain valid when
  the input world is admissible.

`Muninn.CleanupStorage` proves the overwrite/reference transport laws and an
exhaustive projection view for every owned body constructor. Projection only
removes members/references, preserves owner and kind, and is idempotent with
respect to its assessment snapshot. Protected snapshots cannot be rewritten.

The incoming-reference guard prevents an intermediate committed deletion from
leaving a dangling reference, even when both records are ultimately reclaimable.
Other cleanup steps must remove the referring record or trim its snapshot first.
Dependency-ordering progress is a separate obligation; a safe waiting step is
not a claim that the overall task is finished.

## Mutation bound

`MutationBound` is indexed by the actual shared database transaction syntax.
`transactionBound` proves at most one `put` or `remove` statement, including all
branches selected by the scan. An additional write cannot inherit the old proof.
For an admissible world this changes at most one record incarnation. The bound
does not promise constant-cost classification, a fixed number of scanned rows,
or a fixed number of structural members inside one snapshot record.

## Remaining work

This is #72, the safety slice of #70. #73 retains progress and interruption/retry
convergence, including dependency ordering and eventual completion against the
independent outcome. Parent #70 and #67 remain open for integration; #23/#24/#25
retain complete operation, policy supersession, scheduling and receipt work.

These are logical database effects and quantified proofs. They do not implement
Rust/SQL correspondence, operate on the live database, install a binary or change
a service. Public status and corrective dialogue retain their existing contracts;
the internal `unchanged` reply is neither a failure nor task completion.
