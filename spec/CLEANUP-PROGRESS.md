# Finite active cleanup passes

`Muninn.CleanupProgress` selects and executes eligible edits from the fixed
accepted workset using the existing `CleanupEffects` transactions. Every step
reassesses its own current complete world through the shared database semantics.
It does not supply a different keeper predicate or redefine task completion.

## A decreasing measure of actual effects

Every stored record contributes one unit. Structural snapshot nodes and edges
contribute additional units. Thus orphaned records and every owned category are
counted even when no registry or other record refers to them.

General laws prove that an actual committed deletion strictly lowers this
measure. A projection can only filter existing snapshot members, and eligibility
requires an actual member change, so its committed overwrite also strictly lowers
the measure. The overwrite proof accounts for the database's real delete/write
behavior, including duplicate logical keys; no admissibility premise is needed
for the decrease itself.

## Total pass and arbitrary traces

The pass searches the finite captured-ID list for any eligible removal or
projection, executes the shared transaction, then repeats against the resulting
world. It stops only with proof that no captured ID currently has an eligible edit.

Its recursion capacity is justified by the current world measure. At zero, an
eligible edit would contradict the strict-decrease proof. There is no arbitrary
cutoff that silently discards remaining eligible edits.

For every mutating trace, not only the chosen traversal, the number of committed
edits plus the final measure is at most the initial measure. Store admissibility,
unrelated records, metadata, uncaptured records and absence of new IDs are
preserved through the trace. Each individual edit retains its existing current-
state need/protection safety proof.

A restart computes a pass from the observed committed world and the same fixed
workset; its bound depends on that world. No local deletion cursor is restored.
Repeating a pass at its stopping world without any intervening state change
performs zero edits and preserves that world.

## Stopping is distinct from completion

The pass result carries an actual-effect trace and proof of no currently eligible
edit. It carries no proof of `ExclusionOutcomes.Complete`, and must not be reported
as cleanup-task completion. Captured records may still require temporary
protection to be released or incoming dependencies to be resolved.

The completion condition and original-request preservation are established in
`CleanupCompletion` and `CleanupAlignment`. The remaining worker in #84 must
execute productive bounded batches, arrange cleanup of newer blocking records,
and continue until that condition holds. Repeated-pass idempotence alone does
not establish full task completion. Parent #73 remains open.

This is a logical active-pass kernel, not a deployed worker or a claim about
Rust/SQL correspondence, scan cost or elapsed execution time. It adds no runtime,
database, binary, service or installation changes.
