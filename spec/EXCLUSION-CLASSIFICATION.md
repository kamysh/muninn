# Exact finite exclusion classification

`Muninn.ExclusionClassifier` decides the independently specified `Needed` and
`Protected` predicates from `Muninn.ExclusionOutcomes`, over the entire
`OwnedState.World`. It does not replace those predicates or change their roots,
dependencies, policy gates or completion requirements.

The decisions are independent. A record may be permanently needed and also
temporarily protected; its protection must still prevent premature rewriting.
A positive decision contains evidence of the existing predicate. A negative
decision refutes every possible derivation of that predicate.

## Finite saturation

`Muninn.FiniteClosure` constructs the least rooted closure of a decidable edge
relation over a finite universe. The universe is all stored record identities,
including orphaned records and records outside the target family. The adapter
proves that every root and every dependency target belongs to this universe.
These coverage obligations prevent an incomplete traversal from appearing exact.

Each successful expansion removes an identity from the remaining list. A size
proof establishes strict decrease, even if the input list contains duplicates.
At zero, the same proof rules out any remaining candidate. The natural number
argument is a proved upper bound, not an arbitrary cutoff returning a negative
answer when work remains. All functions pass Agda's safe termination checker.

The resulting set contains only derivable records, includes every root and is
closed under dependencies. Induction on arbitrary reachability derivations
proves completeness. Cycles terminate and cannot independently establish need.

## Exact dependency decisions

The adapter checks actual database lookup, expected kind and allowed ownership
for reference dependencies. Attachment dependencies additionally require the
existing parent identity/kind, current permanent or temporary gate, and equal
ownership. Permanent roots and active-work/reader roots use separate saturation
instances and their respective fixed dependency rules.

Kind comparison uses a checked finite encoding and decoding retraction. Adding
an owned kind requires extending its exhaustive encoding and round-trip proof.
Payloads and proof terms need no equality instance. Stored lookup controls
classification even for a nonunique logical input; no admissibility assumption
silently substitutes a smaller world.

## Boundary

This is the classification slice #69 of #67. It performs no deletion, snapshot
rewrite, transaction, policy acceptance or worker scheduling. #70 must use the
exact decisions to prove cleanup effects and interruption/retry convergence;
#23 remains open for integration. Policy parsing, publication/read-state
consistency and Rust/SQL correspondence retain their existing obligations.

The finite decision procedure is a logical specification, not a promise about
the time or memory required by a production graph implementation. No running
service, binary, database or installation is changed.
