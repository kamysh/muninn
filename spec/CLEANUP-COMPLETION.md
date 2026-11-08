# Completion and dependency classification

`Muninn.CleanupCompletion` assesses a stopped cleanup pass against the existing
`ExclusionOutcomes.Complete` contract. It checks actual captured records in the
complete owned world. It does not change that contract, the fixed workset,
eligibility rules or database effects.

## State-level completion

A pending record either still needs reclamation or has needed snapshot members
that still require projection. Finite lookup and exact need/protection decisions
identify such records. The projection view proves that every noncanonical
projection is an actual indexed, family-owned member change.

Absence of pending records constructs every field of the existing completion
contract at the observed state, including uniqueness, canonical needed content,
absence of captured unneeded data and the preservation fields. Conversely, each
pending witness refutes that same completion contract. A stopped pass alone is
not sufficient evidence.

The state assessment uses `Complete ... world world`. It certifies the observed
state against the original captured IDs. It does not replace the outstanding
recovery obligation to compose the historical trace and its preservation frame
from the earlier world. That composition and external-wait convergence remain
#77; the final operation dispatcher must require their full contract.

## Concrete dependencies and ordering

An incoming-dependency witness contains an actual stored source row and one of
its strong references to the pending ID. Its source is classified as inside or
outside the accepted workset; a worker cannot omit the dependency by choosing a
smaller store.

`Muninn.CleanupOrder` assigns reference ranks with exhaustive owned-kind/body
coverage. Every correctly resolved strong reference from an indexed record
strictly decreases the rank. Thus a chain of valid indexed references cannot
cycle. A raw observed cycle is validated separately: the proof extracts an
actual reference that does not resolve to the required stored kind/owner. This
is evidence about that reference, not a new fatal exit or an automatic repair.

A finite maximum-rank argument proves that a nonempty, closed group of
unprotected, unneeded captured records contains a real eligible deletion. This
derives progress from the reference model instead of assuming an edit exists.
The canonical candidate list has both soundness and completeness proofs, so a
caller cannot manufacture a boundary by leaving a candidate out.

## Exact waiting obligations for an admissible store

For an admissible stopped world with pending work, the stronger result type
allows only:

- A pending record with actual temporary-protection evidence.
- An unprotected reclamation candidate with a concrete incoming reference from
  outside this task's immutable captured-ID set.

The proof propagates need and protection through valid references. A needed
captured referrer must already be canonical or protected at rest; neither case
can hide an unprotected, unneeded target. Remaining candidate-to-candidate
dependencies are ordered by the rank proof. Consequently a final dependency
boundary must belong to later work, not another silently skipped candidate.

`assessPass` applies this classification to the actual finite-pass result and
uses its admissibility proof. The recovery protocol in #77 must arrange the
relevant protection release or later cleanup work, wait for a state change,
reassess current need and preserve the fixed capture. It must not repeatedly run
an idle pass or announce completion while the pending witness remains.

For unique worlds without admissibility evidence, the weaker raw assessment
still returns an actual dependency/protection and a proof that completion is
false. It cannot use the stronger valid-store result. Malformed-cycle evidence
remains available for the separately agreed repair/dialogue protocol.

This slice changes Agda and documentation only. It adds no Rust implementation,
live cleanup, installation, deployment or service changes.
