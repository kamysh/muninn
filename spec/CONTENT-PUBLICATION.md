# Content and structural publication

This is the issue #30 specification contract. It adds no Rust implementation,
SQL migration, runtime installation or live database change.

## Intent before storage

`GenericFileMap.For` supplies the same map algebra to both the original
`Worktree.FileEntry` and logical owned-row entries. `FileMap` retains its public
interface. A logical owned-row entry identifies an immutable file-version row
and its saved Git-ignore default; it does not choose a physical SQL layout.

`ContentViews.Family` reads actual `baseBinding` and `deltaBinding` rows in
`OwnedState.World`. `findSound` and `findComplete` connect the projection to
matching owned rows. The consistency requirement prevents a conflicting second
binding from being hidden by choosing the first row.

`ContentPublication.Plan` fixes the desired result independently of the storage
transaction:

- Apply the current family selection policy to the completed selected file map.
- For a base publication, replace the shared base with that selected map.
- For a non-base publication, retain the shared base subject to current
  exclusions. Filtering the base avoids creating an exclusion-only deletion
  override separately in every checkout.
- For every other existing checkout, retain its previously completed file map
  as filtered by the current policy. Paused or Git-suspended checkouts are not
  re-read to preserve this result.
- Recalculate only the differences between each intended map and the next base.

`resolves`, `minimal`, `selectedView`, `otherView`, `noResurrection` and
`minimalStored` are universally quantified laws. Stored representation is
checked against these calculated maps; an adapter cannot supply another goal.
Representation obligations cover actual checkout records, not infinitely many
unused numeric identities.

## Original Git checks and fresh intake

Preserving an inherited entry retains its Git query with its real original
checkout. `OwnedState.DeltaOrigin` requires the same family, without pretending
that Git was queried in the receiving checkout. `preservedDeltaPlaced` proves
that an existing base binding may become a checkout difference while retaining
that evidence.

Fresh indexing remains stricter: `IndexSelection.Checkout.File.fresh` requires
the family, checkout and relevant-input generation of the answer to match the
current indexing context. Moving an existing entry is not fresh indexing.

## Fixed world outcome and one atomic boundary

`ContentPublication.Family.Current` takes the actual saved policy, the completed
file map, completed structural nodes/edges and the original request receipt.
These inputs fix `Outcome`; the storage adapter does not choose it.

An outcome requires:

- Exact base and minimal-overlay representation, with consistent owned rows.
- Store ownership/reference admissibility and valid published selectors.
- A current selected structural snapshot containing the supplied completed
  nodes/edges, canonical under actual current file selection.
- Unchanged other-checkout selectors, existing data, readers, jobs and settings.
- Other-family isolation in both directions.
- A durable cleanup task belonging to the original request, capturing all old
  family record IDs. This includes every old record whose reference publication
  can detach. The existing bounded cleanup worker rechecks need before deletion.

`PolicyGuard` reads the expected immutable policy-version pointer inside the
shared database transaction. `committed` proves that any commit observed the
expected pointer. A changed pointer preserves the old world and returns to the
existing corrective dialogue so work can be prepared under the new policy.

A `Prepared` value must contain an actual `ReceiptLedger.Effect`, a proof that
its transaction commits, and a proof of the fixed outcome in the real final
world, including the checkpoint write of the original receipt. This is a
mandatory refinement obligation, not an assumed custom atomic-effect relation.

`Run` composes that effect with the policy guard and the guarded checkpoint
update of the original request. `commits`, `retry`, `boundary` and `converges`
prove that an interrupted atomic publication followed by a completed retry
reaches the fixed world outcome without repeating its writes. `completes`
constructs a completed local transaction execution. The receipt stays active;
this publication is not a claim that cleanup is already complete.

## Verification boundary

The checked proofs establish map algebra, actual-row projection properties,
fixed outcome requirements, policy guarding, atomicity and retry composition.
They are parameterized by a proof-carrying storage realization. This change
does not construct a general row-writing adapter or certify the current Rust
SQL transaction. Finite prepared input, actual Rust/SQL representation, provider
and filesystem observations, and implementation correspondence require their
own adapter evidence. In particular, `Prepared.outcome` is an obligation an
adapter must discharge; type-checking this interface does not discharge it for
Rust.

Closed dispatch must require the certified publication interface (#51), and
Rust correspondence/coverage remains #52. Parser semantics and retrieval remain
their existing issues. No custom physical tree or new failure mechanism is
introduced by this contract.
