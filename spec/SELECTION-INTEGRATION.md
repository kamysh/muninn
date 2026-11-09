# Concrete selection and Git authority

Muninn asks Git for its ignore default. It does not reproduce the Git ignore
engine. Candidate enumeration uses a complete Git listing of tracked and ordinary
untracked paths; explicit Muninn inclusions additionally drive directory traversal
for ignored content. Tracked files therefore have a direct discovery route.

The intended adapters use batched, NUL-delimited Git interfaces from the checkout
root: `git ls-files --cached --others --exclude-standard --deduplicate -z` and
`git check-ignore --stdin -z`. Complete decoding and context invalidation belong
to the Rust correspondence obligation. See the official documentation for
[listing](https://git-scm.com/docs/git-ls-files) and
[ignore queries](https://git-scm.com/docs/git-check-ignore).

`GitIgnore.Query` retains family, checkout and relevant-input generation, with
unique requested paths. Complete indexed replies and membership evidence bind
each saved answer to an actual requested path. Freshness is checked before file
intake; captured answers stay with published data when Git operations suspend
indexing. This is a logical observation model, with no mandated duplication of
batch data in physical rows.

`IndexSelection` requires admitted policy evidence and fresh Git answers to
construct kept file entries and bindings. Its placement proofs check family and
checkout provenance. The agreement law ties the intake decision to the same
predicate used by search visibility and cleanup. Logical file-map entries now
include the Git-default Boolean, so moving-base/overlay laws preserve it without
forcing deltas for differences in receipt provenance alone.

`InclusionTraversal` derives conservative literal-prefix hints from actual
compiled patterns. Its general theorem proves that a selected ignored file
cannot be hidden by pruning a required ancestor. `GitDiscovery` schedules every
Git-listed candidate directly and always schedules the checkout root.

Persistent defaults and policy versions retain strict entry-admission evidence.
`StoredPolicy` reconstructs admitted effective rules from actual saved rows.
`ExclusionOutcomes` uses the concrete compiled resolver; cleanup, publication and
reader modules no longer take a freely supplied matcher. The family mask is
shared; the full decision additionally uses the saved Git answer for each path.

## Cleanup without exposing a hidden baseline

An excluded worktree override becomes the existing `Deleted` overlay form: a
small absence marker with no reference to its old file version. The marker stays
while the registered checkout needs it; it prevents baseline content from
reappearing. The obsolete version and its unneeded chunks, vectors and symbols
are reclaimed through the existing bounded cleanup transactions. A saved search
retains its actual data dependencies, rather than these private binding records.

`CleanupStorage` proves that normalization preserves ownership, kind and valid
placement, only drops outgoing references, and is idempotent. Search visibility
proofs cover both directions. The cleanup measure includes the removable version
reference, so normalization is real finite progress; completion requires the
stored binding to be canonical. No additional application error state or timeout
is introduced.

## Verification boundary

The verification target is the complete `spec/Muninn.agda` aggregate from the
committed dedicated worktree. The PR records the completed check and its commit.
This document specifies the intended Rust correspondence; it does not claim
that the running implementation already uses these adapters or laws.

No Rust, installation, live-data, deployment or system configuration changes.
