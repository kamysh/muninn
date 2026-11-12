# Effective rules come from stored policy

`StoredPolicy` follows the family-owned current-policy pointer to its saved
version and that version's frozen defaults. All three lookups belong to the
same complete owned world. Resolution checks their owner and body kind.

`OwnedState.defaults` now holds the existing typed `PolicyDefaults`.
`PolicyVersionInfo` holds the typed family identity, revision and existing
`PolicyDraft` fields. The version keeps its strong reference to the separate
defaults record; the current pointer keeps its reference to the version.
No table or new physical storage layout is prescribed.

## Actual observations determine the rule

Each successful `Saved` observation carries the actual pointer, version and
defaults lookups. `policy` reconstructs the existing `FamilyPolicy` from the
version and referenced defaults. `rule` uses that policy's effective exclusion
list, with saved defaults before family rules.

`deterministic` proves that any two observations of the same current pointer
give the same policy. `selectsKnown` proves completeness when the three actual
records exist under the expected owner; the resolver cannot silently omit such
a policy. `effectiveExclusions` exposes the exact ordered stored lists.

## Shared-transaction selection and supersession

`withCurrent` reads the policy inside the shared transaction and supplies its
actual rule to the next operation. Missing context invokes the existing context
continuation; an aborting continuation leaves the complete world unchanged.

`withRetained` also compares a worker's retained version and revision with the
actual observation. A changed version or revision invokes reconsideration with
the current rule and does not execute the old worker continuation. A matching
observation executes the current-rule continuation. This does not finish or
discard the original request; its receipt remains the surrounding protocol's
responsibility.

## Boundary

This is #120 under #84 and #23/#24/#25. Glob parsing and Git-ignore precedence
remain #26, including the pending syntax/traversal choices. Full policy-change
acceptance, immutable history transitions, automatic cleanup supersession and
the complete scheduler remain separate work. Logical owner incarnations are not
a new physical family-ID format; resolving external locators/UUIDs to those
owners remains part of the adapter/catalog obligations.

The shared ownership and reference invariants remain; their existing proofs
must still check with the typed payloads. This is Agda and documentation only,
not a Rust correspondence proof, live data change, installation or deployment.
