# Historical cleanup preservation

`Muninn.CleanupHistory.traceSafety` proves the existing
`ExclusionOutcomes.Safety` contract between the original and final worlds of
every actual cleanup trace from an admissible initial store. `passSafety`
applies the theorem to the executable finite pass. The workset, policy rule,
database semantics and independent preservation contract are unchanged.

## What must survive

Per-step safety cannot simply be assumed transitive: need and projection depend
on the world being observed. The proof first establishes that originally
protected and needed records retain that status after each actual cleanup edit.

`CleanupProtection` carries protection through unchanged holders, references and
attachment footprint. It proves exact retention of originally protected records
through the trace.

`CleanupNeedScope` derives registration support for every needed indexed record
of the selected family. The rootless-component theorem rules out indexed need
being justified by an unregistered orphan component. Reference-kind proofs
cover every owned constructor and distinguish permanent need from work/reader
protection.

`CleanupObservations` derives concrete observation support from the real cleanup
transactions: metadata remains unchanged, non-snapshot records cannot be newly
introduced, and unique identities remain unique. These are proved effects,
not promises supplied by a handler.

`CleanupViews` uses those effects to preserve positive live-checkout, binding,
publication, symbol and edge observations. Absence of a delta override is also
preserved. A binding that establishes a required view is itself rooted and
therefore retained; other-family bindings use the unrelated-data frame.

`CleanupNeed` then preserves roots, projected references and permanent
attachments for every original need derivation. Its proofs use the complete
owned world and the existing classifier semantics.

## Whole-trace snapshot content

Snapshot cleanup may remove members that were already excluded. It must retain
every originally required node and edge, even through several projections.
A general filter-absorption law composes those projections on the original
member domain. The proof carries ownership, kind, checkout identity and member
subset evidence through each step and establishes the original projected-content
equality at the final world.

The resulting `traceSafety` contains every original frame field: unrelated
records, metadata, required projected content and protected records. Existing
trace laws also preserve uncaptured records and prohibit fresh IDs.
Committed prefixes and subsequent cleanup segments concatenate;
`resumedPassSafety` applies the original frame to a restarted pass from the
observed committed world.

## Scope and verification boundary

The initial `OwnedState.Admissible` premise is the established store invariant:
unique IDs, valid placement and correctly resolved strong references. Cleanup
preserves it. The theorem establishes preservation of that invariant; it does
not add a corrupted-store diagnostic protocol.

These are cleanup-only traces under one fixed rule and captured-ID set. An
external reader release, publication, policy change or other operation is not
silently treated as a cleanup edit. #81 must define the permitted external
transitions and compose their obligations with recovery and eventual progress.
[Completion alignment](CLEANUP-ALIGNMENT.md) now combines historical safety with
proved reverse observations and need transport to derive the full cleanup-only
outcome from a current-state completion check. This does not establish eventual
completion across external waits or changes; that integration remains #84.

The existing observation/root predicates in `ExclusionOutcomes` are exposed as
named helpers for the proofs; their conditions and results are unchanged.
No Rust, live cleanup, deployment, service or installation changes are included.
