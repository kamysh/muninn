# Completion relative to the original request

`Muninn.CleanupAlignment.complete` proves the unchanged full
`ExclusionOutcomes.Complete` contract from the original world to the final world
of an actual cleanup trace. Its inputs are an admissible initial store and the
existing completion certificate at the final observed world. The theorem does
not replace the original world with the final world in the requested outcome.

`completeFromNoPending` constructs that final certificate from the existing
finite pending-work predicate, then derives the original-request outcome.
`passComplete` applies it to the executable finite pass. `resumedComplete` and
`resumedPassComplete` concatenate a committed cleanup prefix with a later pass
without changing the original world, rule or captured incarnation IDs.

## Why another proof is needed

An observed-state completion check alone cannot establish that an operation
preserved what was required at its start. Historical safety supplies that frame,
but snapshot canonicalization and reclamation still refer to the world's need
and visibility predicates. Those predicates must be related across real edits.

`CleanupReverseViews` proves that cleanup cannot introduce positive control,
binding, publication, symbol or edge observations. Binding and visibility
transport require registration support from the original world. A live delta
binding, including a deletion marker, is itself rooted and retained, so cleanup
cannot accidentally expose an overridden baseline version. Other-owner records
use the existing unrelated-data frame.

`CleanupReverseNeed` transports need backwards using those observations and
record origins. A record origin provides its actual earlier lookup and equality
of the earlier projected content. Origins are proved from the concrete shared
database transactions, including actual deletion and projection; they are not
new promises supplied by an operation handler.

The registration premise is internal to the reverse-need lemma. The top-level
completion theorem has no extra registration assumption: if the family was not
registered, unchanged metadata precludes newly registered need, and the existing
rootless-component theorem rules out needed family-index records.

## Full outcome

The resulting certificate contains every existing `Complete` field:

- Historical safety for unrelated data, metadata, required content and protection.
- Unique final identities.
- Exact canonical projected content for originally needed captured records.
- Exact preservation outside the fixed capture.
- Absence of every originally unneeded captured family-index record.
- Evidence that each final identity existed in the original store.

Canonical alignment uses a general filter-retention law: filtering a final
canonical view by the earlier visibility mask cannot change it, because cleanup
has not introduced visibility. Combining this fact with the historical content
frame identifies the final stored record with the original canonical projection.

Reclamation uses backwards need transport and stable record ownership/class.
An originally unneeded record cannot acquire permanent need through cleanup.
The final certificate must therefore establish that it is absent.

## Boundary

All new modules use `--safe` and are reachable from `Muninn.agda`. The independent
outcome, eligibility rules, workset, policy matcher and database semantics are
unchanged. The proofs quantify over arbitrary actual traces and admissible
initial worlds; they contain no fixtures or selected-ID cases.

This is the cleanup-only completion-alignment slice, #83, following #80 / #82.
External transitions, database availability, reader release, uncaptured incoming
dependencies, event-driven continuation and eventual recovery remain #84 under
parent #81. No final-state certificate or `NoPending` premise is an eventual
progress proof: a protected or externally blocked pass may still have pending
work and cannot claim completion. No Rust, live cleanup, installation or
deployment changes are included.
