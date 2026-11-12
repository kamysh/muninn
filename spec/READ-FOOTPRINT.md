# Exact search read footprints

Searches retain their saved roots and actual typed references. Sharing a file
version does not make every symbol or staging record attached to that version
part of a search's read footprint.

`ExclusionOutcomes.Protected` derives the dependency scope from the original
stored holder. `readerOrigin` stays fixed through the dependency chain. A search
reader uses `reading`; background holders keep the existing `temporary` scope.
No handler supplies its own weaker scope or protection predicate.

## Actual references, including old saved views

`readingDependency` and `referenceIsReadingDependency` establish both directions
between reading dependencies and actual stored typed references. Reading has
no reverse attachment edge. `requireReference` preserves every actual reference
dependency, and `referenceKeepsOrigin` preserves the original holder's scope.

Reading follows raw references rather than applying today's visibility mask to
an older saved view. An old structural snapshot still holds all members it
actually contains, including members newly excluded by a later policy. Its data
remains protected until that reader releases it.

A new filtered snapshot uses its filtered member list. Reaching a shared file
version through one of those members does not add unrelated symbols from that
version back into the new reader's footprint. Compatible shared content and
background work keep their existing retention semantics.

## Exact classifier and admission

The finite classifier computes separate search and background closures, then
combines them. Soundness, completeness and decidability refer to the same
authoritative `Protected` relation. Search origins cannot acquire worker scope
merely by reaching a worker-owned record.

Admission derives its source-specific scope from the actual stored holder.
Its exact footprint and `Protected` conversion laws agree in both directions.
The existing new-hold fence therefore checks the corrected footprint without
dropping direct or indirect references the new view actually uses.

## Preservation and productive cleanup

The frame, actual-trace and finished-reader-release laws preserve holder origins
as well as protected records. Other holders' dependencies survive release;
release and cleanup create no new protection. The productive pass still reaches
the existing full cleanup outcome once pending use has ended. Saved task IDs,
receipt isolation and unrelated records remain governed by the existing laws.

This is #102 under #84, implementing the user's explicit search-retention
correction. The safe modules remain in the aggregate. Producing fresh canonical
views, completing/removing task bookkeeping, admitting background work and
assembling the full lifecycle remain integration obligations under the parent.
This slice changes Agda and documentation, not Rust or the running installation.
