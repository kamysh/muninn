# Snapshot filtering across publication writes

`PublicationVisibility` proves that changing publication bookkeeping does not
change the filtering rules for a given snapshot. Updating the current selector
still changes which snapshot a new search chooses; this law concerns the
contents selected from that snapshot.

## Derive the observations from actual writes

`Quiet` identifies actual structural-snapshot, published-selector, receipt and private-reader
records. Those bodies do not supply registration, checkout, file-binding,
symbol or edge query facts. It is not a caller-provided unchanged-visibility
predicate.

The generic store laws quantify over arbitrary worlds, keys and observations.
They use the existing unique-store condition and actual old-record lookup to
prove that replacing an ignored record cannot remove or create a query hit.
No per-operation atomic relation or selected fixture is introduced.

`Model.Write` applies those laws to replacement writes; `Model.Insert` covers
fresh insertion. They share the observation-congruence proof and derive,
in dependency order:

- Family registration and checkout observations.
- Delta selection and file-version bindings.
- Symbol visibility and edge visibility.
- Equality of the independent snapshot projection before and after the write.

The policy input remains fixed. Selection changes themselves have their own
operation requirements.

## Canonicality survives the remaining publication writes

`projectSame` proves equal filtering for every record value.
`canonicalPersists` then proves that a value canonical before the metadata
write remains canonical afterward. The publication operation can apply it to
selector replacement and receipt advancement after preparing its filtered copy.

The binding, symbol and edge definitions expose their existing pure input
facts. Their entrypoints still compute those facts from the actual world;
selection semantics and data dependencies are unchanged.

## Boundary

This is #114 under #84, following #108 / #109, #110 / #111 and #112 / #113.
The safe module is imported by the aggregate. Complete receipt-sealed
preparation/replacement composition and reader resumption remain subsequent
work; this law does not claim that lifecycle is finished.

These are specification laws. Rust correspondence, live data, binaries,
installation and deployment are unchanged.
