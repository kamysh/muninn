# Structural readers use the actual current view

`CurrentReader` reads the stored checkout selector inside the transaction that
admits a structural search. It checks the family registration, live checkout,
selector owner and checkout identity. It does not take a caller-selected snapshot
as the current view.

The saved reader references the selected structural snapshot. It never holds
the mutable selector. `currentSound` reconstructs the actual published record
from a successful selection; current-view validity then supplies the snapshot's
existence, owner and checkout agreement.

## Admission and preservation

The selected reference passes through the existing exact-footprint admission
guard and automatic incarnation allocation. Selection and admission share one
transaction snapshot. The general laws preserve all existing rows, saved reader
use, cleanup captures, receipts, store admissibility and current-view validity.
If context or a current view is still being arranged, the original continuation
receives the unchanged store. Pending cleanup keeps the existing admission fence.

`PublicationVisibility.Insert` derives unchanged file-binding, symbol and edge
observations from the actual fresh private-reader insertion. Its observation
congruence is shared with the existing replacement proof. This proves that an
already canonical snapshot stays canonical in the proposed reader world, rather
than assuming that proposal is clean.

## Productive resumption

`AfterCleanup` uses the existing executable family cleanup pass and its actual
trace. It derives current-view validity after cleanup, the selected snapshot's
lasting need, its membership in the fixed capture and its canonicality at rest.
Those facts construct the resolving, clean current-root proposal. The completed
cleanup pass clears the admission fence, so `finishes` executes admission.

The agreed release-of-pending-use condition and an existing live published view
remain explicit. A context continuation or pending cleanup is not described as
completed search work. Constructing a first view and coordinating external
holder lifecycles remain obligations of the assembled protocol.

## Boundary

This is #118 under #84. It covers structural-view root construction and
admission, not query-specific text/vector footprints, pagination, the complete
reader lifecycle, stored-policy supersession or the final closed dispatcher.

Agda and documentation only. Rust correspondence, live data, installed binaries,
system configuration and deployment are unchanged.
