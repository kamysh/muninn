# Structural search candidates

Structural search returns name-based relationship candidates, not guarantees
that a compiler would resolve a call or import to a particular definition.
When the same name has multiple eligible definitions, every matching candidate
is retained. Each result includes the two symbols and their source paths,
positions, and relationship evidence; agents may narrow the query.

The catalog keeps structural content opaque; the search boundary binds the
requested symbol and relation direction for the selected checkout.

`StructuralSearch` defines this outcome over one actual published checkout
view. The selected structural snapshot fixes the nodes and edges the results
must belong to. Both endpoint symbols must be present in that view and visible
under the current family policy: a stored symbol row whose source path matches
the selected visible file map at the same version. The relationship must be an
actual family-owned edge in that same view, with its stored relation decoded
to the requested kind and the appropriate endpoint matching the requested
name. Incoming relations are callers and inheritors; the other relations
follow outgoing edges. Payload decoding is fixed by the source adapter for the
stored parser/representation version.

The result order is related-symbol path, source position, then edge identity.
It retains every candidate rather than selecting one definition or applying a
per-file limit. The common pagination contract bounds each response page.
Its total result universe and source payload decoder are independent of the
execution script and must be supplied by the source adapter.

The contract is logical: both the primary AGE graph and a linked checkout's
stored snapshot must supply evidence for the same selected-view result. It
does not require a second physical graph. The current Rust search returns only
the related symbols; binding its payload decoding, source evidence, completeness,
pagination, and ambiguity guidance to this contract remains part of the
existing implementation-correspondence and dispatcher work.
