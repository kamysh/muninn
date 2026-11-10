# Eligible text and semantic retrieval

Retrieval uses the actual selected checkout, current stored policy and repository
embedding profile. A result must identify a stored chunk with the same version
as the selected visible file. Retained records from another checkout or older
view are not eligible merely because they remain in the database.

## Complete candidates and coverage

`RetrievalCorpus.Inventory` enumerates every actual eligible chunk/path identity
exactly once. Its completeness obligation quantifies over `SearchView.CodeHit`,
which requires real database lookup and current file-map evidence. An adapter
cannot substitute an already truncated SQL result as this inventory.

Semantic readiness requires an actual completed vector association for that
chunk, text and full current profile. A compatible vector cached elsewhere is
not coverage until the association is published. Usable coordinates retain the
existing positive-dimension, exact-length, finite and nonzero requirements.

The logical coverage report includes every eligible identity. The response uses
a fixed-size summary: total, usable, pending and needing-input counts plus a
complete flag, all tied to that inventory. It does not return an unbounded list
of chunk diagnostics. A general law proves that a complete summary cannot hide
an unfinished member. Text matching has no vector precondition.

## Word matching

The independent `RetrievalText.Engine` represents the actual versioned
PostgreSQL English dictionary and `ts_rank` environment. It is fixed outside
the execution handler. Matching requires a nonempty normalized query and every
remaining query word in the normalized document. Search is not substring
matching. A query containing only discarded words cannot produce a match.

`Fulltext.Candidate` also requires a stored posting for the exact chunk text.
The complete full-text universe requires every eligible chunk's posting and
every matching chunk's measured rank. A non-finite rank cannot silently remove
an otherwise matching chunk. Ranks must equal the actual provider result;
neither handlers nor result adapters may choose replacement scores.

The Agda model does not reproduce PostgreSQL's English dictionaries or parser.
The existing #52 source-adapter obligation must bind `Engine` to actual query
and document analysis and rank observations, including dictionary version.
Until the closed dispatcher and that correspondence are complete, the type
alone does not establish that Rust uses the real provider.

## Storage precision and numerical scores

`RetrievalNumerics.Binary32` describes sign, finite exponent and fraction bits.
`Stored32` requires that the logical coordinates are the exact binary64 widening
of those stored values, including subnormals and signed zero. A merely finite
binary64 vector is insufficient evidence of a valid storage representation.
Query vectors use the same representation and the actual repository profile.

Cosine dot products, norms and division use the stated binary64 operations on
those stored coordinates. Only the final cosine roundoff is clamped to [-1,1].
A positive result must certify the actual calculated score, finite raw
calculation, positive finite returned score and upper bound of one. Every
usable vector in exact mode is classified as a positive match or a finite
nonpositive non-match. There is no silent branch in exact mode that omits a
vector because numerical evaluation was not completed. Approximate mode does
not owe exhaustive scoring; every candidate it does return owes the same
numerical certificate.

The exact rational image of the computed binary64 value is used for comparison;
the specification does not assume real-number algebra for rounded arithmetic.
Ties use immutable chunk identity followed by the path's character order.
The old claim that unconstrained binary64 values simply approximate binary32
storage is replaced by this explicit representation boundary.

This does not prove the external storage codec, PostgreSQL or CPU arithmetic
implementation. The existing #52 correspondence must establish exact widening,
the stated arithmetic sequence and all numerical admission certificates. The
module supplies no postulates claiming those obligations are already discharged.

## Exact and approximate lookup

Exact mode examines the complete matching eligible universe of stored vectors.
It cannot omit a nearer match, must fill available page space, and must avoid
duplicate identities. Exactness refers to stored coordinates and the stated
score calculation; it does not restore precision lost before storage or
guarantee that embedding meaning agrees with a person's intent.

Approximate mode may inspect a subset and can miss nearer matches. Its pool
must still consist of actual eligible matching vectors, with the same exact
score calculation, deterministic ordering, uniqueness and page bound within
that pool. Coverage remains a statement about the whole eligible inventory,
not just the approximate pool. No recall guarantee is invented.

`RetrievalSelection` supplies executable ordering and page construction, with
general membership and size laws. A successful response additionally requires
the explicit `Top` outcome certificate over its proper universe. The present
slice does not claim a general theorem deriving every `Top` field from sorting;
the final operation assembler must supply those obligations rather than accept
a raw list or weaken the goal.

Both modes obey the requested page size and the existing maximum of 1000.
There is no tier filter in eligible matching. Exact completeness and filling
apply to every matching candidate, including vendor code; the vacuous
`Tier2Reachable : Tier → unit` declaration is removed.

## Remaining existing work

Hybrid fusion and vendor weighting remain #40; there is no per-file result quota. Pagination
and saved view lifetimes remain #41. The closed proof-requiring dispatcher,
provider correspondence and implementation harness remain #51–#54. This slice
changes only the authoritative Agda specification and documentation, with no
Rust, SQL, provider, live database, installation or deployment changes.
