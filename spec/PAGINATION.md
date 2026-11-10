# Stable search pagination

The first response returns a bounded page (10 results by default, at most
1000 per response). Further pages have no total-result or per-file quota.
They reuse the saved query, checkout incarnation, policy revision, published
source view, embedding profile, dictionary and ranking version.

Exact retrieval saves its complete ranked matching set. Approximate retrieval
saves its current ranked candidate union and the still-unexamined identities
from the complete source inventory. Exhausting one retrieval batch is not the
end of the search. Further batches append newly discovered matches in the same
view. They may contain stronger matches; earlier pages are never reshuffled.

## State and transitions

`PaginationData` gives private continuation payloads a typed query plan and page
token. A plan contains immutable query/view context, known result identities
and exact score ratios, a finite pending source workset, the cached binary32
query vector, and a checkpoint revision. It stores no copies of indexed code.
A token identifies an offset and, once served, the exact page interval and
successor token. The predecessor's recorded end is the successor's start.

`PaginationRanking` constructs code plans from actual `Retrieval` and
`HybridRanking` outcomes. It retains the whole ordered pool rather than storing
only the first response page. Semantic references identify actual vector
associations. All unseen inventory identities remain in approximate pending
work. `HybridRanking.Pools` reuses the same fusion calculation for later pools;
the initial `Legs` contract retains its original selection guarantees.

`PaginationTraversal` classifies each examined source identity as a match or
requires evidence that it does not match the independent query outcome. An
omitted matching identity is therefore not an admissible classification.
`PaginationAdvance` accepts only positive, bounded progress through the fixed
pending workset, fresh result identities and a unique batch. Each committed
batch strictly decreases pending work and appends to the previous results.
Retrying an older checkpoint revision does not perform its batch again.
Provider preparation can remain pending; it does not consume an arbitrary
retry allowance or silently mark the query complete.

`PaginationCommit` captures a plan/token atomically. A page call reads actual
stored continuations in one shared database transaction, validates the source,
and records the page and its successor together. A served token is replayed
before preparing any further batch. Reusing it with a different page size
receives an explanation. An unserved token cannot produce an empty page while
source work remains. A response can omit the successor only after the known
result interval and all pending work are consumed.

## Availability and ownership

`PaginationCodeCall` supplies the concrete checkout eligibility check. It uses
actual registration/checkout records and incarnation, current policy, the saved
structural root, visible file versions, actual chunk/symbol/vector rows and edge
endpoints. A changed policy, retired checkout, removed source row, hidden file
or unavailable saved view leads to the existing conversation to resume the
saved query in a new view. It does not return excluded content. Missing cursor
context first reuses the surrounding conversation; the agent is asked for the
query/repository only when that information is unavailable.

Continuations contain weak record identities only. They create no strong data
references or active-reader rows. An active page uses the database transaction
snapshot; no index hold remains between calls. The physical SQL adapter must
implement that coherent transaction snapshot, rather than combining unrelated
READ COMMITTED statement snapshots.

## General laws and implementation boundary

The safe modules prove bounded pages, no skipped successor interval, immutable
recorded-page replay, query/view/prefix preservation, strict finite source
progress, retention of unseen candidates, actual source ownership/visibility,
private cursor insertion/replacement admissibility, preservation of non-cursor
rows, and all-or-nothing interruption boundaries for page/checkpoint calls.
They do not claim that a provider outage is finite without eventual service.

These are authoritative Agda contracts; this PR does not change Rust. The
existing final-dispatch, source-adapter and harness issues still owe the closed
operation assembly, concrete match classifiers, database snapshot binding and
implementation correspondence. Structural and family-note outcome adapters
reuse this cursor protocol in their existing issues; no dummy checkout is
introduced for notes. General sorting/selection obligations already assigned
to final assembly are not claimed as completed here.
