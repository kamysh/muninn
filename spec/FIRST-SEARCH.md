# First-search preparation and continuation

A search of a newly discovered worktree keeps its complete query while arranging
the work needed to make that worktree searchable. A pending response is a
continuation of the request. It is not a completed search with an empty result.
Muninn does not call a generative LLM to conduct this dialogue.

## Identify and retain the actual request

`SearchTarget` consumes the existing repository-identification protocol. It
requires actual registration/checkout rows, matching binding IDs/incarnation,
the inspected location and either positive filesystem/Git association or the
existing current-inspection clarification. A path string alone cannot select
a saved view belonging to a replacement clone.

A missing registry binding requests resolution with the complete query still
attached; it does not immediately ask the agent to repeat known context. The
existing `RepositoryRegistry.Family.Add` admits a verified new worktree under
a known family, preserves authorization and supplies the stored row needed by
`SearchTarget`. Relocation uses its existing guarded move operation. Only the
resolver's genuinely missing/uncertain identity evidence takes the generic
clarification dialogue. The final dispatcher must interpret these explicit
resolution actions through that existing registry protocol.

`WorkQueue.SavedSearch` retains the entire typed code or structural request:
mode, text/symbol, location, page, precision and ranking options remain in their
original input record. It also saves the family, checkout and incarnation.
Existing private continuation records carry this data. Their weak checkout ID
reservation cannot pin old code, snapshots or vectors against cleanup.

Resumption matches the saved IDs/incarnation against the newly verified target.
It can follow an established repository move without treating the query's old
path as a new selection. If the scope differs, the original query remains
unchanged and the existing identification dialogue resolves the context. If no
query can be recovered, Muninn asks for the query and worktree again; it adds no
special persistence for a request whose repository was never identified.

## Arrange work without granting permission

`FirstSearch` saves the query and, when necessary and authorized, accepts a
finite `reconcileCheckout` job and its own durable receipt in one transaction.
The read query does not acquire a permanent mutation receipt. Its token and
the arranged job's ID are separate. Existing durable request IDs are not
silently reused for a new query or job.

Family authorization, completed setup, pause/retirement and removal guards
control scheduling. Saving or continuing a query cannot set indexing permission
or clear a pause. An already published eligible view goes directly to retrieval
without scheduling an unnecessary indexing pass. When no view is ready and
indexing is disabled, the saved query explains the required Start/Resume/setup
action and remains resumable.

The constructive transactions preserve existing records and store admissibility.
Atomic-boundary proofs cover every interruption and lost acknowledgement.
Repeating accepted preparation finds the original saved query; it does not
allocate another continuation, queue or receipt.

## Resume toward results

`SearchResumption` rechecks the stored scope and current availability. It reuses
actual runnable checkout work with an active receipt. Work explicitly paused
for this query remains paused. If authorized preparation is still needed and no
matching runnable work exists, resumption can arrange it while retaining the
saved query. Its preservation/retry laws prevent duplicate scheduling.

Once an actual published view appears, the same continuation routes back to
retrieval. A missing view, missing context or unresolved prerequisite never
claims that the query has completed. Result matching, semantic coverage and
ranking remain the existing #39/#40 contracts; pagination and completion of idle
query contexts remain #41. Fair execution of the finite jobs remains #44.

## One selected eligible view

`SearchView` obtains the current selector and its matching snapshot through
actual database lookups. Code candidates are filtered through the selected
checkout's actual content map under its current stored policy and must point to
the same file version as their saved chunk. Symbol candidates additionally
belong to the actual current snapshot and agree on source path/version.
Publication and file-map invariants are required by the retrieval contract.

These are eligibility filters, not a replacement for query matching, semantic
retrieval, ranking or compiler name resolution. Their universally quantified
laws exclude another version's data even when it is still stored for another
checkout or an earlier reader.

## Truthful readiness

`SearchReadiness` distinguishes unavailable, Git-suspended, partial, stale,
observed-current and unverified views. There is no freely supplied `current`
Boolean. A current claim needs equality between the actual selected file map
and an inspected inventory. Stale evidence names a mismatching path. A partial
read problem requires an actual saved file-analysis job in the selected family
and checkout, and the old file must be hidden. The inspected waiting map must
be enumerated completely, so an empty list cannot conceal a known read problem.

The inventory, waiting map and observation stamp are fixed source-inspection
outputs, not desired outcomes selected by an execution handler;
the finite inventory adapter owes their comparison/enumeration certificates.
No inspection means unverified freshness. Git suspension uses the actual saved
checkout flag and retains the completed view. These freshness claims concern
text/symbol publication; vector readiness remains separately explicit.

## Implementation boundary

This changes the authoritative specification and logical stored continuation
payload. Rust, SQL serialization, MCP/CLI adapters and installation are unchanged.
The source-observation adapter, full query executors, scheduler and final closed
dispatcher still owe their existing correspondence obligations. No provider
request or live database change is part of this slice.
