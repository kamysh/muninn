# Independent exclusion outcomes

`Muninn.ExclusionOutcomes` defines the cleanup-core contract over the complete
`Muninn.OwnedState.World`. No smaller artifact store or deletion script defines
its goal. The closed role classifier covers every owned body constructor.

## Policy and current use

A rule names one resolved family and its ordered effective exclusion rules,
including stored defaults. The policy matcher is installed once by the shared
selection model (#26), rather than supplied by a cleanup handler. Rule parsing
is not implemented in this slice.

The new-search mask depends on family and path, not checkout scheduling flags.
General laws establish agreement across checkouts and exclusion from new search
visibility. Paused and Git-suspended checkouts use the same mask and remain
potential sources of shared data; retirement is a distinct typed observation.

Owned metadata now exposes registry retirement/legacy-read use, checkout
retirement/pause/Git status, legacy source paths, structural symbol source paths
and graph-resource checkout scope/current read use. These describe actual
published read state; they are not configurable retention preferences. The
registry/publication adapters must establish them from the authoritative state.
This logical refinement adds no SQL columns or runtime migration.

Legacy data is rooted only while the legacy read path is in use. Graph resources
are rooted only while currently used by a live scope. A repository's mere
existence cannot keep an inactive old graph representation alive.

## Lasting need and temporary protection

Need is the least closure of explicit roots and the fixed dependency relation:
current included bindings, current snapshots/resources, metadata and unrelated
owners. Referenced records must resolve to the expected kind/owner. Shared
analysis footprint propagates between a live version and its chunks, postings,
vectors and eligible path-specific symbols. Snapshot edges retain their valid
endpoint symbols. Staging is temporary rather than a permanent cache root.

A general induction proves that a rootless, incoming-closed component cannot
justify retaining itself, including through cycles. A script cannot replace
this need relation with a weaker keeper predicate.

Active readers and accepted work contribute separate temporary protection.
Their references and dependent footprint remain intact while in use, but are
not promoted to permanent search roots. An operation cannot report completion
while a captured, permanently unneeded record is retained only by such a lease.

A structural snapshot may contain included and excluded members together.
Its independent projection preserves the header/ownership and eligible members
while filtering excluded nodes and edges. Soundness, completeness and
idempotence laws govern that filtering. Keeping the header does not make all
its old members needed.

## Capture, safety and completion

The canonical capture scans all family-owned records directly, without relying
on a registry or parent pointer. Its quantified coverage proof prevents leftover
rows from disappearing because a pointer was deleted. `Intent` requires that
coverage and unique accepted incarnation identities; callers cannot substitute
an incomplete workset.

Accepted capture and current assessment are distinct worlds. Original IDs stay
fixed while need/protection are evaluated against the current snapshot. Rows
created later remain outside this task; publication must separately prevent
new excluded content from entering the index.

Safety preserves unrelated data, metadata, still-needed projected content and
every temporarily protected record. It is reflexive, so it holds before the
first step and while waiting. Intermediate snapshots may retain old members,
but cannot add members or lose required ones.

Completion additionally requires exact projection for captured needed records,
absence of captured unneeded indexed records, unchanged uncaptured rows, unique
remaining identities and no invented records. It is a predicate on actual owned
rows, not a status flag. Search hiding or saving a policy is insufficient.

## Remaining work

#69 supplies exact finite need/protection classification; #70 must implement
and prove cleanup convergence against this fixed contract under #67.
#23 remains open for outcome/core integration. Policy acceptance/supersession
and the evolving worker are #24/#25; they must compose permitted metadata
transitions with the cleanup-core frame and release obsolete work protections.

Raw selection semantics, analysis validity, publication/read-state consistency,
structural retrieval and implementation projection remain their respective
contracts (#26/#29/#30/#42/#46/#51/#52). The present theorems do not establish
Rust/SQL correspondence or live database cleanup. No Rust, worker, service,
installation or deployment changes are included.
