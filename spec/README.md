# Formal specification and implementation boundary

`Muninn.agda` is the aggregate entry point. These modules state mathematical
contracts for chunks, policies, registration, checkout views and indexing. They
are not generated Rust and do not constitute a refinement proof of the running
application. [Development](../docs/development.md) describes the current 1.1
implementation; historical proposal/status records remain under `docs/plans/`.

## Current implementation in brief

The application uses one schema per family, managed through the Kryzhen library,
an AGE graph for the primary checkout, and transactional structural snapshots
for linked worktrees. File versions/chunks are shared through a moving base and
relational file deltas. Main updates preserve
other published checkout views. There are no custom physical prefix/radix trees.

Family policies/default histories are in the database. A TUI and guarded JSON
interface provide configuration and metadata preflight, with explicit first start.
Enabled families discover worktrees automatically. Incomplete merge/rebase or
conflicted Git state retains the last completed index until reconciliation can
publish again.

Those runtime statements are established by code and implementation verification,
not solely by the model's type check.

## General laws represented

| Modules | Scope |
| --- | --- |
| `Worktree`, `GenericFileMap`, `FileMap`, `ContentViews`, `ContentPublication` | File-map algebra, actual owned-row projections, fixed publication outcomes and atomic receipt-sealed retry |
| `Schema`, `Storage` | Application/graph roles, readiness evidence, family isolation and abstract publication/reference lifetimes |
| `GraphMembership` | Selected-view symbol/edge membership and endpoint visibility; no compiler name-resolution proof |
| `Config`, `Policy`, `Registration` | Bootstrap/policy separation, frozen defaults, revision guards, registration intent/retry and authorization preservation |
| `IndexFsm`, `Index`, `Cli` | First-start and subsequent-work gates, retained views during blocked Git operations and abstract command intents |
| `Types`, `Embeddings`, `Search`, `Knowledge` | Chunk/vector validity, search bounds/ranking and knowledge-scoping contracts |
| `AdvisoryLock`, `Concurrency` | Index exclusion/preemption and watcher coordination contracts |

`FileMap.movingBasePreservesWorktree` and `movingBaseKeepsMinimalDelta` state
representation laws. Functional maps and retained baseline abstractions are
mathematical models; they do not require physical persistent trees or copying
unchanged chunks. A predicate requiring isolated assignments does not prove that
a particular live SQL registry satisfies it.

## Known model/runtime gaps

These are unresolved correspondence obligations, not authorization to weaken the
model or silently change the application during a documentation edit:

| Area | Model | Current runtime |
| --- | --- | --- |
| Graph ownership | `Storage.SchemaAssignment` maps a family to a `SchemaPair`; `sameFamilySameSchemaPair` covers both roles | Application schema is family-owned; Git checkout graphs are separate AGE namespaces |
| Curated knowledge | Notes belong to a repository family, optionally restricted to one worktree, and use the family embedding profile | `public.knowledge` and MCP knowledge tools use exact repository-path strings; runtime migration and correspondence must preserve existing notes while resolving family/worktree identity |
| Freshness | `Search` models response freshness/suspension | MCP code-search responses contain result lists without that metadata |
| Removal | `RepositoryRemoval` specifies actual family unregistration and the approved forget-all intent; reindex remains rebuilding | `remove PATH` deletes code data/registration and family-local settings; public notes remain. Complete durable removal/forget dialogue and receipts are not implemented |

Other abstract fields/constructors should be traced to their concrete runtime
representation before asserting equivalence. Passing a type check does not close
these gaps. The current model still contains terminology from earlier baseline
and schema-pair designs; do not treat historical physical-layout suggestions as
current implementation instructions.

## What the proofs do not establish

The model does not prove the correctness of Git discovery, filesystem reads,
canonical-path conversion, JSON/glob parsing, SQL migrations, transaction drivers,
AGE APIs or the Rust implementation. AGE readiness and graph ownership require
runtime verification against actual catalog state. A filesystem watcher and a
quiet interval do not provide an atomic snapshot against arbitrary external writers.

SQL storage sharing, garbage collection, HNSW recall, name-based relationship
resolution and performance at 100 worktrees require implementation analysis and
measurement. Integration tests exercise concrete scenarios; they are distinct
from universally quantified Agda laws.

## Checking and changing the model

From the source root, final aggregate verification is:

```sh
nix develop --command sh -c 'cd spec && agda Muninn.agda'
```

Use a persistent `agda --interaction-json` process in the project environment for
proof development, then check the aggregate. Preserve general quantified laws
and the existing safe options. `Muninn.Float` retains its primitive Float boundary.
Do not add a postulate, weaken a guard or substitute a concrete example simply
to make a proof pass. A behavior or architecture change needs explicit agreement;
an implementation discrepancy is evidence to investigate, not permission to
rewrite the specification to fit it.

## Shared database effect semantics

`Muninn.Database` defines one finite-store meaning of reads, scans, writes,
deletions, bounded predicate deletion, commit and rollback. Transaction reads
observe tentative writes; abort discards the complete tentative state. Only a
completed transaction publishes a new store.

Its general laws establish deletion absence, preservation of other keys,
visible writes, complete rollback, retention under selection and strict size
decrease when a deletable record exists. The deletion bound counts deleted
records rather than examined records, so a retained prefix cannot prevent
progress.

This is the common effect foundation for the authoritative specification. It
is not yet connected to every product operation, and it is not a proof that
Rust, SQL or AGE effects implement these semantics. Closed operation dispatch,
complete persistent-state coverage and implementation correspondence remain
explicit obligations of the specification series.

## Shared recovery contracts

`Muninn.Recovery` uses the fixed database transaction semantics to define scripts,
all committed prefixes, interruption and completion. Its general laws characterize
the first atomic boundary, unchanged worlds after returning a result, and prefix
composition. Tentative statement effects are never published before commit.

The `Recoverable` interface requires preservation at every committed prefix, interruption/retry convergence
and constructive termination proofs. The outcome and preservation relation are
interface parameters fixed by the caller; an operation cannot supply weaker ones
as record fields. This is a specification interface, not a runtime change or the
completed closed dispatcher. Catalog integration remains a separate obligation.

These are local execution laws once a transaction can execute against the given
world. Database outages and waiting for external input belong in the application
protocol; this interface alone does not establish eventual service availability.

## Complete owned-state inventory

`Muninn.OwnedState` represents each owned record category, including pending
work and control state, with explicit owner placement, unique identities and
typed strong references. It proves preservation of other owners and of whole
world admissibility when removing an unreferenced record.

See [the source inventory and model boundary](OWNED-STATE.md) for every current
storage category, agreed state still absent from Rust, weak-reference semantics
and remaining operation-specific obligations. This is an ownership/reference
foundation, not the completed product state machine or a runtime cleanup fix.

## Closed operation and adapter catalog

`Muninn.CatalogInputs`, `Muninn.Catalog` and `Muninn.CatalogSources` give shared
semantic input types, separate finite background jobs, closed current MCP names,
local UI/control inputs, exhaustive outcome ownership and source assignments.
General laws establish wire-name round trips, exclusion of unknown names from
the current tool set and transport-independent outcome ownership.

See [the operation source inventory and coverage boundary](OPERATION-SOURCES.md).
This catalog has no raw-script request constructor or execution dispatcher.
Individual outcome/progress proofs, corrected input admission and Rust coverage
remain required before the final proof-requiring dispatcher can be installed.

## Generic corrective dialogue

`Muninn.Dialogue` defines context reuse, batched corrections, actionable guidance,
explicit alternatives and certified admission/completion around the closed
catalog. General laws preserve known facts and work, keep dialogue effects out
of the persistent world and rule out consecutive internal assessment steps.
See [the dialogue contract and integration boundary](DIALOGUE.md). Missing context
uses the same restatement dialogue regardless of why it became unavailable;
this adds no special persistence for unidentified repositories.

## Normalized mutation and job identity

`Muninn.Canonical`, `Muninn.RequestCodecs` and `Muninn.RequestIdentity`
compare complete typed inputs, with record reconstruction proofs, exhaustive
constructor coverage and transport-independent meaning. Ordered rules and all
actual field values remain significant. See [the identity contract and adapter
boundary](REQUEST-IDENTITY.md). The receipt/admission integration is described
below; these formal modules add no runtime persistence behavior.

## Durable request receipts

`Muninn.ReceiptTypes` and `Muninn.ReceiptLedger` refine receipt state in the
existing owned world. Acceptance, checkpoint commits, replay and ID-only
retention use the shared database semantics, with mandatory receipt-isolation
proofs for business effects. See [the state machine and integration
boundary](RECEIPTS.md). Operation outcomes, physical adapters and worker
progress remain separate obligations; no runtime persistence is added.

## Identity-aware corrective admission

`Muninn.IdentityDialogue` and `Muninn.RequestAdmission` bind context recovery,
normalized identity and receipt-first replay to the generic dialogue model. The
transaction-bound gate requires identity/prerequisite certificates and preserves
accepted work while asking for clarification. Completion answers require both
the independent outcome and a durable receipt. See [the integration contract and
remaining adapter/dispatcher obligations](IDENTITY-ADMISSION.md).

## Independent exclusion outcomes

`Muninn.ExclusionOutcomes` derives need and temporary protection from every
owned record category and defines complete-world capture, safety and completion
contracts. Mixed snapshots are projected without retaining excluded members;
rootless components cannot justify their own retention. See [the outcome model
and cleanup-core boundary](EXCLUSION-OUTCOMES.md). Cleanup convergence is #67;
no runtime cleanup is implemented here.

## Finite exclusion classification

`Muninn.FiniteClosure` and `Muninn.ExclusionClassifier` construct exact decisions
for lasting need and temporary protection in the complete owned world. Their
size decrease and saturation proofs handle cyclic dependencies without arbitrary
cutoffs. See [the classifier and remaining cleanup boundary](EXCLUSION-CLASSIFICATION.md).
No deletion effects or runtime cleanup are implemented by this slice.

## Bounded cleanup effects

`Muninn.CleanupStorage` and `Muninn.CleanupEffects` prove complete-world safety,
reference/identity preservation and actual committed deletion/projection effects
for current-snapshot cleanup. Their mutation bound is indexed by the database
transaction itself. See [the transaction contract and convergence boundary](CLEANUP-EFFECTS.md).
Progress and retry convergence remain #73 under #70; no runtime cleanup is added.

## Finite active cleanup passes

`Muninn.CleanupProgress` proves strict decrease of actual deletion/projection
effects, bounded arbitrary mutating traces and a total current-world cleanup
pass. Repeating a stopped pass without state changes performs no edits. See
[the progress kernel and completion boundary](CLEANUP-PROGRESS.md). Worker
integration remains unfinished under #84.

## Cleanup completion and constructive progress

`Muninn.CleanupCompletion` constructs the existing completion certificate when
no requested cleanup remains. `CleanupOrder` and `closedComponentProgress` prove
that a closed, nonempty group of unneeded, unprotected records contains an
actual eligible deletion. Diagnostic-only stopped-state classifications have
been removed. See [completion and constructive progress](CLEANUP-COMPLETION.md).
The runtime worker and its integration remain unfinished under #84.

## Historical cleanup preservation

`Muninn.CleanupHistory` derives the existing original-to-final safety contract
for actual cleanup traces and resumed passes from admissible stores. It proves
need/protection persistence and composes projected snapshot content. See [the
historical frame and external-recovery boundary](CLEANUP-HISTORY.md). External
transitions and full eventual recovery remain #81 under #77.

## Original-request cleanup completion

`CleanupAlignment` derives the full existing `ExclusionOutcomes.Complete`
contract for the original world from actual cleanup traces and the final
observed completion certificate. `CleanupReverseViews` and `CleanupReverseNeed`
rule out new visibility and permanent need introduced by cleanup. The executable
pass and resumed-pass corollaries preserve the fixed captured identities.
See [completion alignment](CLEANUP-ALIGNMENT.md) for the proof and external-recovery
boundary. These are formal laws, not runtime cleanup implementation.

## Executable cleanup completion

`CleanupLoop.Run.finishes` proves that the executable deletion/projection pass
reaches the existing full completion contract after pending use is released.
`CleanupReleased` proves that actual edits preserve this condition. Bounded
follow-up captures cover newer blocking records and preserve the original task
record and captured IDs. See [executable cleanup completion](CLEANUP-LOOP.md).
Admission and scheduling integration remain #84; this is not a runtime cleanup fix.

## Reader admission during cleanup

`CleanupAdmission` checks canonical roots and the proposed new reader's exact
footprint against all saved cleanup worksets in one shared transaction. It
prevents new direct or indirect holds on pending records while preserving
existing holders, task IDs and receipts. Proposals that still touch pending
data take the existing current-view replanning continuation without writing a reader. See
[reader admission](CLEANUP-ADMISSION.md). View production and lifecycle/scheduling
integration remain #84.

## Reader resumption after cleanup

`CleanupResumption` derives the admission guard from the completed fresh family
cleanup pass, then executes the existing reader transaction for the original
request. Its shared script has a constructive completion proof and preserves
saved task worksets. See [reader resumption](CLEANUP-RESUMPTION.md). Canonical
view production, holder lifecycle and scheduling remain under #84.

## Releasing completed readers

`ReaderRelease` removes a completed search’s private reader record atomically,
preserves indexed records and other holders, and proves retry idempotence.
`ReaderReleaseCleanup` executes release followed by productive cleanup and
proves the full cleanup outcome when other pending use has ended. The shared
store and admission enforce private reader identities. See [reader release](READER-RELEASE.md).
Lifecycle scheduling and current-view production remain under #84.

## Durable follow-up cleanup capture

`CleanupScheduling` commits a fixed follow-up workset and its existing receipt
checkpoint atomically. It preserves original tasks, derives the worker intent
from the persisted IDs, and proves old-checkpoint retries do not recapture.
See [durable follow-up capture](CLEANUP-SCHEDULING.md). Full lifecycle scheduling,
current-view production and policy integration remain under #84.

## Fresh tracked record incarnations

`RecordAllocation` constructs an incarnation outside the complete row/weak-ID
reservation set and uses it inside the shared reader and task transactions.
The existing admission guards, durable captures and receipt retry guarantees
remain. See [record allocation](RECORD-ALLOCATION.md). Current-view production
and lifecycle integration remain under #84.

## Database access and request resumption

`DatabaseResumption` keeps known conversations responsive without a database
transaction while access is unavailable, then resumes or replays actual saved
work through the current shared receipt. It preserves context and bootstrap
credentials across connection observations. See [database resumption](DATABASE-RESUMPTION.md).
Initial bootstrap, migrations and full runtime integration remain under #46.

## Exact search read footprints

`Protected` derives its dependency scope from the stored holder origin. Search
readers follow their saved-view references; background work keeps its existing
attachment scope. The exact classifier, admission guard, cleanup preservation
and reader-release proofs use that same rule. See [search footprints](READ-FOOTPRINT.md).
Fresh-view production and full lifecycle integration remain under #84.

## Private execution bookkeeping

The shared admissibility invariant now prevents strong references to readers,
cleanup tasks, accepted work, continuations and receipts. Admission checks the
same predicate; private records' no-incoming-reference guard is derived.
Cleanup captures carry the same typed request ID as their accepting receipt.
See [private bookkeeping](PRIVATE-BOOKKEEPING.md). Verified task removal and
the full lifecycle remain under #84.

## Verified cleanup-task completion

`CleanupFinalization` checks the actual saved workset, then removes its private
task and updates its existing receipt atomically. The original request stays
active while sibling tasks remain and finishes only after its last task.
Productive cleanup constructs readiness; unresolved work keeps the whole store
and continues the conversation. Retry, indexed-data preservation and
compact-marker retention are proved.
See [task completion](CLEANUP-FINALIZATION.md). Policy selection, fresh-view
production and full lifecycle scheduling remain under #84.

## Current published views

`PublishedViews` distinguishes the checkout's current published structural
view from older retained snapshots. Publication references provide permanent
reachability; a stored snapshot is not itself a root. The model states uniqueness
and checkout agreement, and preserves cleanup/history laws with the corrected
references. See [current views](CURRENT-VIEWS.md). Fresh-view construction,
publication and closed-catalog enforcement remain under #84.

## Filtered snapshot preparation

`SnapshotPreparation` reads an actual source snapshot, allocates inside the
transaction and inserts its independently specified filtered copy before
invoking the publication continuation. The copy is canonical in the resulting
store; original records, receipts and current-view invariants are preserved.
See [snapshot preparation](SNAPSHOT-PREPARATION.md). Association replacement,
receipt sealing and full lifecycle assembly remain under #84.

## Current-view selector replacement

`ViewReplacement` guards the actual current association and target checkout,
then replaces only that private selector. Shared admission prevents selector
holds; existing snapshot data, receipts and current-view invariants survive.
Unresolved contexts roll back through the existing continuation.
See [selector replacement](VIEW-REPLACEMENT.md). Complete publication
composition, canonicality and receipt replay remain under #84.

## Canonicality across publication writes

`PublicationVisibility` derives unchanged binding, symbol and edge observations
from actual snapshot/selector/receipt writes and proves canonical filtering
persists. The policy input stays fixed; the entrypoints still compute query
facts from the actual world. See [publication filtering](PUBLICATION-VISIBILITY.md).
Receipt-sealed publication composition and reader resumption remain under #84.

## Atomic current-view publication

`ViewPublication` commits the filtered snapshot, current selector and original
request checkpoint together. It derives canonicality after the actual writes,
preserves saved data/readers/worksets and proves interrupted retry convergence
without repeating allocation. See [view publication](VIEW-PUBLICATION.md).
Stored-policy selection, new-reader construction and full lifecycle assembly
remain under #84.

## Structural readers from the current view

`CurrentReader` selects the actual stored current snapshot and admits its saved
reader in one transaction. It preserves old rows/readers/worksets and derives
successful admission after the existing productive cleanup pass, including
canonicality under the new reader insertion. See [current readers](CURRENT-READER.md).
Query-specific footprints and full lifecycle assembly remain under #84.

## Current stored policy selection

`StoredPolicy` resolves typed policy-version contents and frozen defaults through
the actual current pointer. It constructs the effective rule inside the shared
transaction and redirects stale version/revision continuations to the current
rule. Resolution completeness and deterministic policy selection are proved.
See [stored policy](STORED-POLICY.md). Rule parsing, atomic policy acceptance,
history/supersession and full lifecycle integration remain separate obligations.

## Cleanup effects under current stored policy

`PolicyCleanupBatch` resolves policy and verifies the actual saved task before
executing the existing bounded deletion/projection effect in the same transaction.
It keeps the original capture, derives productive progress and preserves receipts,
protected data, stored policy and current-view invariants. See
[current-policy cleanup batches](POLICY-CLEANUP-BATCH.md). Complete acceptance,
supersession reporting and lifecycle scheduling remain under #84/#25.

## Total glob matching

`GlobMatching` gives explicit syntax-tree languages and a total match decision
through complete finite path splits. Its computed Boolean is sound and complete
for the independent relation; ordinary wildcards/classes cannot consume path
separators. See [glob matching](GLOB-MATCHING.md). Raw parsing, rule precedence,
ignored-parent traversal and selection integration remain under #26.

## Certified glob class scanning

`GlobLexing` scans escaped units and bracketed classes with actual source-grammar
evidence. Recognition completeness, deterministic meaning, source reconstruction
and strict suffix progress are proved for arbitrary input. See
[glob class scanning](GLOB-LEXING.md). Range interpretation, complete raw parsing
and selection integration remain under #26.

## Certified class-range interpretation

`GlobRanges` turns actual scanned class units into ordered singleton/range
meaning and constructs the matching atom from both source certificates.
Recognition completeness, deterministic atom/suffix meaning and inherited
source progress are proved. See [class ranges](GLOB-RANGES.md). The complete
selection integration is described in [Git authority](SELECTION-INTEGRATION.md).

## Certified raw glob tokens

`GlobTokens` assigns source-certified token meanings, including position-sensitive
recursive wildcards and compiled classes. Recognition, determinism, exact source
consumption and strict suffix progress are proved. See [raw glob tokens](GLOB-TOKENS.md).
Whole-body assembly and selection integration use these tokens; see
[Git authority](SELECTION-INTEGRATION.md).

## Complete raw glob-body parsing

`GlobBody` supplies actual position/group context and assembles certified tokens
into complete matcher trees. General laws prove full recognition, unique meaning,
a source-length transition bound and raw-pattern match soundness/completeness.
See [complete glob bodies](GLOB-BODY.md). Rule framing and policy integration are connected through
[Git authority](SELECTION-INTEGRATION.md).

## Source-certified rule framing and scope

`RulePatterns` compiles actual negation/root/directory framing around certified
bodies; `RuleScope` decides scoped and ancestor matching through complete finite
path splits. General laws prove recognition, unique compiled meaning and sound/
complete matching. See [rule framing and scope](RULE-PATTERNS.md). Entry admission,
Git precedence and traversal are connected through [Git authority](SELECTION-INTEGRATION.md).

## Ordered selection from compiled rules

`OrderedSelection` compiles complete ordered lists and resolves actual certified
matches from the Git default through frozen-default and family overrides. General
laws establish matching-tail precedence, unmatched preservation, deterministic
family decisions and vendor isolation. See [ordered selection](ORDERED-SELECTION.md).
Entry/Git admission and indexing/search/cleanup share the concrete
[selection integration](SELECTION-INTEGRATION.md).

## Strict policy admission and family selection

`StrictGlob` and `PolicyRuleAdmission` validate complete original-input policy
entries and lists, preserving quoted literals and the strict class requirement.
`AdmittedSelection` connects those certificates to normalized effective family
rules and deterministic selection. See [policy admission](POLICY-RULE-ADMISSION.md).
Git supplies batched defaults; traversal and stored-policy integration are
described in [Git authority](SELECTION-INTEGRATION.md).

## Exact file and structural limits

`FileLimits` decides admission from actual raw bytes with inclusive bounds.
`IndexFileLimits` schedules every ready selected file while preserving actionable
size questions and explicit text-only coverage. Captured family defaults and
normalized request identity include both caps. See [file limits](FILE-LIMITS.md).

## Mandatory completed-work reuse

`ArtifactIdentity`, `CanonicalChunks`, `CompletedWork` and `ArtifactReuse` bind
exact versioned inputs and byte spans to certified immutable checkpoints.
Completed hits cannot choose recomputation; explicit recreation isolates its
requested family. See [artifact reuse](ARTIFACT-REUSE.md).

## Fixed content and structural publication outcomes

`ContentViews` reads logical file versions and saved Git defaults from actual
owned base/delta rows. `ContentPublication` calculates the selected checkout
result and other-checkout preservation under the policy read from stored state.
The shared transaction interface requires proofs of exact representation,
structural publication, retained data/readers, family isolation and durable
cleanup capture. Receipt sealing keeps the original request active.

See [publication intent and refinement boundary](CONTENT-PUBLICATION.md).
The universally quantified map and atomic retry laws are proved. Constructing
and certifying the Rust storage transaction, and requiring this interface in
the closed dispatcher, remain the separate correspondence/catalog obligations.
A proof-carrying storage interface is not itself a verified SQL implementation.

## Unreadable files and Git suspension

`CheckoutReconciliation` is the total per-file publication state machine.
Unreadable files lose both text and structural visibility and retain actionable
read work. Other indexed paths advance without a premise about their peers.
Operating/conflicted Git state ignores new candidates and retains the whole
previous view, filtered by current family policy; an absent initial view stays
absent. See [the transition laws and adapter boundary](CHECKOUT-RECONCILIATION.md).
The public `Index.FileReconciliation` module exposes this contract alongside
existing authorization, schema and dispatch gates. This is specification work,
not a claim that Rust currently implements the new per-file behavior.

## Retirement and prompt reclamation

`Retirement` defines confirmed-absence grace, inconclusive inspections and
verified return, with exact persistence in owned control records.
`RetirementControl` performs the actual control update and conditional existing
cleanup capture inside a receipt-sealed shared transaction, preserving store
admissibility, metadata and other families. `RetirementCleanup` connects retired
availability to the existing reclamation contract without a retention TTL.
See [the lifecycle and implementation boundary](RETIREMENT.md).

## Repository discovery and stable identities

`RepositoryIdentity` separates database IDs, current locations and trusted
filesystem/Git object-incarnation evidence. Paths, content hashes, branch names
and remote URLs do not establish identity. There are no private IDs in Git
metadata. When evidence is insufficient, `RepositoryDiscovery` uses the generic
corrective dialogue, bound to the current inspection. Both same-repository and
new/replacement answers have constructive next decisions. See
[the discovery contract](REPOSITORY-IDENTITY.md).

`RegistryCreation` writes the family reservation, typed immutable creation policy
and first checkout in one receipt-sealed transaction. It cannot start indexing.
`RepositoryRegistry` implements guarded location updates and admission of fresh
checkouts under an existing family. General laws cover actual stored records,
other-family preservation and interrupted-run/completed-retry convergence.
`DirectoryConversion` retains directory behavior until an explicitly requested,
Git-reclassified view and updated metadata can publish together. Its publication
adapter owes fixed content, structural, retention and cleanup outcomes; this is
a mandatory refinement interface, not a completed Rust/SQL implementation.

## Unregistration and forget-all

`RemovalStore` defines an exhaustive policy over every owned category and
compiles it to ordinary DB removes/puts in one shared transaction. It proves
actual lookup results, complete scope cleanup, metadata preservation, other-family
isolation and store admissibility. `RepositoryRemoval` supplies receipt-first
admission, draining of earlier readers, actual completion and interruption/retry
convergence. See [removal semantics](REPOSITORY-REMOVAL.md).

The canonical removal intent is now `unregister`, matching existing `remove`.
It targets the whole family. The draft standalone clear-index intention and
checkout-only payload have been removed; reindex remains rebuilding. An active
removal receipt gates current-reader admission and content publication without
inventing a new registration state. A generic question before acceptance does
not pretend that work has already been saved.

## Durable indexing controls

[Work control](WORK-CONTROL.md) documents `WorkQueue`, `IndexControl`,
`WorkControlStore` and `FirstStart`: explicit authorization, accepted work
independent of MCP connections, current-work Ctrl-C pause, family resume, and
cancellation with durable cleanup. `ContentPublication` rechecks the worker
generation and pause state in its committing transaction. These are formal
product contracts; the Rust durable-job and administration adapters remain
implementation obligations.

## Staged vector readiness

[Staged vector publication](STAGED-VECTORS.md) replaces eager-first-party
embedding with text/symbol availability independent of vectors. `VectorData`,
`StagedVectors`, `TextPublication` and `VectorPublication` define validated
stored vectors, exact compatible reuse, truthful per-chunk/family coverage,
and receipt-sealed preservation of published text while vectors are prepared.
This is an approved behavior change; the Rust pipeline remains unchanged.

## Embedding-profile recreation

[Profile recreation](PROFILE-RECREATION.md) defines fixed derived-data removal,
new-profile publication, preserved identity/notes/settings and receipt-sealed
interruption/retry. `RepositoryProfile` binds code and curated-note vectors to
the actual saved family profile. Rebuild scheduling and runtime correspondence
remain the existing pipeline/dispatcher obligations.

## First-search continuation

[First search](FIRST-SEARCH.md) binds the complete saved query to verified
repository/checkout identity, arranges authorized work atomically and resumes
toward the actual published view. Selected-view eligibility and evidence-backed
freshness are explicit. Full retrieval/ranking, pagination, scheduling and
runtime correspondence remain their existing series obligations.

## Eligible text and semantic retrieval

[Retrieval](RETRIEVAL.md) binds matches to the current eligible checkout, actual
postings and vector associations, the stored binary32 representation and
binary64 scoring. Exact mode requires global completeness; approximate mode
reports its weaker candidate guarantee. All responses preserve numerical and
page bounds and expose actual semantic coverage. Source-provider and final
dispatch correspondence remain the existing series obligations.

## Complete hybrid ranking

[Hybrid ranking](HYBRID-RANKING.md) combines actual text/vector modality
candidates with the agreed fusion formula, current-policy vendor weights and
per-query vendor weighting. Its selection pipeline proves membership,
deterministic output and page bounds, with no per-file suppression.
Pagination and runtime correspondence remain their existing obligations.

See [stable pagination](PAGINATION.md) for typed saved queries, atomic page
receipts, finite approximate continuation and the no-idle-index-hold contract.
