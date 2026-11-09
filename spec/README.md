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
| `Worktree`, `FileMap` | Abstract file lookup, overrides/deletions, minimal differences and moving-base preservation |
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
| Curated knowledge | `Knowledge` models family-scoped notes | `public.knowledge` and MCP knowledge tools use exact repository-path strings |
| Freshness | `Search` models response freshness/suspension | MCP code-search responses contain result lists without that metadata |
| Removal | `Cli` distinguishes abstract directory/family intents | Legacy `remove PATH` resolves a registered locator and deletes the family's code index; Git discovery handles checkout retirement |

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
