# Formal specification

`Muninn.agda` is the aggregate entry point. The proposed 1.0.0 worktree and
configuration behavior is documented in the
[design proposal](../docs/plans/2026-10-02-worktree-indexing-proposal.md).
The focused 2026-10-04 rollback removed custom file/graph trees and dependent
snapshot storage, analysis and capture code. Configuration, registration and Git
helpers remain. These specifications describe logical behavior; they do not
imply that indexing/publication is implemented or installed.

## Agreed model

- **One application schema per family, one AGE graph per checkout.** Kryzhen
  applies `repo/*` to the application schema; AGE manages each graph namespace.
  Existing migration blocks remain immutable.
- **One moving base and file deltas.** Main updates change the base and adjust
  worktree deltas while preserving each worktree's effective view. File versions
  and embeddings are shared; there are no physical baseline chains or trees.
  `FileMap.moveBase` formalizes this representation change. The `Baselines`
  environment in older modules can describe logical pre/post states; it does
  not require separately retained physical snapshots.
- **Independent published views.** A checkout's baseline reference, differences,
  and scoped graph are published together. Search uses the selected checkout's
  effective manifest, and visibility precedes ranking and limits.
- **Retain snapshots during Git operations.** A merge/rebase in progress or
  unresolved conflicts suspend indexing for that checkout. Serve its last
  snapshot with explicit stale/suspended status, or report pending if none
  exists. Do not parse/embed transient conflict contents. After completion or
  abort, reconcile automatically and publish only when ready. Ordinary local
  edits remain indexable. Hooks are optional; watching and reconciliation are
  required. Other worktrees continue independently.
- **Configuration and first start.** Local bootstrap supplies DB connection and
  secrets. Family policy lives in the DB. TUI and JSON clients share policy and
  cheap preflight; registration/configuration alone never starts a new family.
  After an explicit first start, discovered worktrees index automatically when
  schema, Git state, pause, and job guards allow it.

## Model and general laws

The schema pair is modeled in `Schema`/`Storage`. The physical storage design
has been withdrawn. `GraphMembership` supplies an abstract visibility contract;
`FileMap` proves laws about mathematical lookup functions. Neither implements a
prefix tree. Baseline/overlay abstractions remain for later reconciliation with
an accepted physical design; they do not authorize restoring the removed code.

| Module | Contract and proof coverage |
| --- | --- |
| `Muninn.Worktree` | Distinct identities; baseline/overlay semantics; `unchangedHasNoOverride`, `deletionMasksBaseline`, `pinnedBaselinePreservesView`, and `reuseKeepsBytes`; typed selected-checkout result and edge visibility. |
| `Muninn.FileMap` | General file-update lookup laws; `fileDifferenceResolves`, `fileDifferenceMinimal`, `normalizationPreservesFileView`, `normalizedFileOverlayIsMinimal`, `normalizationIsIdempotent`, `fileEditRetainsOtherPaths`, and `retainedFileMapView`. No physical storage representation is specified. |
| `Muninn.Schema` | Distinct application/graph identities; `schemaRoleInjective`; independent application migration completion and AGE readiness; `noDirectReadiness`, `readinessRequiresOwnTemplate`, `readinessRequiresGraph`, `readinessRequiresGraphMapping`, `noReadinessWithoutGraph`, and `noReadinessWithoutApplication`. `GraphReady` is independent of Kryzhen's template and ledger. |
| `Muninn.GraphMembership` | Family-qualified edge/symbol identities and extensional sets; `insertSelectsEdge`, `deleteExcludesEdge`, `otherMembershipUnchanged`, `unselectedCannotReturn`, `visibleEndpointsDoNotBypassMembership`, `foreignFamilyCannotReturn`, `extensionPreservesSelectedEdge`, and `viewMemberHasVisibleEndpoints`. |
| `Muninn.Storage` | One schema pair per family; isolation across both roles; `sameFamilySameSchemaPair`, `assignedSchemaIdentity`, `distinctFamiliesNoSchemaOverlap`, `otherCheckoutUnchanged`, `publicationPreservesReferences`, `publicationWhileBlockedRetains`, `extensionPreservesResolution`, `unreferencedRemovalPreservesReferences`, and `referencedFamilyCannotDrop`. Publication requires pair readiness. Retained baseline entries remain roots even when an override hides them. |
| `Muninn.IndexFsm` | Unified first-family/worktree transitions; `noAutoBeforeFamilyStart`, `blockedCannotStart`, `indexingRequiresReadySchema`, `blockedRetainsSnapshot`, and explicit stale/pending statuses; foreground priority and configuration/embedding rules. |
| `Muninn.Index` | Proposed dispatch gates; `dispatchNeedsExplicitFirstStart`, `blockedDispatchSkips`, and `dispatchPermitsBackgroundStart`. The pre-worktree decision is retained explicitly as `legacyDaemonDecision`. |
| `Muninn.Config` | Shared family policy with stored immutable defaults, bootstrap secrets, revisions, fixed schema vector dimension, and resolver evidence supplied by an external canonical-path relation. |
| `Muninn.Policy` | Explicit revision-one initialization, atomic history/current-pointer changes, stale-family/revision refusal, no-op preservation, retained history, generation invalidation and unchanged start/pause authorization. Stored policy resolution is independent of new binary defaults. |
| `Muninn.Registration` | Durable initial policy/defaults and family identity survive retries; completion preserves indexing authorization and cannot reopen permission to create a missing AGE graph. Absent creation intent cannot authorize graph creation. |
| `Muninn.Cli` | TUI/JSON/preflight intents, explicit first start, expected family/revision preconditions, and distinct directory/family removal intents. These do not prescribe final command flag spelling. |
| `Muninn.Knowledge` / `Muninn.Search` | Family-scoped curated notes, checkout-visible code, response freshness, `noCodeWithoutSnapshot`, and result bounds. |

## Proof boundary

The general laws quantify over arbitrary identities, views, and transitions.
There are no concrete test fixtures or example-only assertions in the new model.
Maps give extensional lookup semantics; the model does not prove a particular
SQL representation allocates no duplicate storage or meets latency budgets.
`Baselines` is an immutable environment of available snapshots, not a mutable
main-branch pointer. Its physical representation and GC of snapshot nodes still
need an implementation design.

Graph membership and endpoint visibility do not prove correct name resolution
or that a symbol ordinal was produced by a parser. Runtime graph lookup must
establish these facts. The extensional set-update laws do not prove a physical
storage implementation. The rejected Rust storage and its tests were removed.
Git state,
canonical path containment, migration receipts, and snapshot freshness are
observations the runtime must establish. The model does not prove the detector,
filesystem scan, Kryzhen SQL, AGE API calls, or Rust implementation correct. AGE
readiness and graph mapping are abstract observations, and the runtime must verify
their graph name and namespace against the same actual AGE catalog. Family
isolation is a predicate required of the assignment, not a proof that a live
registry satisfies it. The job FSM consumes a pair-readiness report; publication
also requires application migration completion and separate AGE readiness. These
requirements do not imply a shared transaction or a Kryzhen record for graph
operations. Filesystem watchers and
a quiet interval cannot establish an atomic filesystem
snapshot. Candidate revalidation and reader/build lifetime protection remain
implementation and integration-test obligations.

Earlier chunk, graph, ranking, and lock types remain where applicable. Legacy
`Repo`-based contracts describe the existing implementation; new family and
checkout identities must not be conflated with those legacy records. The
preflight equality and policy/registry predicates state required contracts;
they are not proofs of an implemented CLI or filesystem walker.

The policy model governs the isolated `family_policy` Rust primitives. Its
transition constructors require validation/identity evidence; it does not prove
the JSON parser, glob library, PostgreSQL constraints or transaction driver
correct. Finite JSON revision limits and SQL integer overflow are checked by
implementation tests. Policy storage and the preparation coordinator have
disposable-database coverage; CLI/TUI activation and live import remain separate.

## Checking

From `spec/`, use one interactive Agda process during proof development:

```sh
nix develop --command agda --interaction-json
```

For final aggregate verification:

```sh
nix develop --command agda Muninn.agda
```

Changed formal modules use `--safe` and belong to the aggregate import graph.
`Muninn.Float` retains its existing primitive Float declarations. The new model
introduces no postulates or unsafe options.
