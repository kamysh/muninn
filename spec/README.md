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
