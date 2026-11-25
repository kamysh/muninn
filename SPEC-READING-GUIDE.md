# Reading the Muninn specification

Start with the operation you want to understand. Each topic explains the
behavior before the Agda declarations and proofs that state its guarantees.
The links in each topic lead to the requirements, Rust code, and available
implementation checks.

| Topic | What it covers | Runtime evidence |
| --- | --- | --- |
| [Specification entry point](spec/Muninn.lagda.md) | The modules checked together and which publication contract governs current worktrees | [Formal and implementation boundary](spec/README.md) |
| [Worktree identity and views](spec/Muninn/Worktree.lagda.md) | Shared version ownership, stable checkout views, and evidence behind search results | [Worktree persistence](crates/core/tests/family_persistence/worktrees.rs) checks shared versions and sibling isolation |
| [Artifact identity](spec/Muninn/ArtifactIdentity.lagda.md) | What must match to reuse analysis, chunks, and embeddings | [File preparation](crates/core/src/worktrees/prepared.rs) checks exact source before reuse |
| [Worktree publication and sharing](spec/Muninn/CheckoutPublication.lagda.md) | Shared file versions, checkout-local publication, search during indexing, current exclusions, and reuse after interruption | [Database persistence scenarios](crates/core/tests/family_persistence/worktrees.rs) exercise shared versions, interruption, concurrent requests, and checkout isolation |
| [Earlier moving-base publication](spec/Muninn/ContentPublication.lagda.md) | How the historical design preserved sibling views while advancing a shared base | [Earlier publication contract](spec/CONTENT-PUBLICATION.md) |
| [Earlier serialized maintenance](spec/Muninn/SerializedMaintenance.lagda.md) | Why the former maintenance protocol drained readers and when it reopened admission | [Earlier maintenance contract](spec/ISSUE-203-SERIALIZED-MAINTENANCE.md) |
| [First worktree search](spec/Muninn/FirstSearch.lagda.md) | Checkout resolution, first-start authorization, indexing on demand, coverage, and result eligibility | [The on-demand MCP test](crates/mcp/src/worktree_tests.rs) pauses a first search during a Git operation and resumes it by ID on a fresh connection |
| [File selection](spec/Muninn/OrderedSelection.lagda.md) | Ordered rules, Git defaults, parent pruning, and vendor classification | [Policy tests](crates/core/src/family_policy/types.rs) and [selection maintenance](crates/core/tests/family_persistence/maintenance.rs) |
| [Internal symlinks](spec/Muninn/SymlinkSelection.lagda.md) | Logical paths, ignore decisions and checkout boundaries | [Worktree search](crates/mcp/src/worktree_tests.rs) exercises file and directory aliases |
| [File size limits](spec/Muninn/IndexFileLimits.lagda.md) | Text admission, structural size limits and progress of other files | [Policy runtime tests](crates/core/tests/family_persistence/runtime.rs) exercise policy changes for directory and Git families |
| [Structural search](spec/Muninn/StructuralSearch.lagda.md) | Direction, selected-view membership, endpoint visibility, and complete candidate order | [Graph tests](crates/core/tests/graph_integration.rs) and [MCP endpoint evidence](crates/mcp/src/worktree_tests.rs) |
| [Text and semantic retrieval](spec/Muninn/Retrieval.lagda.md) | Eligible postings and vectors, result bounds, and coverage | [Worktree persistence](crates/core/tests/family_persistence/worktrees.rs) covers search isolation. The [MCP test](crates/mcp/src/worktree_tests.rs) checks exact and approximate retrieval across embedding completion |
| [Curated note requests](spec/Muninn/NoteRequests.lagda.md) | Family-wide and checkout-local access, scoped changes, and receipts | [Note state](spec/NOTE-STATE.md) tracks Rust correspondence |
| [Registration](spec/Muninn/Registration.lagda.md) | Identity, saved policy, separate start authorization, and preparation retry | [Persistence tests](crates/core/tests/family_persistence.rs) and [CLI start progress](crates/cli/tests/start_progress.rs) |
| [Directory-to-Git conversion](spec/Muninn/RepositoryRegistration.lagda.md) | Explicit conversion with persistent family and checkout identities | [MCP lifecycle test](crates/mcp/src/worktree_tests.rs) |
| [Embedding profile recreation](spec/Muninn/ProfileRecreation.lagda.md) | Preserved policy and notes, reset derived data, and safe retries | [MCP lifecycle test](crates/mcp/src/worktree_tests.rs) |
| [Repository removal](spec/Muninn/RepositoryRemoval.lagda.md) | Retirement, deletion of owned records and receipt cleanup | [MCP administration](crates/mcp/src/admin.rs) and [worktree persistence](crates/core/tests/family_persistence/worktrees.rs) |
| [Database startup](spec/Muninn/DatabaseStartup.lagda.md) | Connection state, readiness, and recovery after failed preparation | [Disposable reconnect scenario](muninn-setup/test-reconnect.py) |
| [Database resumption](spec/Muninn/DatabaseResumption.lagda.md) | Retaining request identity during database loss and inspecting a receipt before resuming | [Watcher dispatcher](crates/indexer/src/main.rs) and [MCP request adapter](crates/mcp/src/requests.rs) |

The [formal index](spec/README.md) maps the wider Agda model. The
[operation catalog](spec/OPERATION-CATALOG.md) lists the broader operation
surface, including areas that still need a reader topic. A checked Agda law
establishes the stated property under its premises. The linked runtime tests
provide separate evidence about Rust and PostgreSQL.

When changing behavior, update the relevant literate module and its
applicable laws first. Then update the implementation and its verification.
Run the reader check to type-check the aggregate, render its literate
modules, and validate local links in the source documents.

```sh
nix develop --command python3 scripts/check_reader_spec.py
```

To keep the rendered pages for inspection, pass `--output` with a new
directory path.
