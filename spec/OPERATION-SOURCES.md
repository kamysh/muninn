# Operation and adapter source inventory

The user approved one semantic contract for equivalent CLI, MCP and TUI intents,
with resumable background jobs registered separately. `CatalogInputs` defines
structural input types; `Catalog` maps closed adapters to their shared intents;
`CatalogSources` assigns every request an independent outcome owner and an
explicit current-source or missing-adapter record. Approved administration wire
names are specified in `Catalog`; their runtime adapters remain absent.

This is the closed inventory, not the proof-requiring execution dispatcher.
`sourceRecorded` means that a matching Rust declaration exists, not that its
behavior already satisfies the independent outcome. `missing` names the current
integration site and the issue owning the absent adapter. Semantic input
validation, complete operation proofs and enforced dispatch remain #20, the
individual outcome issues, and #51/#52. Unknown wire names produce no tool ID;
the admission conversation must help the agent select an available operation.

Inputs here use current domain types. Later contracts must refine native path
encoding, complete policy settings (including the agreed size limits), numeric
ranking validity and narrower note scope; this PR does not silently decide
those remaining details or claim their validation is complete. Raw CLI/TUI
settings are lowered to a complete typed replacement before the shared change
request, preserving unspecified settings through the adapter contract.

## Mechanical MCP catalog check

`scripts/check_mcp_catalog.py` compares the literal advertised tools, dispatch
arms, formal wire names, decoder clauses, intent assignments and source-site
handler identities. It also checks the current initialization, tool-list and
tool-call transport routes. Unsupported source forms, duplicates and mismatches
are rejected. `tests/test_mcp_catalog.py` exercises missing, extra, duplicate,
misrouted and unsupported entries.

The checker validates the separately named planned administration and
continuation entries and reports that their current runtime adapters are absent.
As agreed for #48, proof-carrying operation enforcement and the mandatory gate
belong to #51; Rust effect correspondence remains #52. Matching names and
handlers alone does not prove implementation behavior.

## Current MCP surface

`crates/mcp/src/main.rs:78-275,428-476` advertises and dispatches exactly these
eight tool names; implementations are in `crates/mcp/src/tools.rs`.

| Wire tool | Current implementation | Independent outcome area |
| --- | --- | --- |
| `search_hybrid` | `tools.rs:55` | Selected-checkout retrieval and hybrid ranking (#39, #40) |
| `search_fulltext` | `tools.rs:91` | Selected-checkout retrieval (#39) |
| `search_semantic` | `tools.rs:107` | Selected-checkout retrieval and semantic coverage (#36, #39) |
| `search_structural` | `tools.rs:148` | Structural candidates and evidence (#42) |
| `record_knowledge` | `tools.rs:366` | Family-scoped knowledge writes (#43) |
| `search_knowledge` | `tools.rs:392` | Family-scoped knowledge retrieval (#43) |
| `delete_knowledge` | `tools.rs:422` | Family-scoped knowledge deletion (#43) |
| `list_knowledge` | `tools.rs:431` | Family-scoped knowledge listing (#43) |

The transport also handles initialization, listing and calls. Input parsing,
unknown methods/tools, notifications, EOF and malformed requests are admission
or connection lifecycle inputs, not permission to execute an arbitrary script.
Today malformed JSON is skipped and ordinary tool errors become JSON-RPC errors;
the agreed corrective conversation is still missing from Rust (#20, #52).

## Current CLI leaves

`crates/cli/src/main.rs:22-125,339-387,391-724,726-790` defines:

| Current command or variant | Effect implementation / outcome area |
| --- | --- |
| `init KEY=VALUE...`, bare `init` | Bootstrap persistence and database preparation; global TUI for the bare form (#46, #49) |
| `config --global get [KEY]` | Global read, including unset-key behavior (#46, #49) |
| `config --global set KEY=VALUE...`, `unset KEY`, `edit` | Validated global replacement, owner-only temporary file, save then database preparation (#46, #49) |
| `config PATH`, `add PATH` without JSON | Native family editor, separate save and start (#49) |
| `config PATH --json` | `readonly.rs`: current policy inspection (#26, #49) |
| `config PATH --json --check -` | `readonly.rs`: complete candidate validation/preview without saving (#26, #49) |
| `config PATH --json --apply -` | `writes.rs`: revision-guarded policy change and reconciliation (#24, #25, #49) |
| `preflight PATH --json` | `readonly.rs`: cheap inventory without registration, migration or start (#26, #49) |
| `add PATH --json [--input -]` | `writes.rs`: registration with frozen creation policy (#32, #49) |
| `start PATH [--json] [--input -]` | `writes.rs`: guarded explicit first-start authorization and indexing (#35, #49) |
| `reindex PATH`, `reindex --all`, `reindex PATH --detach` | Foreground work, fleet iteration or handoff to daemon; compatible work reuse (#29, #35) |
| `pause PATH`, `resume PATH` | `WorkControlStore` preserves authorization and saved work; current Rust uses registry pause/preemption flags (#35) |
| `remove PATH [--yes]` | `removal.rs`, `store::delete_repo`: existing family unregistration and code-index deletion (#34) |
| `status`, `status PATH` | Fleet/detail status and truthful progress (#47) |
| `usage [--days N]` | Saved MCP usage query (#47) |
| Help/version for all three binaries | Clap-owned metadata output; no index or configuration mutation (#49, #50) |

Raw arguments are not already-valid catalog inputs. Required identities, policy
revision guards, explicit removal intention, page bounds and continuation context
must be checked by admission before an executable request is constructed.

## Current TUI inputs and effects

The family editor separates `Action` from `Confirm`, `Modal` and draft changes
(`tui/mod.rs:111-176`; `tui/model.rs:6-38,104-206`). Its current action set is:
open view, edit field, advanced view, edit more, rules, defaults, select/add rule,
check, save, start, close, back, refresh current, load current and keep draft.
Confirmations cover save, discard, load current, keep draft and remove rule.
Draft actions include removing/reordering a rule, provider selection, text edits,
focus/scroll/help/modal navigation and conflict review.

`tui/backend.rs:18-29` exposes load, check, save, start and start-with-progress.
Saving an unregistered draft invokes registration; saving an existing one applies
policy and may associate a checkout. Start invokes guarded indexing separately.
UI cancel/discard does not undo an already committed save.

The global editor (`tui/global.rs:157-185,603-917`) has field, advanced, save,
cancel, back, add and rule actions, with text/provider/secret/docs/confirmation/
rule modals. It returns an optional draft; `main.rs:314-387` owns persistence and
database preparation. Terminal editing inputs and effectful save/start requests
must both be covered; a UI key is not automatically a database operation.

## Startup, background and maintenance work

| Entry point | Work and independent outcome area |
| --- | --- |
| CLI `main`, `handle_init`, global save | Load/create bootstrap, validate settings, prepare intended database (#46, #49) |
| MCP `main.rs:25-75` | Bootstrap/logging, connections, public migrations, embedding backend setup, input loop and EOF (#46, #48) |
| MCP `init_logging`, rolling writer, `prune_log_dir` | Owned file logging and periodic retention; preserve foreign files in the configured directory (owned-state inventory records current mismatch) |
| MCP `record_usage` | Optional usage persistence without replacing the successful user result (#47, #48) |
| Search `tools::resolve_worktree`, `worktrees::resolve` | Discover selected checkout, arrange first indexing and continue the request (#32, #38) |
| Daemon `main.rs:32-121` | Bootstrap, migration, LISTEN setup, initial scan, notification/poll dispatch and shutdown (#46, #50) |
| `scan_and_dispatch`, `main.rs:165-545` | Registry scan, confirmed absence/retirement, pause/authorization checks, watcher eviction/restart, reindex launch (#33, #35, #44, #50) |
| `watcher::watch_repo`, `watch_family` | Debounced filesystem changes, overflow recovery, discovery/Git observation, reconciliation and retry (#30, #31, #32, #50) |
| `pipeline`, `worktrees::reconcile_*` | Accepted file analysis, publication, graph work, pending embeddings and bounded reclamation (#29, #30, #36) |
| `family_store::PreparationConnection`, graph readiness | Family/public migration progress, registration recovery and AGE readiness (#32, #46) |
| `logging::RepeatedEvents` | Periodic summary and final diagnostic flush; no per-family index mutation (#47, #50) |
| Agreed durable cleanup worker, receipt/continuation recovery | Runtime adapters absent: fixed worksets, exclusion completion and resumable interaction (#20-#25) |

Long-lived service loops must be decomposed into finite catalog operations and
explicit waiting/scheduling; a proof of a tick must not be presented as a proof
that the whole daemon exits. Scheduling/environment assumptions remain explicit.

## Agreed MCP administration still missing

The user approved full administration through MCP: configuration inspection,
checking and application; registration/discovery; start/reindex/pause/resume/
cancel; status; unregistration versus forget-all; and derived-index recreation for
an embedding profile change while retaining notes/settings. The current eight
tools do not expose this scope. `Catalog.adminWireName` defines the approved
planned names; these are not yet advertised by the running server.
Exact runtime adapters and their correspondence remain #52.

The planned wire names are:

| Purpose | MCP name |
| --- | --- |
| Inspect, check and apply policy | `inspect_policy`, `check_policy`, `apply_policy` |
| Preview and register a family | `preflight_family`, `register_family` |
| Start, reindex, pause and resume | `start_family`, `reindex_family`, `pause_family`, `resume_family` |
| Cancel work and inspect status | `cancel_work`, `inspect_status` |
| Unregister or forget a repository | `unregister_family`, `forget_repository` |
| Recreate derived data or convert a directory | `recreate_index`, `convert_directory` |
| Continue a conversation | `continue_request` |

The closed catalog must also name missing corrective conversation, operation-ID,
continuation and background-work adapters. Missing implementation must be explicit;
neither a raw script entry nor a permissive fallback establishes coverage.

### Work-control contract (#35)

`FirstStart` binds authorization to the actual family/current policy and saves
accepted work with its checkpoint. `IndexControl` gates indexing commits on
actual durable work, phase and generation. `WorkControlStore` specifies current
request pause, family pause/resume and cancellation linked to the existing
bounded cleanup/finalization protocol. Current CLI Ctrl-C exits with code 130;
the agreed behavior is a durable pause with the explicit resume command.
Cancellation is an agreed administration intent, not an existing CLI leaf or
new MCP wire name. See [the work-control contract](WORK-CONTROL.md).

### Staged text/vector publication (#36)

`pipeline.rs` currently embeds first-party chunks eagerly and defers vendor
chunks. The approved `TextPublication`/`VectorPublication` contracts permit
text and symbol publication before vectors for both tiers. `StagedVectors`
derives coverage from actual stored associations and requires reuse of compatible
completed vectors; `VectorData` certifies usable coordinates. See
[staged vector publication](STAGED-VECTORS.md) for the current Rust gap and
provider/pipeline/search correspondence boundaries.

The existing `recreateIndex` intent is specified by `RecreationStore`,
`ProfileRecreation` and `RepositoryProfile`: explicit profile recreation, fixed
owned-world removal/preservation, current-policy publication and receipt retry.
It adds no standalone removal CLI command. End-to-end rebuild scheduling,
physical schema adaptation and final dispatcher enforcement remain separate
existing-series obligations. See [profile recreation](PROFILE-RECREATION.md).

First-search preparation and `continueRequest` query recovery are covered by
`SearchTarget`, `FirstSearch`, `SearchResumption`, `SearchView` and
`SearchReadiness`. Read queries remain separate from the durable finite
`reconcileCheckout` work they arrange. These contracts add no MCP/CLI wire name;
see [first search](FIRST-SEARCH.md) for the full execution boundary.

Selected-checkout full-text and semantic search are specified by `Retrieval`
and its numerical, corpus, text and selection modules. They require actual
eligible rows, complete source universes, stored-coordinate precision evidence,
truthful coverage and the appropriate exact/approximate outcome certificate.
See [retrieval](RETRIEVAL.md) for the English-provider and runtime boundary.

`HybridRanking` is the common reference pipeline for `searchCode hybrid`.
Legacy `Search` defaults/contributions delegate to `HybridNumbers`; a runtime
adapter must satisfy the selected-view modality contracts and return the
computed hybrid response, not call an isolated fusion helper as a substitute.
See [hybrid ranking](HYBRID-RANKING.md) for the exact/approximate boundary.

Search pagination and continuation checkpoints use `PaginationData`,
`Pagination`, `PaginationTraversal`, `PaginationAdvance`, `PaginationStore`,
`PaginationCommit`, `PaginationSource`, `PaginationCodeCall` and
`PaginationRanking`. The checkout page operation binds eligibility to actual
stored source rows; idle cursor rows have no strong data references. See
[stable pagination](PAGINATION.md) for the query, source and runtime boundaries.

Structural results use `StructuralSearch`: both endpoints and their edge are
in the selected eligible view, with name-based matching and source evidence.
See [structural search](STRUCTURAL-SEARCH.md) for the runtime boundary.
