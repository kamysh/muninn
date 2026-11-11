# Operation catalog

`OperationCatalog` is the closed logical inventory of public operations,
lifecycle controls and finite background jobs. Inputs are indexed by operation;
no catalog constructor takes an arbitrary execution script. A search request is
opaque here: matching and ranking are outside the state specification. Local
unsaved editor changes are not modeled as Muninn state.

Each entry maps to an outcome area in the catalog. These are ownership labels,
not proofs that an operation implements its outcome. The proof-carrying
dispatcher and mechanical runtime coverage remain #48–#52. The runtime currently
does not require the modeled durable ID for every write; that correspondence is
also outstanding.

## Current MCP tools

The eight tools in `McpTool` correspond to the names advertised and dispatched
in `crates/mcp/src/main.rs`; their handlers are in `crates/mcp/src/tools.rs`.

| Catalog | Wire name | Handler |
| --- | --- | --- |
| `searchHybrid` | `search_hybrid` | `search_hybrid` |
| `searchFulltext` | `search_fulltext` | `search_fulltext` |
| `searchSemantic` | `search_semantic` | `search_semantic` |
| `searchStructural` | `search_structural` | `search_structural` |
| `recordKnowledge` | `record_knowledge` | `record_knowledge` |
| `searchKnowledge` | `search_knowledge` | `search_knowledge` |
| `deleteKnowledge` | `delete_knowledge` | `delete_knowledge` |
| `listKnowledge` | `list_knowledge` | `list_knowledge` |

## Planned MCP administration

The following names were approved for the planned administration surface. They
are not advertised or implemented by the current MCP server. `continue_request`
is also planned for continuing a request or providing an answer.

| Catalog | Planned wire name |
| --- | --- |
| `inspect` | `inspect_policy` |
| `check` | `check_policy` |
| `apply` | `apply_policy` |
| `inventory` | `preflight_family` |
| `registerFamily` | `register_family` |
| `startFamily` | `start_family` |
| `reindexFamily` | `reindex_family` |
| `pauseFamily` | `pause_family` |
| `resumeFamily` | `resume_family` |
| `cancelWork` | `cancel_work` |
| `inspectStatus` | `inspect_status` |
| `unregisterFamily` | `unregister_family` |
| `forgetRepository` | `forget_repository` |
| `recreateDerived` | `recreate_index` |
| `convert` | `convert_directory` |

## CLI, editor and background work

`CliLeaf` covers `init`, global `config get/set/unset`, family policy
inspect/check/apply, `preflight`, `add`, `start`, `reindex`, `pause`, `resume`,
`remove`, `status`, and `usage`. Their parser and dispatch are in
`crates/cli/src/main.rs`; family JSON operations are in `crates/cli/src/writes.rs`
and `crates/cli/src/readonly.rs`. Opening a configuration editor is a control;
effectful editor actions are in `TuiEffect`, implemented in `crates/cli/src/tui/`.

`Job` names finite work, including preparation, discovery, reconciliation,
indexing, embedding, cleanup, recovery and logging. The current daemon starts
and schedules work in `crates/indexer/src/main.rs` and `crates/indexer/src/watcher.rs`;
indexing is in `crates/core/src/pipeline.rs`. Some job identities describe the
agreed target state and have no current standalone runtime handler. Startup,
shutdown, notifications, help, version, tool listing and interruption are
`Control` events; their protocol and process handling are in the MCP, CLI and
daemon entry points above.

The entries below identify the closest current source; a planned entry has no
standalone handler. Several logical jobs are parts of one existing function.

| Logical job | Current source or target status |
| --- | --- |
| `preparePublic` | `crates/core/src/db.rs` (`run_migrations`) |
| `prepareFamily`, `prepareGraph` | `crates/core/src/family_store/preparation.rs` (`prepare_family`) |
| `fleetScan` | `crates/indexer/src/main.rs` (`scan_and_dispatch`) |
| `discoverCheckouts` | `crates/core/src/worktrees/mod.rs` (`discovery`) |
| `observeCheckout` | `crates/core/src/repo_resolver/git_state.rs` |
| `reconcileFamily`, `reconcileCheckout` | `crates/core/src/worktrees/mod.rs` (`reconcile_family`, `reconcile_requested_checkout`) |
| `watchBatch` | `crates/indexer/src/watcher.rs` (`watch_repo`, `watch_family`) |
| `analyzeFile`, `publishCheckout`, `embedCode` | `crates/core/src/pipeline.rs` (`index_repo`) |
| `embedNote` | `crates/mcp/src/tools.rs` (`record_knowledge`); separate job is planned |
| `reclaimExcluded`, `reclaimRetired` | Target cleanup work; no standalone handler established |
| `handoff` | `crates/indexer/src/main.rs`; independent queued handoff is planned |
| `recoverOperation` | Planned; no durable-operation recovery handler established |
| `appendLog`, `flushDiagnostics` | `crates/indexer/src/logging.rs`; standalone jobs are planned |
| `pruneLogs` | `crates/mcp/src/main.rs` (`prune_log_dir`) |

The catalog does not establish that the above mappings are complete or that
Rust handlers follow the modeled inputs and outcomes. Those checks remain the
existing coverage and correspondence issues; this inventory is not a claim
that the missing MCP administration or background adapters exist.
