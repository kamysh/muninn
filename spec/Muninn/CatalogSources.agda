{-# OPTIONS --safe #-}
-- Exhaustive source assignments are not implementation-correspondence proofs.
-- Missing entries stay explicit and cannot be mistaken for runnable handlers.
module Muninn.CatalogSources where

open import Muninn.CatalogInputs
open import Muninn.Catalog
open import Data.String using (String)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)

data Source : Set where
  cliMain cliReadonly cliWrites cliRemoval tuiMain tuiBackend tuiGlobal mcpMain mcpTools indexerMain watcher diagnostics database familyStore familyPreparation resolver worktrees pipeline store knowledgeStore : Source

path : Source → String
path cliMain = "crates/cli/src/main.rs"
path cliReadonly = "crates/cli/src/readonly.rs"
path cliWrites = "crates/cli/src/writes.rs"
path cliRemoval = "crates/cli/src/removal.rs"
path tuiMain = "crates/cli/src/tui/mod.rs"
path tuiBackend = "crates/cli/src/tui/backend.rs"
path tuiGlobal = "crates/cli/src/tui/global.rs"
path mcpMain = "crates/mcp/src/main.rs"
path mcpTools = "crates/mcp/src/tools.rs"
path indexerMain = "crates/indexer/src/main.rs"
path watcher = "crates/indexer/src/watcher.rs"
path diagnostics = "crates/indexer/src/logging.rs"
path database = "crates/core/src/db.rs"
path familyStore = "crates/core/src/family_store/mod.rs"
path familyPreparation = "crates/core/src/family_store/preparation.rs"
path resolver = "crates/core/src/repo_resolver.rs"
path worktrees = "crates/core/src/worktrees/mod.rs"
path pipeline = "crates/core/src/pipeline.rs"
path store = "crates/core/src/store.rs"
path knowledgeStore = "crates/core/src/knowledge.rs"

record Site : Set where
  constructor site
  field source : Source
        symbol : String

data Coverage : Set where
  sourceRecorded : Site → Coverage
  missing : Site → ℕ → Coverage

cliSite : CliLeaf → Site
cliSite initAssignments = site cliMain "handle_init"
cliSite globalGet = site cliMain "handle_global_config"
cliSite globalSet = site cliMain "handle_global_config"
cliSite globalUnset = site cliMain "handle_global_config"
cliSite policyInspect = site cliReadonly "run"
cliSite policyCheck = site cliReadonly "run"
cliSite policyApply = site cliWrites "apply"
cliSite preflightJson = site cliReadonly "run"
cliSite addJson = site cliWrites "add"
cliSite startHuman = site cliWrites "start"
cliSite startJson = site cliWrites "start"
cliSite reindexOne = site cliMain "run_foreground_index"
cliSite reindexAll = site cliMain "main"
cliSite reindexDetached = site cliMain "main"
cliSite pausePath = site cliMain "main"
cliSite resumePath = site cliMain "main"
cliSite removeConfirmed = site cliMain "main"
cliSite statusFleet = site cliMain "main"
cliSite statusPath = site cliMain "main"
cliSite usageDays = site cliMain "main"

mcpSite : McpTool → Site
mcpSite searchHybrid = site mcpTools "search_hybrid"
mcpSite searchFulltext = site mcpTools "search_fulltext"
mcpSite searchSemantic = site mcpTools "search_semantic"
mcpSite searchStructural = site mcpTools "search_structural"
mcpSite recordKnowledge = site mcpTools "record_knowledge"
mcpSite searchKnowledge = site mcpTools "search_knowledge"
mcpSite deleteKnowledge = site mcpTools "delete_knowledge"
mcpSite listKnowledge = site mcpTools "list_knowledge"

tuiSite : TuiEffect → Site
tuiSite inspectDraft = site tuiBackend "load"
tuiSite previewDraft = site tuiBackend "check"
tuiSite saveNewFamily = site tuiBackend "save"
tuiSite saveExistingPolicy = site tuiBackend "save"
tuiSite startSavedPolicy = site tuiBackend "start"
tuiSite refreshCurrent = site tuiBackend "load"
tuiSite saveGlobalSettings = site cliMain "persist_global"

userCoverage : UserAdapter → Coverage
userCoverage (cliAdapter leaf) = sourceRecorded (cliSite leaf)
userCoverage (mcpAdapter tool) = sourceRecorded (mcpSite tool)
userCoverage (tuiAdapter effect) = sourceRecorded (tuiSite effect)
userCoverage (plannedAdministration admin) = missing (site mcpMain "dispatch_tool") 48
userCoverage conversationContinuation = missing (site mcpMain "handle_request") 48

jobCoverage : Job → Coverage
jobCoverage preparePublic = sourceRecorded (site database "run_migrations")
jobCoverage prepareFamily = sourceRecorded (site familyPreparation "prepare_family")
jobCoverage prepareGraph = sourceRecorded (site store "ensure_graph")
jobCoverage fleetScan = sourceRecorded (site indexerMain "scan_and_dispatch")
jobCoverage discoverCheckouts = sourceRecorded (site resolver "list_git_worktrees")
jobCoverage observeCheckout = sourceRecorded (site familyStore "record_checkout_observation")
jobCoverage reconcileFamily = sourceRecorded (site worktrees "reconcile_family")
jobCoverage reconcileCheckout = sourceRecorded (site worktrees "reconcile_requested_checkout")
jobCoverage watchBatch = sourceRecorded (site watcher "watch_repo")
jobCoverage analyzeFile = sourceRecorded (site pipeline "index_file")
jobCoverage publishCheckout = sourceRecorded (site worktrees "reconcile_requested_checkout")
jobCoverage embedCode = sourceRecorded (site pipeline "backfill_once")
jobCoverage embedNote = missing (site knowledgeStore "upsert") 43
jobCoverage reclaimExcluded = missing (site worktrees "garbage_collect") 25
jobCoverage reclaimRetired = missing (site familyStore "retire_if_missing") 33
jobCoverage handoff = sourceRecorded (site store "unlock")
jobCoverage recoverOperation = missing (site familyStore "reserve_family") 21
jobCoverage recordUsage = sourceRecorded (site mcpMain "record_usage")
jobCoverage appendLog = sourceRecorded (site mcpMain "init_logging")
jobCoverage pruneLogs = sourceRecorded (site mcpMain "prune_log_dir")
jobCoverage flushDiagnostics = sourceRecorded (site diagnostics "flush_stderr")

mainSite : Binary → Site
mainSite cli = site cliMain "main"
mainSite mcp = site mcpMain "main"
mainSite indexer = site indexerMain "main"

editorSite : Editor → Site
editorSite globalEditor = site tuiGlobal "run"
editorSite familyEditor = site tuiMain "drive"

controlCoverage : (event : Control) → ControlInput event → Coverage
controlCoverage startup binary = sourceRecorded (mainSite binary)
controlCoverage shutdown binary = sourceRecorded (mainSite binary)
controlCoverage help (binary , args) = sourceRecorded (mainSite binary)
controlCoverage version binary = sourceRecorded (mainSite binary)
controlCoverage initializeMcp protocol = sourceRecorded (site mcpMain "handle_request")
controlCoverage listTools input = sourceRecorded (site mcpMain "handle_request")
controlCoverage notification input = sourceRecorded (site mcpMain "handle_request")
controlCoverage openEditor (editor , location) = sourceRecorded (editorSite editor)

coverage : Request → Coverage
coverage (user adapter input) = userCoverage adapter
coverage (background job input) = jobCoverage job
coverage (control event input) = controlCoverage event input
coverage (localUi input) = sourceRecorded (editorSite (UiInput.editor input))

-- Owners name the independent contract work, not operation-supplied goals.
outcomeIssues : OutcomeOwner → List ℕ
outcomeIssues connection = 46 ∷ []
outcomeIssues configuration = 24 ∷ 26 ∷ []
outcomeIssues selection = 26 ∷ 27 ∷ 28 ∷ []
outcomeIssues registration = 32 ∷ []
outcomeIssues indexing = 35 ∷ []
outcomeIssues removal = 33 ∷ 34 ∷ []
outcomeIssues retrieval = 38 ∷ 39 ∷ 40 ∷ 41 ∷ []
outcomeIssues structure = 42 ∷ []
outcomeIssues knowledge = 43 ∷ []
outcomeIssues continuation = 20 ∷ 21 ∷ []
outcomeIssues publication = 30 ∷ 31 ∷ []
outcomeIssues artifacts = 29 ∷ 36 ∷ 37 ∷ []
outcomeIssues cleanup = 23 ∷ 24 ∷ 25 ∷ []
outcomeIssues concurrency = 44 ∷ 45 ∷ []
outcomeIssues observability = 47 ∷ []
outcomeIssues interface = 48 ∷ 49 ∷ 50 ∷ []
outcomeIssues metadata = 49 ∷ 50 ∷ []
