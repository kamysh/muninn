{-# OPTIONS --safe #-}
-- Closed operation identities and outcome ownership. No execution scripts.
module Muninn.OperationCatalog where

open import Muninn.CatalogInputs
open import Relation.Binary.PropositionalEquality using (_≡_; cong)

data McpTool : Set where
  searchHybrid searchFulltext searchSemantic searchStructural : McpTool
  recordKnowledge searchKnowledge deleteKnowledge listKnowledge : McpTool

mcpIntent : McpTool → Intent
mcpIntent searchHybrid = searchCode hybrid
mcpIntent searchFulltext = searchCode fulltext
mcpIntent searchSemantic = searchCode semantic
mcpIntent searchStructural = searchStructure
mcpIntent recordKnowledge = writeNote
mcpIntent searchKnowledge = searchNotes
mcpIntent deleteKnowledge = deleteNote
mcpIntent listKnowledge = listNotes

data CliLeaf : Set where
  initAssignments globalGet globalSet globalUnset policyInspect policyCheck policyApply : CliLeaf
  preflightJson addJson startHuman startJson reindexOne reindexAll reindexDetached : CliLeaf
  pausePath resumePath removeConfirmed statusFleet statusPath usageDays : CliLeaf

cliIntent : CliLeaf → Intent
cliIntent initAssignments = replaceGlobal
cliIntent globalGet = inspectGlobal
cliIntent globalSet = replaceGlobal
cliIntent globalUnset = replaceGlobal
cliIntent policyInspect = inspectPolicy
cliIntent policyCheck = checkPolicy
cliIntent policyApply = applyPolicy
cliIntent preflightJson = preflight
cliIntent addJson = register
cliIntent startHuman = start
cliIntent startJson = start
cliIntent reindexOne = reindex
cliIntent reindexAll = reindex
cliIntent reindexDetached = reindex
cliIntent pausePath = pause
cliIntent resumePath = resume
cliIntent removeConfirmed = unregister
cliIntent statusFleet = status
cliIntent statusPath = status
cliIntent usageDays = usage

data TuiEffect : Set where
  inspectDraft previewDraft saveNewFamily saveExistingPolicy startSavedPolicy : TuiEffect
  refreshCurrent saveGlobalSettings : TuiEffect

tuiIntent : TuiEffect → Intent
tuiIntent inspectDraft = preflight
tuiIntent previewDraft = checkPolicy
tuiIntent saveNewFamily = register
tuiIntent saveExistingPolicy = applyPolicy
tuiIntent startSavedPolicy = start
tuiIntent refreshCurrent = inspectPolicy
tuiIntent saveGlobalSettings = replaceGlobal

data McpAdministration : Set where
  inspect check apply inventory registerFamily startFamily reindexFamily pauseFamily : McpAdministration
  resumeFamily cancelWork inspectStatus unregisterFamily forgetRepository recreateDerived convert : McpAdministration

adminIntent : McpAdministration → Intent
adminIntent inspect = inspectPolicy
adminIntent check = checkPolicy
adminIntent apply = applyPolicy
adminIntent inventory = preflight
adminIntent registerFamily = register
adminIntent startFamily = start
adminIntent reindexFamily = reindex
adminIntent pauseFamily = pause
adminIntent resumeFamily = resume
adminIntent cancelWork = cancel
adminIntent inspectStatus = status
adminIntent unregisterFamily = unregister
adminIntent forgetRepository = forget
adminIntent recreateDerived = recreateIndex
adminIntent convert = convertDirectory

data UserAdapter : Set where
  cliAdapter : CliLeaf → UserAdapter
  mcpAdapter : McpTool → UserAdapter
  tuiAdapter : TuiEffect → UserAdapter
  plannedAdministration : McpAdministration → UserAdapter
  conversationContinuation : UserAdapter

canonicalIntent : UserAdapter → Intent
canonicalIntent (cliAdapter leaf) = cliIntent leaf
canonicalIntent (mcpAdapter tool) = mcpIntent tool
canonicalIntent (tuiAdapter effect) = tuiIntent effect
canonicalIntent (plannedAdministration admin) = adminIntent admin
canonicalIntent conversationContinuation = continueRequest

-- Public operations, lifecycle events and finite background work enter here.
-- Local unsaved editor changes are not Muninn state.
data Request : Set where
  user : (adapter : UserAdapter) → IntentInput (canonicalIntent adapter) → Request
  background : (job : Job) → JobInput job → Request
  control : (event : Control) → ControlInput event → Request

data OutcomeOwner : Set where
  connection configuration selection registration indexing removal retrieval structure : OutcomeOwner
  knowledge continuation publication artifacts cleanup concurrency observability interface metadata : OutcomeOwner

intentOwner : Intent → OutcomeOwner
intentOwner inspectGlobal = connection
intentOwner replaceGlobal = connection
intentOwner inspectPolicy = configuration
intentOwner checkPolicy = selection
intentOwner applyPolicy = cleanup
intentOwner preflight = selection
intentOwner register = registration
intentOwner start = indexing
intentOwner reindex = indexing
intentOwner pause = indexing
intentOwner resume = indexing
intentOwner cancel = indexing
intentOwner unregister = removal
intentOwner forget = removal
intentOwner recreateIndex = artifacts
intentOwner convertDirectory = registration
intentOwner status = observability
intentOwner usage = observability
intentOwner (searchCode mode) = retrieval
intentOwner searchStructure = structure
intentOwner writeNote = knowledge
intentOwner searchNotes = knowledge
intentOwner deleteNote = knowledge
intentOwner listNotes = knowledge
intentOwner continueRequest = continuation

jobOwner : Job → OutcomeOwner
jobOwner preparePublic = connection
jobOwner prepareFamily = connection
jobOwner prepareGraph = connection
jobOwner fleetScan = indexing
jobOwner discoverCheckouts = registration
jobOwner observeCheckout = registration
jobOwner reconcileFamily = indexing
jobOwner reconcileCheckout = publication
jobOwner watchBatch = publication
jobOwner analyzeFile = artifacts
jobOwner publishCheckout = publication
jobOwner embedCode = artifacts
jobOwner embedNote = knowledge
jobOwner reclaimExcluded = cleanup
jobOwner reclaimRetired = removal
jobOwner handoff = concurrency
jobOwner recoverOperation = continuation
jobOwner appendLog = observability
jobOwner pruneLogs = observability
jobOwner flushDiagnostics = observability

controlOwner : Control → OutcomeOwner
controlOwner startup = connection
controlOwner shutdown = concurrency
controlOwner help = metadata
controlOwner version = metadata
controlOwner initializeMcp = interface
controlOwner listTools = interface
controlOwner notification = interface
controlOwner openEditor = interface
controlOwner interrupt = indexing

owner : Request → OutcomeOwner
owner (user adapter input) = intentOwner (canonicalIntent adapter)
owner (background job input) = jobOwner job
owner (control event input) = controlOwner event

sameIntentSameOwner : ∀ first second input otherInput →
  canonicalIntent first ≡ canonicalIntent second →
  owner (user first input) ≡ owner (user second otherInput)
sameIntentSameOwner first second input otherInput same = cong intentOwner same
