{-# OPTIONS --safe #-}
-- Closed identities and adapter routing only. The proof-requiring execution
-- dispatcher is a later obligation: no constructor below accepts a Script.
module Muninn.Catalog where

open import Muninn.CatalogInputs
open import Data.String using (String)
open import Data.List using (List; []; _∷_)
import Data.Empty
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)

data McpTool : Set where
  searchHybrid searchFulltext searchSemantic searchStructural : McpTool
  recordKnowledge searchKnowledge deleteKnowledge listKnowledge : McpTool

wireName : McpTool → String
wireName searchHybrid = "search_hybrid"
wireName searchFulltext = "search_fulltext"
wireName searchSemantic = "search_semantic"
wireName searchStructural = "search_structural"
wireName recordKnowledge = "record_knowledge"
wireName searchKnowledge = "search_knowledge"
wireName deleteKnowledge = "delete_knowledge"
wireName listKnowledge = "list_knowledge"

decodeTool : String → Maybe McpTool
decodeTool "search_hybrid" = just searchHybrid
decodeTool "search_fulltext" = just searchFulltext
decodeTool "search_semantic" = just searchSemantic
decodeTool "search_structural" = just searchStructural
decodeTool "record_knowledge" = just recordKnowledge
decodeTool "search_knowledge" = just searchKnowledge
decodeTool "delete_knowledge" = just deleteKnowledge
decodeTool "list_knowledge" = just listKnowledge
decodeTool _ = nothing

mcpIntent : McpTool → Intent
mcpIntent searchHybrid = searchCode hybrid
mcpIntent searchFulltext = searchCode fulltext
mcpIntent searchSemantic = searchCode semantic
mcpIntent searchStructural = searchStructure
mcpIntent recordKnowledge = writeNote
mcpIntent searchKnowledge = searchNotes
mcpIntent deleteKnowledge = deleteNote
mcpIntent listKnowledge = listNotes

-- Metadata/help and editor-open commands are Control inputs, not mutations.
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

-- Approved administration scope, with NO new wire names assigned here.
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

-- One dependent input family is shared by every adapter for an intent.
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
jobOwner recordUsage = observability
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

-- Changing transport cannot change the assigned independent outcome owner.
sameIntentSameOutcomeOwner : ∀ first second input otherInput →
  canonicalIntent first ≡ canonicalIntent second →
  owner (user first input) ≡ owner (user second otherInput)
sameIntentSameOutcomeOwner first second input otherInput same = cong intentOwner same

wireRoundTrip : ∀ tool → decodeTool (wireName tool) ≡ just tool
wireRoundTrip searchHybrid = refl
wireRoundTrip searchFulltext = refl
wireRoundTrip searchSemantic = refl
wireRoundTrip searchStructural = refl
wireRoundTrip recordKnowledge = refl
wireRoundTrip searchKnowledge = refl
wireRoundTrip deleteKnowledge = refl
wireRoundTrip listKnowledge = refl


unknownNotAdvertised : ∀ name → decodeTool name ≡ nothing →
  ∀ tool → wireName tool ≡ name → Data.Empty.⊥
unknownNotAdvertised name unknown tool same
  with trans (sym (wireRoundTrip tool)) (trans (cong decodeTool same) unknown)
... | ()
