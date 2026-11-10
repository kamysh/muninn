{-# OPTIONS --safe #-}
-- Structural request types. Admission proves semantic validity separately;
-- no transport can substitute a different input type for the same intent.
module Muninn.CatalogInputs where

open import Data.Nat using (ℕ; _≤_)
open import Data.String using (String)
open import Data.List using (List)
open import Data.Maybe using (Maybe)
open import Data.Bool using (Bool)
open import Data.Product using (_×_)
open import Data.Unit using (⊤)
open import Muninn.Types using (UUID; FilePath)
open import Muninn.Worktree using (FamilyId; CheckoutId; VersionId)
open import Muninn.Config using (BootstrapConfig; IndexConfig; WatcherConfig; EmbeddingSelection)
open import Muninn.Knowledge using (KnowledgeId)
open import Muninn.Float using (Float)

record OperationId : Set where
  field value : UUID

record Mutation (A : Set) : Set where
  field operationId : OperationId
        input : A

data Locator : Set where
  repository cwd : FilePath → Locator

record FamilyTarget : Set where
  field location : Locator
        expectedFamily : FamilyId

record PolicyTarget : Set where
  field target : FamilyTarget
        expectedRevision : ℕ

record PolicyDraft : Set where
  field name : String
        index : IndexConfig
        watcher : WatcherConfig
        embeddings : EmbeddingSelection

record GlobalSettings : Set where
  field bootstrap : BootstrapConfig
        defaultIndex : IndexConfig
        defaultWatcher : WatcherConfig
        defaultEmbeddings : EmbeddingSelection

record Page : Set where
  field size : ℕ
        positive : 1 ≤ size
        bounded : size ≤ 1000
        continuation : Maybe UUID

data SearchMode : Set where
  fulltext semantic hybrid : SearchMode

data Precision : Set where
  approximate exact : Precision

record RankingOverrides : Set where
  field vendorWeight : Maybe Float

record SearchInput : Set where
  field location : Locator
        query : String
        page : Page
        precision : Precision
        ranking : RankingOverrides

data StructuralRelation : Set where
  callers callees imports defines inheritors inherits : StructuralRelation

record StructuralInput : Set where
  field location : Locator
        symbol : String
        relation : StructuralRelation
        page : Page

record NoteInput : Set where
  field target : FamilyTarget
        id : Maybe KnowledgeId
        origin : Maybe FilePath
        scope : Maybe CheckoutId
        title body : String
        tags : List String
        relatedFiles : List FilePath

data ReindexTarget : Set where
  foregroundIndex detachedIndex : FamilyTarget → ReindexTarget
  allRegistered : ReindexTarget

data Editor : Set where
  globalEditor familyEditor : Editor

data Binary : Set where
  cli mcp indexer : Binary

data Intent : Set where
  inspectGlobal replaceGlobal inspectPolicy checkPolicy applyPolicy preflight register : Intent
  start reindex pause resume cancel unregister forget recreateIndex convertDirectory status usage : Intent
  searchCode : SearchMode → Intent
  searchStructure writeNote searchNotes deleteNote listNotes continueRequest : Intent

IntentInput : Intent → Set
IntentInput inspectGlobal = Maybe String
IntentInput replaceGlobal = Mutation GlobalSettings
IntentInput inspectPolicy = Locator
IntentInput checkPolicy = Locator × PolicyDraft
IntentInput applyPolicy = Mutation (PolicyTarget × PolicyDraft)
IntentInput preflight = Locator
IntentInput register = Mutation (Locator × PolicyDraft)
IntentInput start = Mutation PolicyTarget
IntentInput reindex = Mutation ReindexTarget
IntentInput pause = Mutation FamilyTarget
IntentInput resume = Mutation FamilyTarget
IntentInput cancel = Mutation (FamilyTarget × OperationId)
IntentInput unregister = Mutation FamilyTarget
IntentInput forget = Mutation FamilyTarget
IntentInput recreateIndex = Mutation (FamilyTarget × EmbeddingSelection)
IntentInput convertDirectory = Mutation FamilyTarget
IntentInput status = Maybe FamilyTarget
IntentInput usage = ℕ
IntentInput (searchCode mode) = SearchInput
IntentInput searchStructure = StructuralInput
IntentInput writeNote = Mutation NoteInput
IntentInput searchNotes = FamilyTarget × String × Page
IntentInput deleteNote = Mutation (FamilyTarget × KnowledgeId)
IntentInput listNotes = FamilyTarget × Page
IntentInput continueRequest = OperationId

-- Finite jobs are distinct from the service loop that schedules them.
data Job : Set where
  preparePublic prepareFamily prepareGraph fleetScan discoverCheckouts observeCheckout : Job
  reconcileFamily reconcileCheckout watchBatch analyzeFile publishCheckout embedCode embedNote : Job
  reclaimExcluded reclaimRetired handoff recoverOperation recordUsage appendLog pruneLogs flushDiagnostics : Job

record FamilyJob : Set where
  field operationId : OperationId
        family : FamilyId

record CheckoutJob : Set where
  field parent : FamilyJob
        checkout : CheckoutId

record FileJob : Set where
  field parent : CheckoutJob
        path : FilePath
        version : Maybe VersionId

record UsageInput : Set where
  field tool : String
        family : Maybe FamilyId
        durationMilliseconds : ℕ
        resultCount : Maybe ℕ

JobInput : Job → Set
JobInput preparePublic = BootstrapConfig
JobInput prepareFamily = FamilyJob
JobInput prepareGraph = FamilyJob × Maybe CheckoutId
JobInput fleetScan = OperationId
JobInput discoverCheckouts = FamilyJob
JobInput observeCheckout = CheckoutJob
JobInput reconcileFamily = FamilyJob
JobInput reconcileCheckout = CheckoutJob
JobInput watchBatch = FamilyJob × Maybe (List FilePath)
JobInput analyzeFile = FileJob
JobInput publishCheckout = CheckoutJob
JobInput embedCode = FamilyJob × VersionId
JobInput embedNote = FamilyJob × KnowledgeId
JobInput reclaimExcluded = FamilyJob
JobInput reclaimRetired = FamilyJob
JobInput handoff = FamilyJob
JobInput recoverOperation = OperationId
JobInput recordUsage = UsageInput
JobInput appendLog = String
JobInput pruneLogs = ℕ
JobInput flushDiagnostics = ⊤

data Control : Set where
  startup shutdown help version initializeMcp listTools notification openEditor interrupt : Control

ControlInput : Control → Set
ControlInput startup = Binary
ControlInput shutdown = Binary
ControlInput help = Binary × List String
ControlInput version = Binary
ControlInput initializeMcp = String
ControlInput listTools = ⊤
ControlInput notification = String
ControlInput openEditor = Editor × Maybe Locator
ControlInput interrupt = OperationId

-- Local editing cannot carry an arbitrary database script. Effectful Save,
-- Check, Start and Refresh use their shared public intents above.
data UiAction : Set where
  openView editField advanced editMore rules defaults selectRule addRule close back : UiAction
  loadCurrent keepDraft confirmSave confirmDiscard confirmLoad confirmKeep confirmRemove : UiAction
  removeRule moveRule selectProvider editText selectSecret focus scroll helpModal : UiAction

record UiInput : Set where
  field editor : Editor
        action : UiAction
        selection : ℕ
        text : String
