{-# OPTIONS --safe #-}
-- Structural request types. Admission proves semantic validity separately;
-- no transport can substitute a different input type for the same intent.
module Muninn.CatalogInputs where

open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Data.List using (List)
open import Data.Maybe using (Maybe)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_)
open import Data.Unit using (⊤)
open import Muninn.Types using (UUID; FilePath)
open import Muninn.Worktree using (FamilyId; CheckoutId; VersionId)
open import Muninn.Config using (BootstrapConfig; IndexConfig; WatcherConfig; EmbeddingSelection)
open import Muninn.Knowledge using (KnowledgeId)

record OperationId : Set where
  field value : UUID

-- Resolved internally before an operation is admitted; this is not a new
-- CLI or MCP argument. It lets repository removal find its detailed receipts.
data Owner : Set where
  installationOwner : Owner
  repositoryOwner : FamilyId → Owner

record Mutation (A : Set) : Set where
  field operationId : OperationId
        owner : Owner
        input : A

data Locator : Set where
  repository cwd : FilePath → Locator

record FamilyTarget : Set where
  field location : Locator
        expectedFamily : FamilyId

record PolicyTarget : Set where
  field target : FamilyTarget
        expectedRevision : ℕ

record FileLimits : Set where
  field selectedBytes : ℕ
        structuralBytes : ℕ

record PolicyDraft : Set where
  field name : String
        index : IndexConfig
        limits : FileLimits
        watcher : WatcherConfig
        embeddings : EmbeddingSelection

record GlobalSettings : Set where
  field bootstrap : BootstrapConfig
        defaultIndex : IndexConfig
        defaultLimits : FileLimits
        defaultWatcher : WatcherConfig
        defaultEmbeddings : EmbeddingSelection
        interactiveSlots : ℕ
        handoffPollSeconds : ℕ

data SearchMode : Set where
  fulltext semantic hybrid : SearchMode

-- Search content is opaque here; the state machine only needs its location
-- and must retain the request when work continues.
record SearchInput : Set where
  field location : Locator
        request : String

record StructuralInput : Set where
  field location : Locator
        request : String

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

record ContinueInput : Set where
  constructor continueInput
  field requestId : OperationId
        message : Maybe String

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
IntentInput searchNotes = FamilyTarget × String
IntentInput deleteNote = Mutation (FamilyTarget × KnowledgeId)
IntentInput listNotes = FamilyTarget × String
IntentInput continueRequest = ContinueInput

-- Finite jobs are distinct from the service loop that schedules them.
data Job : Set where
  preparePublic prepareFamily prepareGraph fleetScan discoverCheckouts observeCheckout : Job
  reconcileFamily reconcileCheckout watchBatch analyzeFile publishCheckout embedCode embedNote : Job
  reclaimExcluded reclaimRetired handoff appendLog pruneLogs flushDiagnostics : Job

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

JobInput : Job → Set
JobInput preparePublic = OperationId × BootstrapConfig
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
JobInput appendLog = OperationId × String
JobInput pruneLogs = OperationId × ℕ
JobInput flushDiagnostics = OperationId


-- Preserve the complete notification payload for its handler. Parsing and
-- validation of the JSON text remain the transport adapter’s responsibility.
record NotificationInput : Set where
  constructor notificationInput
  field method : String
        parametersJson : String

data Control : Set where
  startup shutdown help version initializeMcp listTools notification openEditor interrupt : Control

ControlInput : Control → Set
ControlInput startup = Binary
ControlInput shutdown = Binary
ControlInput help = Binary × List String
ControlInput version = Binary
ControlInput initializeMcp = String
ControlInput listTools = ⊤
ControlInput notification = NotificationInput
ControlInput openEditor = Editor × Maybe Locator
ControlInput interrupt = OperationId
