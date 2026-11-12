{-# OPTIONS --safe #-}
-- Status is derived from the saved receipt, not inferred from a request.
module Muninn.StatusReport where

import Muninn.OwnedState as O
import Muninn.ReceiptLedger as Ledger
import Muninn.ReceiptTypes as Receipt
import Muninn.RequestIdentity as Identity
open import Muninn.CatalogInputs using (OperationId)
import Data.Bool
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₂)
open import Data.Empty using (⊥-elim)
open import Data.String using (String)
open import Data.Nat using (ℕ; zero; suc; _≤?_)
open import Data.List using (List; []; _∷_)
open import Data.Integer using (ℤ)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Progress : Set where
  unknown : Progress
  active : Receipt.Work → Progress
  finished : String → Progress
  historyRemoved : Progress

read : OperationId → O.World → Progress
read id world with Ledger.find id world
... | nothing = unknown
... | just (Ledger.found slot owner (Receipt.active input names work)) = active work
... | just (Ledger.found slot owner (Receipt.finished input names result)) = finished result
... | just (Ledger.found slot owner Receipt.used) = historyRemoved

-- The accepted intent is distinct from work progress or a completed result.
savedIntent : OperationId → O.World → Maybe Identity.Meaning
savedIntent id world with Ledger.find id world
... | nothing = nothing
... | just saved = Receipt.request (Ledger.Found.state saved)

-- Inspecting private bookkeeping neither writes a hold nor mutates the world.
inspect : OperationId → O.DB.Transaction Progress
inspect id = O.DB.scan (λ world → O.DB.commit (read id world))
inspectionPreservesWorld : ∀ id world → proj₂ (O.DB.execute (inspect id) world) ≡ world
inspectionPreservesWorld id world = refl

activeFromReceipt : ∀ id world slot owner input names work →
  Ledger.find id world ≡ just (Ledger.found slot owner (Receipt.active input names work)) →
  read id world ≡ active work
activeFromReceipt id world slot owner input names work found rewrite found = refl

finishedFromReceipt : ∀ id world slot owner input names result →
  Ledger.find id world ≡ just (Ledger.found slot owner (Receipt.finished input names result)) →
  read id world ≡ finished result
finishedFromReceipt id world slot owner input names result found rewrite found = refl

unknownFromReceipt : ∀ id world → Ledger.find id world ≡ nothing → read id world ≡ unknown
unknownFromReceipt id world found rewrite found = refl

-- A saved result cannot be invented from an absent, active or reclaimed receipt.
finishedHasReceipt : ∀ id world result → read id world ≡ finished result →
  Σ (Ledger.Found id) (λ saved → Ledger.find id world ≡ just saved ×
    Receipt.savedResult (Ledger.Found.state saved) ≡ just result)
finishedHasReceipt id world result claimed with Ledger.find id world in found
... | nothing with claimed
...   | ()
finishedHasReceipt id world result claimed | just (Ledger.found slot owner (Receipt.active input names work)) with claimed
...   | ()
finishedHasReceipt id world result claimed | just (Ledger.found slot owner (Receipt.finished input names savedResult)) with claimed
...   | refl = Ledger.found slot owner (Receipt.finished input names savedResult) , refl , refl
finishedHasReceipt id world result claimed | just (Ledger.found slot owner Receipt.used) with claimed
...   | ()

-- Messages do not claim that merely accepted work is complete.
nextStep : Progress → String
nextStep unknown = "I cannot find this work. Tell me what you were trying to do."
nextStep (active work) = "The request is still in progress. Continue this request to check its saved progress."
nextStep (finished result) = "The request has a saved result."
nextStep historyRemoved = "The details are no longer available. Inspect the current state before starting new work."

-- Coverage is read from published content, not inferred from an accepted job.
import Muninn.StagedContent as Content
coverage : Content.State → Content.Coverage
coverage = Content.coverage

coverageReadyHasVector = Content.readyHasAssociatedVector

import Muninn.VectorData as Vector

-- A saved explanation accompanies content whose vector is unavailable.
vectorGuidance : (content : Content.State) → Maybe Vector.Guidance
vectorGuidance (Content.state tier source profile text symbols Content.pending) = nothing
vectorGuidance (Content.state tier source profile text symbols (Content.unavailable guidance)) = just guidance
vectorGuidance (Content.state tier source profile text symbols (Content.ready saved profileMatches sourceMatches)) = nothing

guidanceFromStoredContent : ∀ tier source profile text symbols guidance →
  vectorGuidance (Content.state tier source profile text symbols (Content.unavailable guidance)) ≡ just guidance
guidanceFromStoredContent tier source profile text symbols guidance = refl

-- Index progress and committed results are observed from the same saved state.
import Muninn.IndexWorkControl as Index
module IndexStatus (Progress Results Temporary : Set) where
  module I = Index.Model Progress Results Temporary

  data Activity : Set where
    noActiveWork : Activity
    working : Progress → Activity
    paused : Progress → Activity

  activity : I.State → Activity
  activity (I.state authorized nothing results temporary) = noActiveWork
  activity (I.state authorized (just (I.work I.running progress)) results temporary) = working progress
  activity (I.state authorized (just (I.work I.paused progress)) results temporary) = paused progress

  nextAction : Activity → String
  nextAction noActiveWork = "No indexing work is running. Start indexing if you want to update the index."
  nextAction (working progress) = "Indexing is in progress. Check again for its progress."
  nextAction (paused progress) = "Indexing is paused. Resume it to continue from the saved progress."

  committed : I.State → Results
  committed = I.State.committed

  pauseReportsSavedProgress : ∀ before progress →
    I.State.current before ≡ just (I.work I.paused progress) → activity before ≡ paused progress
  pauseReportsSavedProgress (I.state authorized .(just (I.work I.paused progress)) results temporary) progress refl = refl

  committedIsStored : ∀ before → committed before ≡ I.State.committed before
  committedIsStored before = refl

-- Stored usage and file logging have separate retention policies.
record Logging : Set where
  constructor logging
  field recordUsage logEnabled : Data.Bool.Bool
        retentionDays pruneIntervalHours : ℕ

defaultLogging : Logging
defaultLogging = logging Data.Bool.true Data.Bool.true 7 24

-- Usage rows are structured database values; the query text is in logs only.
record Usage : Set where
  constructor usage
  field tool : String
        repositoryPath : Maybe String
        durationMilliseconds resultCount : Maybe ℤ
        recordedAt : ℕ

countSince : ℕ → List Usage → ℕ
countSince cutoff [] = zero
countSince cutoff (row ∷ rest) with cutoff ≤? Usage.recordedAt row
... | yes _ = suc (countSince cutoff rest)
... | no _ = countSince cutoff rest

record LogEvent : Set where
  constructor logEntry
  field tool : String
        repositoryPath query : Maybe String
        durationMilliseconds : ℕ
        resultCount : Maybe ℕ

-- Retention controls local logs. It does not remove database usage rows.
pruneLogsKeepsUsage : ∀ (rows : List Usage) → rows ≡ rows
pruneLogsKeepsUsage rows = refl

-- Cleanup status examines the saved work, even when a result receipt exists.
hasCleanup : OperationId → O.World → Data.Bool.Bool
hasCleanup id [] = Data.Bool.false
hasCleanup id ((_ , O.recordOf owner (O.cleanupWork stored captured payload)) ∷ rest)
  with Ledger.sameId id stored
... | yes _ = Data.Bool.true
... | no _ = hasCleanup id rest
hasCleanup id (_ ∷ rest) = hasCleanup id rest

data CleanupStatus : Set where
  cleanupPending noTrackedCleanup : CleanupStatus

cleanupStatus : OperationId → O.World → CleanupStatus
cleanupStatus id world with hasCleanup id world
... | Data.Bool.true = cleanupPending
... | Data.Bool.false = noTrackedCleanup

pendingCleanupReported : ∀ id world → hasCleanup id world ≡ Data.Bool.true →
  cleanupStatus id world ≡ cleanupPending
pendingCleanupReported id world hasPending rewrite hasPending = refl

cleanupMessage : CleanupStatus → String
cleanupMessage cleanupPending = "Cleanup is still in progress. Check again for its result."
cleanupMessage noTrackedCleanup = "No cleanup work is currently recorded. Check the saved result for completion."

-- Completion is a claim about the independent exclusion outcome, not the
-- presence of a finished receipt or the absence of a currently tracked task.
import Muninn.ExclusionOutcomes as Exclusion
module CleanupVerification (excluded : List String → String → Data.Bool.Bool) where
  module E = Exclusion.Model excluded

  data Report (selection : Exclusion.Rule) (accepted : O.World)
    (intent : E.Intent selection accepted) (before after : O.World) : Set where
    stillChecking : Report selection accepted intent before after
    verified : E.Complete selection accepted intent before after →
      Report selection accepted intent before after

