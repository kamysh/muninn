{-# OPTIONS --safe #-}
-- Status is derived from the saved receipt, not inferred from a request.
module Muninn.StatusReport where

import Muninn.OwnedState as O
import Muninn.ReceiptLedger as Ledger
import Muninn.ReceiptTypes as Receipt
import Muninn.WorkQueue as Queue
import Muninn.RequestIdentity as Identity
open import Muninn.CatalogInputs using (OperationId)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₂)
open import Data.Empty using (⊥-elim)
open import Data.String using (String)
open import Data.Nat using (ℕ)
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

-- Work phases come from a stored accepted-work record at the observed slot.
workAt : ℕ → O.World → Maybe Queue.Info
workAt slot world with O.DB.lookup slot world
... | just (O.recordOf owner (O.acceptedWork versions info)) = just info
... | _ = nothing

workFromRecord : ∀ slot world owner versions info →
  O.DB.lookup slot world ≡ just (O.recordOf owner (O.acceptedWork versions info)) →
  workAt slot world ≡ just info
workFromRecord slot world owner versions info found rewrite found = refl

workMessage : Queue.Phase → String
workMessage Queue.queued = "This work is waiting for its turn."
workMessage Queue.running = "This work is in progress."
workMessage Queue.paused = "This work is paused. Resume it when you are ready."

-- Coverage and cleanup claims use the same evidence as the operations.
import Muninn.ExclusionOutcomes as Exclusion
import Muninn.CleanupCompletion as Cleanup
import Muninn.StagedVectors as Vectors
import Muninn.Worktree as Worktree
import Muninn.VectorData as Vector
import Muninn.FiniteClosure as Finite
open import Relation.Nullary using (¬_; yes; no)

module CleanupReport (selection : Exclusion.Rule) (accepted : O.World)
  (intent : Exclusion.Model.Intent selection accepted) where
  module Check = Cleanup.Model.Contract selection accepted intent
  noCompletionWhilePending : ∀ key world → Check.Pending key world →
    ¬ Exclusion.Model.Complete selection accepted intent world world
  noCompletionWhilePending = Check.pendingExcludesComplete

  data Assessment (world : O.World) : Set where
    unfinished : (key : ℕ) → Check.Pending key world → Assessment world
    complete : Exclusion.Model.Complete selection accepted intent world world → Assessment world

  assess : ∀ world → O.Unique world → Assessment world
  assess world unique with Finite.choose (λ key → Check.Pending key world)
    (λ key → Check.pending? key world) (Exclusion.Model.Intent.keys intent)
  ... | yes (key , captured , pending) = unfinished key pending
  ... | no none = complete (Check.completeWithoutPending world unique
    (λ key pending → none (key , Check.pendingCaptured key world pending , pending)))

module VectorReport (selection : Exclusion.Rule) (profile : Worktree.EmbeddingKey) where
  module Check = Vectors.Family selection profile
  reportedUsableRequiresStoredVector : ∀ world chunk text →
    Check.availability world chunk text ≡ Vectors.usable →
    Σ Vector.Value (λ saved → Check.linkedReady world chunk text ≡ just saved)
  reportedUsableRequiresStoredVector = Check.usableRequiresStoredVector

  -- A waiting report carries the saved explanation for the exact item; a
  -- pending report never presents a cached vector as coverage for this item.
  data Coverage (world : O.World) (chunk : ℕ) (text : String) : Set where
    ready : (saved : Vector.Value) → Check.linkedReady world chunk text ≡ just saved → Coverage world chunk text
    waiting : (why : Vector.Guidance) → Check.linkedReady world chunk text ≡ nothing →
      Check.guidance world chunk text ≡ just why → Coverage world chunk text
    pending : Check.linkedReady world chunk text ≡ nothing → Check.guidance world chunk text ≡ nothing → Coverage world chunk text

  assess : ∀ world chunk text → Coverage world chunk text
  assess world chunk text with Check.linkedReady world chunk text in found
  ... | just saved = ready saved found
  ... | nothing with Check.guidance world chunk text in explanation
  ...   | just why = waiting why found explanation
  ...   | nothing = pending found explanation
