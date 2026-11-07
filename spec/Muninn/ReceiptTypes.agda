{-# OPTIONS --safe #-}
-- Logical receipt data. Physical tables and host-file storage are adapters.
module Muninn.ReceiptTypes where

open import Muninn.CatalogInputs using (OperationId; Mutation; IntentInput)
open import Muninn.RequestIdentity using (Meaning; mutation; durableJob; MutationKind; intent;
  kReplaceGlobal; kApplyPolicy; kRegister; kStart; kReindex; kPause; kResume;
  kCancel; kRemoveIndex; kForget; kRecreateIndex; kConvertDirectory; kWriteNote; kDeleteNote)
open import Data.Nat using (ℕ; suc)
open import Data.List using (List)
open import Data.String using (String)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

mutationId : (kind : MutationKind) → IntentInput (intent kind) → OperationId
mutationId kReplaceGlobal = Mutation.operationId
mutationId kApplyPolicy = Mutation.operationId
mutationId kRegister = Mutation.operationId
mutationId kStart = Mutation.operationId
mutationId kReindex = Mutation.operationId
mutationId kPause = Mutation.operationId
mutationId kResume = Mutation.operationId
mutationId kCancel = Mutation.operationId
mutationId kRemoveIndex = Mutation.operationId
mutationId kForget = Mutation.operationId
mutationId kRecreateIndex = Mutation.operationId
mutationId kConvertDirectory = Mutation.operationId
mutationId kWriteNote = Mutation.operationId
mutationId kDeleteNote = Mutation.operationId

-- Job IDs identify that accepted job; a parent ID inside its payload can differ.
Names : OperationId → Meaning → Set
Names id (mutation kind input) = mutationId kind input ≡ id
Names id (durableJob job input) = ⊤

record Work : Set where
  constructor progressOf
  field generation : ℕ
        versions : List ℕ
        checkpoint : String
open Work public

nextWork : Work → List ℕ → String → Work
nextWork before retained checkpoint = progressOf (suc (generation before)) retained checkpoint

data State (id : OperationId) : Set where
  active : (input : Meaning) → Names id input → Work → State id
  finished : (input : Meaning) → Names id input → String → State id
  used : State id

record Entry : Set where
  constructor entry
  field id : OperationId
        state : State id
open Entry public

request : ∀ {id} → State id → Maybe Meaning
request (active input names progress) = just input
request (finished input names result) = just input
request used = nothing

-- The ID is the ONLY payload left after detailed history is reclaimed.
marker : OperationId → Entry
marker id = entry id used

markerHasNoRequest : ∀ id → request (state (marker id)) ≡ nothing
markerHasNoRequest id = refl

data Transition {id : OperationId} : State id → State id → Set where
  advance : ∀ input names before retained checkpoint →
    Transition (active input names before)
      (active input names (nextWork before retained checkpoint))
  finish : ∀ input names before result →
    Transition (active input names before) (finished input names result)
  reclaim : ∀ input names result → Transition (finished input names result) used
  retain : Transition used used

usedIsPermanent : ∀ {id} {after : State id} → Transition used after → after ≡ used
usedIsPermanent retain = refl

advancePreservesInput : ∀ {id} input (names : Names id input) before retained checkpoint →
  request (active input names (nextWork before retained checkpoint)) ≡ just input
advancePreservesInput input names before retained checkpoint = refl

savedResult : ∀ {id} → State id → Maybe String
savedResult (active input names progress) = nothing
savedResult (finished input names result) = just result
savedResult used = nothing

pendingWork : ∀ {id} → State id → Maybe Work
pendingWork (active input names progress) = just progress
pendingWork (finished input names result) = nothing
pendingWork used = nothing

markerHasNoResultOrWork : ∀ id →
  savedResult (state (marker id)) ≡ nothing ×
  pendingWork (state (marker id)) ≡ nothing
markerHasNoResultOrWork id = refl , refl
