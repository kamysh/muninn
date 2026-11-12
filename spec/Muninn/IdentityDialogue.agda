{-# OPTIONS --safe #-}
-- Recover known identity and input before any fresh admission or write.
module Muninn.IdentityDialogue where

import Muninn.Catalog as C
import Muninn.CatalogInputs as I
import Muninn.Dialogue as D
import Muninn.OwnedState as O
import Muninn.ReceiptTypes as R
import Muninn.ReceiptLedger as L
import Muninn.RequestIdentity as N
open import Data.Nat using (ℕ)
open import Data.List using ([])
open import Data.String using (String)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (tt)
import Data.Empty
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst)

-- A restored request uses an internal catalog adapter, never an invented wire
-- name. Its NORMALIZED meaning, including all input values, is unchanged.
restore : N.Meaning → C.Request
restore (N.mutation N.kReplaceGlobal input) = C.user (C.cliAdapter C.initAssignments) input
restore (N.mutation N.kApplyPolicy input) = C.user (C.plannedAdministration C.apply) input
restore (N.mutation N.kRegister input) = C.user (C.plannedAdministration C.registerFamily) input
restore (N.mutation N.kStart input) = C.user (C.plannedAdministration C.startFamily) input
restore (N.mutation N.kReindex input) = C.user (C.plannedAdministration C.reindexFamily) input
restore (N.mutation N.kPause input) = C.user (C.plannedAdministration C.pauseFamily) input
restore (N.mutation N.kResume input) = C.user (C.plannedAdministration C.resumeFamily) input
restore (N.mutation N.kCancel input) = C.user (C.plannedAdministration C.cancelWork) input
restore (N.mutation N.kRemoveIndex input) = C.user (C.plannedAdministration C.removeDerived) input
restore (N.mutation N.kForget input) = C.user (C.plannedAdministration C.forgetRepository) input
restore (N.mutation N.kRecreateIndex input) = C.user (C.plannedAdministration C.recreateDerived) input
restore (N.mutation N.kConvertDirectory input) = C.user (C.plannedAdministration C.convert) input
restore (N.mutation N.kWriteNote input) = C.user (C.mcpAdapter C.recordKnowledge) input
restore (N.mutation N.kDeleteNote input) = C.user (C.mcpAdapter C.deleteKnowledge) input
restore (N.durableJob job input) = C.background job input

restorePreservesMeaning : ∀ subject → N.normalize (restore subject) ≡ just subject
restorePreservesMeaning (N.mutation N.kReplaceGlobal input) = refl
restorePreservesMeaning (N.mutation N.kApplyPolicy input) = refl
restorePreservesMeaning (N.mutation N.kRegister input) = refl
restorePreservesMeaning (N.mutation N.kStart input) = refl
restorePreservesMeaning (N.mutation N.kReindex input) = refl
restorePreservesMeaning (N.mutation N.kPause input) = refl
restorePreservesMeaning (N.mutation N.kResume input) = refl
restorePreservesMeaning (N.mutation N.kCancel input) = refl
restorePreservesMeaning (N.mutation N.kRemoveIndex input) = refl
restorePreservesMeaning (N.mutation N.kForget input) = refl
restorePreservesMeaning (N.mutation N.kRecreateIndex input) = refl
restorePreservesMeaning (N.mutation N.kConvertDirectory input) = refl
restorePreservesMeaning (N.mutation N.kWriteNote input) = refl
restorePreservesMeaning (N.mutation N.kDeleteNote input) = refl
restorePreservesMeaning (N.durableJob job input) = refl

record Target (ctx : D.Context) : Set where
  constructor target
  field request : C.Request
        subject : N.Meaning
        normalized : N.normalize request ≡ just subject
        names : R.Names (D.Context.id ctx) subject
open Target public

restoredTarget : ∀ ctx subject → R.Names (D.Context.id ctx) subject → Target ctx
restoredTarget ctx subject names = target (restore subject) subject (restorePreservesMeaning subject) names

bindName : ∀ id subject → Maybe (R.Names id subject)
bindName id (N.mutation kind input) with L.sameId (R.mutationId kind input) id
... | yes same = just same
... | no _ = nothing
bindName id (N.durableJob job input) = just tt

-- Continuation carries identity without resubmitting a new mutation payload.
continuationInput : (intent : I.Intent) → I.IntentInput intent → Maybe I.OperationId
continuationInput I.continueRequest id = just id
continuationInput _ _ = nothing

continuationId : C.Request → Maybe I.OperationId
continuationId (C.user adapter input) = continuationInput (C.canonicalIntent adapter) input
continuationId (C.background job input) = nothing
continuationId (C.control event input) = nothing
continuationId (C.localUi input) = nothing

automaticId : C.Request → Maybe I.OperationId
automaticId request with N.normalize request
... | just (N.mutation kind input) = just (R.mutationId kind input)
... | just (N.durableJob job input) = nothing -- parent job ID is NOT this job's ID
... | nothing = continuationId request

identityPrompt : D.Prompt
identityPrompt = D.prompt
  (D.text 'I' " need the request ID before I can change anything.")
  (D.text 'P' "rovide the ID from the earlier attempt, or a new ID if this is a new operation.") []

conflictingIdentity : D.Prompt
conflictingIdentity = D.prompt
  (D.text 'T' "his request uses a different ID from the conversation we are continuing. The existing work is unchanged.")
  (D.text 'C' "larify which operation you want to continue. Start a separate request with a new ID for a new operation.") []

advicePrompt : L.Advice → D.Prompt
advicePrompt L.differentRequest = D.prompt
  (D.text 'T' "his ID belongs to a different request. The original work is unchanged.")
  (D.text 'U' "se a new ID for the new request.") []
advicePrompt L.historyReclaimed = D.prompt
  (D.text 'T' "his ID was already used. Its detailed result is no longer retained, so it will not run again.")
  (D.text 'I' "nspect the current state before deciding whether another operation is needed.") []
advicePrompt L.unknownId = D.prompt
  (D.text 'I' " cannot find saved work for this ID.")
  (D.text 'D' "escribe what you were trying to do, including the repository and intended change, so we can continue.") []

data View (ctx : D.Context) : Set where
  newRequest : Target ctx → View ctx
  knownWork : Target ctx → ℕ → O.Owner → R.Work → View ctx
  historicalResult : String → View ctx
  question : D.Prompt → View ctx
  ordinary : C.Request → View ctx

observeExisting : ∀ ctx → Target ctx → L.Found (D.Context.id ctx) → View ctx
observeExisting ctx selected (L.found slot owner (R.active original names work))
  with N.sameRequest (subject selected) original
... | yes _ = knownWork (restoredTarget ctx original names) slot owner work
... | no _ = question (advicePrompt L.differentRequest)
observeExisting ctx selected (L.found slot owner (R.finished original names result))
  with N.sameRequest (subject selected) original
... | yes _ = historicalResult result
... | no _ = question (advicePrompt L.differentRequest)
observeExisting ctx selected (L.found slot owner R.used) = question (advicePrompt L.historyReclaimed)

observeBound : ∀ ctx → Target ctx → O.World → View ctx
observeBound ctx selected world with L.find (D.Context.id ctx) world
... | nothing = newRequest selected
... | just value = observeExisting ctx selected value

observeSaved : ∀ ctx → O.World → View ctx
observeSaved ctx world with L.find (D.Context.id ctx) world
... | nothing = question (advicePrompt L.unknownId)
... | just (L.found slot owner (R.active original names work)) =
  knownWork (restoredTarget ctx original names) slot owner work
... | just (L.found slot owner (R.finished original names result)) = historicalResult result
... | just (L.found slot owner R.used) = question (advicePrompt L.historyReclaimed)

-- Incomplete input is NOT an implicit continuation of an older operation.
data Candidate : Set where
  submission : C.Request → Candidate
  continueCurrent : Candidate
  incomplete : D.Question → Candidate

observe : ∀ ctx → Candidate → O.World → View ctx
observe ctx continueCurrent world = observeSaved ctx world
observe ctx (incomplete query) world = question (D.questionPrompt query)
observe ctx (submission request) world with continuationId request
... | just id with L.sameId id (D.Context.id ctx)
...   | yes _ = observeSaved ctx world
...   | no _ = question conflictingIdentity
observe ctx (submission request) world | nothing with N.normalize request in normalized
... | nothing = ordinary request
... | just subject with bindName (D.Context.id ctx) subject
...   | nothing = question conflictingIdentity
...   | just names = observeBound ctx (target request subject normalized names) world

record Turn : Set where
  constructor turn
  field available : Maybe D.Context
        candidate : Candidate
        statement : String
open Turn public

data Response : Set where
  within : (ctx : D.Context) → View ctx → Response
  contextQuestion : D.Prompt → Response
  ordinaryWithoutContext : C.Request → Response

route : Turn → O.World → Response
route (turn (just ctx) candidate statement) world = within ctx (observe ctx candidate world)
route (turn nothing continueCurrent statement) world = contextQuestion (D.prompt D.lostExplanation D.lostAction [])
route (turn nothing (incomplete query) statement) world = contextQuestion (D.questionPrompt query)
route (turn nothing (submission request) statement) world with automaticId request
... | just id = within (D.fresh id statement) (observe (D.fresh id statement) (submission request) world)
... | nothing with N.normalize request
...   | nothing = ordinaryWithoutContext request
...   | just subject = contextQuestion identityPrompt

contextOf : Response → Maybe D.Context
contextOf (within ctx view) = just ctx
contextOf (contextQuestion guidance) = nothing
contextOf (ordinaryWithoutContext request) = nothing

knownContextIsReused : ∀ ctx candidate statement world →
  contextOf (route (turn (just ctx) candidate statement) world) ≡ just ctx
knownContextIsReused ctx candidate statement world = refl

correctionKeepsBinding : ∀ ctx updates subject → R.Names (D.Context.id ctx) subject →
  R.Names (D.Context.id (D.repairMany updates ctx)) subject
correctionKeepsBinding ctx updates subject names =
  subst (λ id → R.Names id subject) (sym (D.repairManyKeepsIdentity updates ctx)) names

knownInputIsRecovered : ∀ ctx world slot owner original names work →
  L.find (D.Context.id ctx) world ≡ just (L.found slot owner (R.active original names work)) →
  observeSaved ctx world ≡ knownWork (restoredTarget ctx original names) slot owner work
knownInputIsRecovered ctx world slot owner original names work foundHere rewrite foundHere = refl

knownResultIsReplayed : ∀ ctx world slot owner original names result →
  L.find (D.Context.id ctx) world ≡ just (L.found slot owner (R.finished original names result)) →
  observeSaved ctx world ≡ historicalResult result
knownResultIsReplayed ctx world slot owner original names result foundHere rewrite foundHere = refl

newInputCannotReplaceWork : ∀ ctx selected slot owner original names work →
  subject selected ≢ original →
  observeExisting ctx selected (L.found slot owner (R.active original names work)) ≡
    question (advicePrompt L.differentRequest)
newInputCannotReplaceWork ctx selected slot owner original names work different
  with N.sameRequest (subject selected) original
... | yes same = Data.Empty.⊥-elim (different same)
... | no _ = refl

continuationRecoversWorkAfterContextLoss : ∀ id original names slot owner work statement world →
  L.find id world ≡ just (L.found slot owner (R.active original names work)) →
  route (turn nothing (submission (C.user C.conversationContinuation id)) statement) world ≡
    within (D.fresh id statement)
      (knownWork (restoredTarget (D.fresh id statement) original names) slot owner work)
continuationRecoversWorkAfterContextLoss id original names slot owner work statement world foundHere
  with L.sameId id id
... | yes _ rewrite foundHere = refl
... | no different = Data.Empty.⊥-elim (different refl)

continuationRecoversResultAfterContextLoss : ∀ id original names slot owner result statement world →
  L.find id world ≡ just (L.found slot owner (R.finished original names result)) →
  route (turn nothing (submission (C.user C.conversationContinuation id)) statement) world ≡
    within (D.fresh id statement) (historicalResult result)
continuationRecoversResultAfterContextLoss id original names slot owner result statement world foundHere
  with L.sameId id id
... | yes _ rewrite foundHere = refl
... | no different = Data.Empty.⊥-elim (different refl)
