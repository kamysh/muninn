{-# OPTIONS --safe #-}
-- One receipt-first admission gate. Schema/outcome parameters are installed
-- once by the application, not selected by individual handlers.
module Muninn.RequestAdmission where

import Muninn.Catalog as C
import Muninn.CatalogInputs as I
import Muninn.Dialogue as D
import Muninn.IdentityDialogue as Identity
import Muninn.OwnedState as O
import Muninn.ReceiptTypes as R
import Muninn.ReceiptLedger as L
import Muninn.RequestIdentity as N
open import Data.Nat using (ℕ)
open import Data.List using (List; [])
open import Data.String using (String)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥)
import Data.Sum
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

module DB = O.DB

-- This changes only replies, not database semantics or commit boundaries.
mapTransaction : ∀ {A B : Set} → (A → B) → DB.Transaction A → DB.Transaction B
mapTransaction f (DB.commit a) = DB.commit (f a)
mapTransaction f (DB.abort a) = DB.abort (f a)
mapTransaction f (DB.scan next) = DB.scan (λ world → mapTransaction f (next world))
mapTransaction f (DB.read key next) = DB.read key (λ value → mapTransaction f (next value))
mapTransaction f (DB.put key value next) = DB.put key value (mapTransaction f next)
mapTransaction f (DB.remove key next) = DB.remove key (mapTransaction f next)
mapTransaction f (DB.eraseRows count keep next) = DB.eraseRows count keep (mapTransaction f next)

mapEvaluation : ∀ {A B : Set} → (A → B) → DB.Evaluation A → DB.Evaluation B
mapEvaluation f (DB.committed a world) = DB.committed (f a) world
mapEvaluation f (DB.aborted a) = DB.aborted (f a)

evaluationMapping : ∀ {A B} (f : A → B) transaction world →
  DB.evaluate (mapTransaction f transaction) world ≡ mapEvaluation f (DB.evaluate transaction world)
evaluationMapping f (DB.commit a) world = refl
evaluationMapping f (DB.abort a) world = refl
evaluationMapping f (DB.scan next) world = evaluationMapping f (next world) world
evaluationMapping f (DB.read key next) world = evaluationMapping f (next (DB.lookup key world)) world
evaluationMapping f (DB.put key value next) world = evaluationMapping f next (DB.write key value world)
evaluationMapping f (DB.remove key next) world = evaluationMapping f next (DB.delete key world)
evaluationMapping f (DB.eraseRows count keep next) world = evaluationMapping f next (DB.erase count keep world)

executionMapping : ∀ {A B} (f : A → B) transaction world →
  DB.execute (mapTransaction f transaction) world ≡
    (f (proj₁ (DB.execute transaction world)) , proj₂ (DB.execute transaction world))
executionMapping f transaction world rewrite evaluationMapping f transaction world
  with DB.evaluate transaction world
... | DB.committed a after = refl
... | DB.aborted a = refl

record Completed (id : I.OperationId) (subject : N.Meaning) (world : O.World) : Set where
  field slot : ℕ
        owner : O.Owner
        names : R.Names id subject
        result : String
        located : L.find id world ≡ just (L.found slot owner (R.finished subject names result))

justNotNothing : ∀ {A : Set} {a : A} → ¬ (just a ≡ nothing)
justNotNothing ()

completionRequiresReceipt : ∀ {id subject world} → Completed id subject world → ¬ (L.find id world ≡ nothing)
completionRequiresReceipt completed absent =
  justNotNothing (trans (Relation.Binary.PropositionalEquality.sym (Completed.located completed)) absent)

module Protocol
  (Environment : Set)
  (Fields : List String)
  (Prerequisites : N.Meaning → O.World → Environment → Set)
  (Result : N.Meaning → Set)
  (Achieved : (subject : N.Meaning) → O.World → Result subject → Set)
  where

  data Reply : Set where
    ask : Maybe D.Context → D.Prompt → Reply
    ordinary : C.Request → Reply
    acceptedWork : I.OperationId → ℕ → Reply
    knownWork : I.OperationId → N.Meaning → ℕ → R.Work → Reply
    historicalResult : I.OperationId → String → Reply
    allocateSlot : I.OperationId → Reply -- internal allocator continuation

  ledgerReply : D.Context → N.Meaning → L.Reply → Reply
  ledgerReply ctx subject L.fresh = ask (just ctx) (Identity.advicePrompt L.unknownId)
  ledgerReply ctx subject (L.accepted slot) = acceptedWork (D.Context.id ctx) slot
  ledgerReply ctx subject (L.resume slot work) = knownWork (D.Context.id ctx) subject slot work
  ledgerReply ctx subject (L.saved result) = historicalResult (D.Context.id ctx) result
  ledgerReply ctx subject (L.explain advice) = ask (just ctx) (Identity.advicePrompt advice)
  ledgerReply ctx subject L.allocateSlot = allocateSlot (D.Context.id ctx)
  ledgerReply ctx subject (L.continueDialogue slot work guidance) = ask (just ctx) guidance

  module For (id : I.OperationId) (subject : N.Meaning) where
    -- All adapters share the same subject, prerequisites, result and outcome.
    Coherent : D.Context → C.Request → Set
    Coherent ctx request = (N.normalize request ≡ just subject) ×
      ((D.Context.id ctx ≡ id) × R.Names id subject)

    module Review = D.Protocol Environment Fields Coherent
      (λ request → Prerequisites subject)
      (λ request → Result subject)
      (λ request world result → Achieved subject world result × Completed id subject world)

    fromPrerequisites : ∀ ctx world env → D.Context.id ctx ≡ id → R.Names id subject →
      Prerequisites subject world env → Review.Permission ctx world env
    fromPrerequisites ctx world env identity names preconditions = record
      { request = Identity.restore subject
      ; matches = Identity.restorePreservesMeaning subject , (identity , names)
      ; prerequisites = preconditions
      }

    questionRequiresMissingPrerequisite : ∀ ctx world env → D.Context.id ctx ≡ id → R.Names id subject →
      ¬ (Review.Permission ctx world env) → ¬ (Prerequisites subject world env)
    questionRequiresMissingPrerequisite ctx world env identity names blocked prerequisites =
      blocked (fromPrerequisites ctx world env identity names prerequisites)

    permissionRequiresIdentity : ∀ ctx world env → Review.Permission ctx world env →
      (D.Context.id ctx ≡ id) × R.Names id subject
    permissionRequiresIdentity ctx world env permission = proj₂ (Review.Permission.matches permission)

    answerRequiresOutcomeAndReceipt : ∀ ctx world (answer : Review.Answer ctx world) →
      Achieved subject world (Review.Answer.result answer) × Completed id subject world
    answerRequiresOutcomeAndReceipt ctx world answer = Review.Answer.achieved answer

    -- Receipt lookup precedes the checker. A completed answer without a
    -- recorded ID is uninhabited, even if its user-visible goal already holds.
    -- That case must still arrange durable completion through the operation.
    beginSnapshot : ∀ ctx → D.Context.id ctx ≡ id → R.Names id subject → Review.Checker →
      Environment → ℕ → O.Owner → R.Work → O.World → DB.Transaction Reply
    beginSnapshot ctx identity names checker env slot owner initial world with L.find id world
    ... | just value = DB.commit (ledgerReply ctx subject (L.existing subject value))
    ... | nothing with Review.Checker.assess checker ctx world env
    ...   | Review.ready permission = mapTransaction (ledgerReply ctx subject)
      (L.acceptSnapshot id subject names slot owner initial world)
    ...   | Review.done answer = DB.commit
      (historicalResult id (Completed.result (proj₂ (Review.Answer.achieved answer))))
    ...   | Review.needs blocked query = DB.commit (ask (just ctx) (D.questionPrompt query))

    begin : ∀ ctx → D.Context.id ctx ≡ id → R.Names id subject → Review.Checker →
      Environment → ℕ → O.Owner → R.Work → DB.Transaction Reply
    begin ctx identity names checker env slot owner initial =
      DB.scan (beginSnapshot ctx identity names checker env slot owner initial)

    receiptPrecedesReassessment : ∀ ctx identity names checker env slot owner initial world value →
      L.find id world ≡ just value →
      DB.execute (begin ctx identity names checker env slot owner initial) world ≡
        (ledgerReply ctx subject (L.existing subject value) , world)
    receiptPrecedesReassessment ctx identity names checker env slot owner initial world value foundHere
      rewrite foundHere = refl

    cachedCompletionRequiresReceipt : ∀ ctx world → Review.Answer ctx world → ¬ (L.find id world ≡ nothing)
    cachedCompletionRequiresReceipt ctx world answer =
      completionRequiresReceipt (proj₂ (Review.Answer.achieved answer))

    pendingQuestionKeepsWorld : ∀ ctx identity names checker env slot owner initial world blocked query →
      L.find id world ≡ nothing →
      Review.Checker.assess checker ctx world env ≡ Review.needs blocked query →
      DB.execute (begin ctx identity names checker env slot owner initial) world ≡
        (ask (just ctx) (D.questionPrompt query) , world)
    pendingQuestionKeepsWorld ctx identity names checker env slot owner initial world blocked query absent assessed
      rewrite absent | assessed = refl

    acceptanceUsesSharedTransaction : ∀ ctx identity names checker env slot owner initial world permission →
      L.find id world ≡ nothing →
      Review.Checker.assess checker ctx world env ≡ Review.ready permission →
      DB.execute (begin ctx identity names checker env slot owner initial) world ≡
        (ledgerReply ctx subject (proj₁ (DB.execute (L.accept id subject names slot owner initial) world)) ,
          proj₂ (DB.execute (L.accept id subject names slot owner initial) world))
    acceptanceUsesSharedTransaction ctx identity names checker env slot owner initial world permission absent assessed
      rewrite absent | assessed | absent with DB.lookup slot world
    ... | nothing = refl
    ... | just stored = refl

    dialogueKeepsAcceptedState : ∀ {before after env₀ env₁}
      {first : Review.Phase before env₀} {second : Review.Phase after env₁} →
      Review.Step first second → before ≡ after
    dialogueKeepsAcceptedState = Review.preservesOwnedWorld

  Checkers : Set
  Checkers = ∀ id subject → For.Review.Checker id subject

  respond : Checkers → Environment → ℕ → O.Owner → R.Work →
    Identity.Response → O.World → DB.Transaction Reply
  respond checkers env slot owner initial (Identity.contextQuestion guidance) world = DB.commit (ask nothing guidance)
  respond checkers env slot owner initial (Identity.ordinaryWithoutContext request) world = DB.commit (ordinary request)
  respond checkers env slot owner initial (Identity.within ctx (Identity.question guidance)) world =
    DB.commit (ask (just ctx) guidance)
  respond checkers env slot owner initial (Identity.within ctx (Identity.ordinary request)) world = DB.commit (ordinary request)
  respond checkers env slot owner initial (Identity.within ctx (Identity.historicalResult result)) world =
    DB.commit (historicalResult (D.Context.id ctx) result)
  respond checkers env slot owner initial (Identity.within ctx (Identity.knownWork selected key previousOwner work)) world =
    DB.commit (knownWork (D.Context.id ctx) (Identity.subject selected) key work)
  respond checkers env slot owner initial (Identity.within ctx (Identity.newRequest selected)) world =
    For.beginSnapshot (D.Context.id ctx) (Identity.subject selected) ctx refl (Identity.names selected)
      (checkers (D.Context.id ctx) (Identity.subject selected)) env slot owner initial world

  -- Routing is INSIDE the transaction. Unidentified, changed-input and
  -- historical requests cannot reach fresh admission.
  interact : Checkers → Identity.Turn → Environment → ℕ → O.Owner → R.Work → DB.Transaction Reply
  interact checkers inputTurn env slot owner initial =
    DB.scan (λ world → respond checkers env slot owner initial (Identity.route inputTurn world) world)

  missingContextCannotWrite : ∀ checkers statement env slot owner initial world →
    DB.execute (interact checkers (Identity.turn nothing Identity.continueCurrent statement) env slot owner initial) world ≡
      (ask nothing (D.prompt D.lostExplanation D.lostAction []) , world)
  missingContextCannotWrite checkers statement env slot owner initial world = refl

  missingJobIdentityCannotWrite : ∀ checkers job input statement env slot owner initial world →
    DB.execute (interact checkers (Identity.turn nothing (Identity.submission (C.background job input)) statement) env slot owner initial) world ≡
      (ask nothing Identity.identityPrompt , world)
  missingJobIdentityCannotWrite checkers job input statement env slot owner initial world = refl

  routedQuestionCannotWrite : ∀ checkers inputTurn env slot owner initial world ctx guidance →
    Identity.route inputTurn world ≡ Identity.within ctx (Identity.question guidance) →
    DB.execute (interact checkers inputTurn env slot owner initial) world ≡ (ask (just ctx) guidance , world)
  routedQuestionCannotWrite checkers inputTurn env slot owner initial world ctx guidance routed
    rewrite routed = refl

  savedResultIsHistorical : ∀ checkers inputTurn env slot owner initial world ctx result →
    Identity.route inputTurn world ≡ Identity.within ctx (Identity.historicalResult result) →
    DB.execute (interact checkers inputTurn env slot owner initial) world ≡
      (historicalResult (D.Context.id ctx) result , world)
  savedResultIsHistorical checkers inputTurn env slot owner initial world ctx result routed
    rewrite routed = refl

  knownWorkIsReused : ∀ checkers inputTurn env slot owner initial world ctx selected key oldOwner work →
    Identity.route inputTurn world ≡ Identity.within ctx (Identity.knownWork selected key oldOwner work) →
    DB.execute (interact checkers inputTurn env slot owner initial) world ≡
      (knownWork (D.Context.id ctx) (Identity.subject selected) key work , world)
  knownWorkIsReused checkers inputTurn env slot owner initial world ctx selected key oldOwner work routed
    rewrite routed = refl

  lostReplyDoesNotCreateNewWork : ∀ checkers id original names previousSlot previousOwner work statement
    env proposedSlot proposedOwner initial world →
    DB.execute (interact checkers
      (Identity.turn nothing (Identity.submission (C.user C.conversationContinuation id)) statement)
      env proposedSlot proposedOwner initial)
      (DB.write previousSlot (L.recordAt previousOwner (R.active original names work)) world) ≡
        (knownWork id original previousSlot work ,
          DB.write previousSlot (L.recordAt previousOwner (R.active original names work)) world)
  lostReplyDoesNotCreateNewWork checkers id original names previousSlot previousOwner work statement
    env proposedSlot proposedOwner initial world =
    knownWorkIsReused checkers
      (Identity.turn nothing (Identity.submission (C.user C.conversationContinuation id)) statement)
      env proposedSlot proposedOwner initial
      (DB.write previousSlot (L.recordAt previousOwner (R.active original names work)) world)
      (D.fresh id statement) (Identity.restoredTarget (D.fresh id statement) original names)
      previousSlot previousOwner work
      (Identity.continuationRecoversWorkAfterContextLoss id original names previousSlot previousOwner work statement
        (DB.write previousSlot (L.recordAt previousOwner (R.active original names work)) world)
        (L.writtenReceiptVisible id previousSlot previousOwner (R.active original names work) world))

  interactionCrashBoundary : ∀ checkers inputTurn env slot owner initial before after →
    O.Execution.Interrupted
      (O.Execution.atomic (interact checkers inputTurn env slot owner initial) O.Execution.done) before after →
    (after ≡ before) Data.Sum.⊎
      (after ≡ proj₂ (DB.execute (interact checkers inputTurn env slot owner initial) before))
  interactionCrashBoundary checkers inputTurn env slot owner initial =
    L.atomicBoundary (interact checkers inputTurn env slot owner initial)

  incompleteRequestCannotWrite : ∀ checkers available query statement env slot owner initial world →
    DB.execute (interact checkers (Identity.turn available (Identity.incomplete query) statement)
      env slot owner initial) world ≡ (ask available (D.questionPrompt query) , world)
  incompleteRequestCannotWrite checkers nothing query statement env slot owner initial world = refl
  incompleteRequestCannotWrite checkers (just ctx) query statement env slot owner initial world = refl
