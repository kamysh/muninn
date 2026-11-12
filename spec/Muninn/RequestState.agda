{-# OPTIONS --safe #-}
-- Durable request identity and the conversation after a repeated request.
module Muninn.RequestState where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.String using (String)
open import Data.Product using (Σ; _,_; proj₁)
open import Data.Unit using (⊤)
import Muninn.Worktree as W
import Muninn.CatalogInputs as C
import Muninn.OperationCatalog as O
import Muninn.Dialogue as D
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)

-- A meaning is the canonical operation together with its complete typed input.
-- Transport adapters normalize into these values; their correspondence is separate.
Id : Set
Id = C.OperationId

data Meaning : Set where
  userMeaning : (intent : C.Intent) → C.IntentInput intent → Meaning
  jobMeaning : (job : C.Job) → C.JobInput job → Meaning

-- Equivalent adapters use the same canonical intent and typed input.
normalized : O.Request → Maybe Meaning
normalized (O.user adapter input) = just (userMeaning (O.canonicalIntent adapter) input)
normalized (O.background job input) = just (jobMeaning job input)
normalized (O.control event input) = nothing

requestId : Meaning → Maybe Id
requestId (userMeaning C.replaceGlobal input) = just (C.Mutation.operationId input)
requestId (userMeaning C.applyPolicy input) = just (C.Mutation.operationId input)
requestId (userMeaning C.register input) = just (C.Mutation.operationId input)
requestId (userMeaning C.start input) = just (C.Mutation.operationId input)
requestId (userMeaning C.reindex input) = just (C.Mutation.operationId input)
requestId (userMeaning C.pause input) = just (C.Mutation.operationId input)
requestId (userMeaning C.resume input) = just (C.Mutation.operationId input)
requestId (userMeaning C.cancel input) = just (C.Mutation.operationId input)
requestId (userMeaning C.unregister input) = just (C.Mutation.operationId input)
requestId (userMeaning C.forget input) = just (C.Mutation.operationId input)
requestId (userMeaning C.recreateIndex input) = just (C.Mutation.operationId input)
requestId (userMeaning C.convertDirectory input) = just (C.Mutation.operationId input)
requestId (userMeaning C.writeNote input) = just (C.Mutation.operationId input)
requestId (userMeaning C.deleteNote input) = just (C.Mutation.operationId input)
requestId (userMeaning C.inspectGlobal input) = nothing
requestId (userMeaning C.inspectPolicy input) = nothing
requestId (userMeaning C.checkPolicy input) = nothing
requestId (userMeaning C.preflight input) = nothing
requestId (userMeaning C.status input) = nothing
requestId (userMeaning C.usage input) = nothing
requestId (userMeaning C.searchStructure input) = nothing
requestId (userMeaning C.searchNotes input) = nothing
requestId (userMeaning C.listNotes input) = nothing
requestId (userMeaning C.continueRequest input) = nothing
requestId (userMeaning (C.searchCode mode) input) = nothing
requestId (jobMeaning C.preparePublic (id , config)) = just id
requestId (jobMeaning C.prepareFamily input) = just (C.FamilyJob.operationId input)
requestId (jobMeaning C.prepareGraph (family , checkout)) = just (C.FamilyJob.operationId family)
requestId (jobMeaning C.fleetScan input) = just (C.FleetJob.operationId input)
requestId (jobMeaning C.discoverCheckouts input) = just (C.FamilyJob.operationId input)
requestId (jobMeaning C.observeCheckout input) = just (C.FamilyJob.operationId (C.CheckoutJob.parent input))
requestId (jobMeaning C.reconcileFamily input) = just (C.FamilyJob.operationId input)
requestId (jobMeaning C.reconcileCheckout input) = just (C.FamilyJob.operationId (C.CheckoutJob.parent input))
requestId (jobMeaning C.watchBatch (family , paths)) = just (C.FamilyJob.operationId family)
requestId (jobMeaning C.analyzeFile input) = just (C.FamilyJob.operationId (C.CheckoutJob.parent (C.FileJob.parent input)))
requestId (jobMeaning C.publishCheckout input) = just (C.FamilyJob.operationId (C.CheckoutJob.parent input))
requestId (jobMeaning C.embedCode (family , version)) = just (C.FamilyJob.operationId family)
requestId (jobMeaning C.embedNote (family , note)) = just (C.FamilyJob.operationId family)
requestId (jobMeaning C.reclaimExcluded input) = just (C.FamilyJob.operationId input)
requestId (jobMeaning C.reclaimRetired input) = just (C.FamilyJob.operationId input)
requestId (jobMeaning C.handoff input) = just (C.FamilyJob.operationId input)
requestId (jobMeaning C.appendLog (id , text)) = just id
requestId (jobMeaning C.pruneLogs (id , duration)) = just id
requestId (jobMeaning C.flushDiagnostics input) = just input

-- Detailed receipts retain a resolved logical owner. The compact used-ID
-- marker carries no owner or request content.
requestOwner : Meaning → Maybe C.Owner
requestOwner (userMeaning C.replaceGlobal input) = just (C.Mutation.owner input)
requestOwner (userMeaning C.applyPolicy input) = just (C.Mutation.owner input)
requestOwner (userMeaning C.register input) = just (C.Mutation.owner input)
requestOwner (userMeaning C.start input) = just (C.Mutation.owner input)
requestOwner (userMeaning C.reindex input) = just (C.Mutation.owner input)
requestOwner (userMeaning C.pause input) = just (C.Mutation.owner input)
requestOwner (userMeaning C.resume input) = just (C.Mutation.owner input)
requestOwner (userMeaning C.cancel input) = just (C.Mutation.owner input)
requestOwner (userMeaning C.unregister input) = just (C.Mutation.owner input)
requestOwner (userMeaning C.forget input) = just (C.Mutation.owner input)
requestOwner (userMeaning C.recreateIndex input) = just (C.Mutation.owner input)
requestOwner (userMeaning C.convertDirectory input) = just (C.Mutation.owner input)
requestOwner (userMeaning C.writeNote input) = just (C.Mutation.owner input)
requestOwner (userMeaning C.deleteNote input) = just (C.Mutation.owner input)
requestOwner (userMeaning C.inspectGlobal input) = nothing
requestOwner (userMeaning C.inspectPolicy input) = nothing
requestOwner (userMeaning C.checkPolicy input) = nothing
requestOwner (userMeaning C.preflight input) = nothing
requestOwner (userMeaning C.status input) = nothing
requestOwner (userMeaning C.usage input) = nothing
requestOwner (userMeaning C.searchStructure input) = nothing
requestOwner (userMeaning C.searchNotes input) = nothing
requestOwner (userMeaning C.listNotes input) = nothing
requestOwner (userMeaning C.continueRequest input) = nothing
requestOwner (userMeaning (C.searchCode mode) input) = nothing
requestOwner (jobMeaning C.preparePublic (id , config)) = just (C.installationOwner)
requestOwner (jobMeaning C.prepareFamily input) = just (C.repositoryOwner (C.FamilyJob.family input))
requestOwner (jobMeaning C.prepareGraph (family , checkout)) = just (C.repositoryOwner (C.FamilyJob.family family))
requestOwner (jobMeaning C.fleetScan input) = just (C.repositoriesOwner (C.FleetJob.families input))
requestOwner (jobMeaning C.discoverCheckouts input) = just (C.repositoryOwner (C.FamilyJob.family input))
requestOwner (jobMeaning C.observeCheckout input) = just (C.repositoryOwner (C.FamilyJob.family (C.CheckoutJob.parent input)))
requestOwner (jobMeaning C.reconcileFamily input) = just (C.repositoryOwner (C.FamilyJob.family input))
requestOwner (jobMeaning C.reconcileCheckout input) = just (C.repositoryOwner (C.FamilyJob.family (C.CheckoutJob.parent input)))
requestOwner (jobMeaning C.watchBatch (family , paths)) = just (C.repositoryOwner (C.FamilyJob.family family))
requestOwner (jobMeaning C.analyzeFile input) = just (C.repositoryOwner (C.FamilyJob.family (C.CheckoutJob.parent (C.FileJob.parent input))))
requestOwner (jobMeaning C.publishCheckout input) = just (C.repositoryOwner (C.FamilyJob.family (C.CheckoutJob.parent input)))
requestOwner (jobMeaning C.embedCode (family , version)) = just (C.repositoryOwner (C.FamilyJob.family family))
requestOwner (jobMeaning C.embedNote (family , note)) = just (C.repositoryOwner (C.FamilyJob.family family))
requestOwner (jobMeaning C.reclaimExcluded input) = just (C.repositoryOwner (C.FamilyJob.family input))
requestOwner (jobMeaning C.reclaimRetired input) = just (C.repositoryOwner (C.FamilyJob.family input))
requestOwner (jobMeaning C.handoff input) = just (C.repositoryOwner (C.FamilyJob.family input))
requestOwner (jobMeaning C.appendLog (id , text)) = just (C.installationOwner)
requestOwner (jobMeaning C.pruneLogs (id , duration)) = just (C.installationOwner)
requestOwner (jobMeaning C.flushDiagnostics input) = just (C.installationOwner)

reindexOwnerMatches : C.ReindexTarget → C.Owner → Set
reindexOwnerMatches (C.foregroundIndex target) owner = owner ≡ C.repositoryOwner (C.FamilyTarget.expectedFamily target)
reindexOwnerMatches (C.detachedIndex target) owner = owner ≡ C.repositoryOwner (C.FamilyTarget.expectedFamily target)
reindexOwnerMatches C.allRegistered owner = Σ (List W.FamilyId) (λ families → owner ≡ C.repositoriesOwner families)

-- The internal owner must agree with the typed target before admission.
-- Registration additionally needs its resolved family binding from #32.
ownerMatches : Meaning → Set
ownerMatches (userMeaning C.replaceGlobal input) = C.Mutation.owner input ≡ (C.installationOwner)
ownerMatches (userMeaning C.applyPolicy input) = C.Mutation.owner input ≡ (C.repositoryOwner (C.FamilyTarget.expectedFamily (C.PolicyTarget.target (proj₁ (C.Mutation.input input)))))
ownerMatches (userMeaning C.start input) = C.Mutation.owner input ≡ (C.repositoryOwner (C.FamilyTarget.expectedFamily (C.PolicyTarget.target (C.Mutation.input input))))
ownerMatches (userMeaning C.reindex input) = reindexOwnerMatches (C.Mutation.input input) (C.Mutation.owner input)
ownerMatches (userMeaning C.pause input) = C.Mutation.owner input ≡ (C.repositoryOwner (C.FamilyTarget.expectedFamily (C.Mutation.input input)))
ownerMatches (userMeaning C.resume input) = C.Mutation.owner input ≡ (C.repositoryOwner (C.FamilyTarget.expectedFamily (C.Mutation.input input)))
ownerMatches (userMeaning C.cancel input) = C.Mutation.owner input ≡ (C.repositoryOwner (C.FamilyTarget.expectedFamily (proj₁ (C.Mutation.input input))))
ownerMatches (userMeaning C.unregister input) = C.Mutation.owner input ≡ (C.repositoryOwner (C.FamilyTarget.expectedFamily (C.Mutation.input input)))
ownerMatches (userMeaning C.forget input) = C.Mutation.owner input ≡ (C.repositoryOwner (C.FamilyTarget.expectedFamily (C.Mutation.input input)))
ownerMatches (userMeaning C.recreateIndex input) = C.Mutation.owner input ≡ (C.repositoryOwner (C.FamilyTarget.expectedFamily (proj₁ (C.Mutation.input input))))
ownerMatches (userMeaning C.convertDirectory input) = C.Mutation.owner input ≡ (C.repositoryOwner (C.FamilyTarget.expectedFamily (C.Mutation.input input)))
ownerMatches (userMeaning C.writeNote input) = C.Mutation.owner input ≡ (C.repositoryOwner (C.FamilyTarget.expectedFamily (C.NoteInput.target (C.Mutation.input input))))
ownerMatches (userMeaning C.deleteNote input) = C.Mutation.owner input ≡ (C.repositoryOwner (C.FamilyTarget.expectedFamily (proj₁ (C.Mutation.input input))))
ownerMatches (userMeaning C.register input) = Σ W.FamilyId (λ family → C.Mutation.owner input ≡ C.repositoryOwner family)
ownerMatches (userMeaning C.inspectGlobal input) = ⊤
ownerMatches (userMeaning C.inspectPolicy input) = ⊤
ownerMatches (userMeaning C.checkPolicy input) = ⊤
ownerMatches (userMeaning C.preflight input) = ⊤
ownerMatches (userMeaning C.status input) = ⊤
ownerMatches (userMeaning C.usage input) = ⊤
ownerMatches (userMeaning C.searchStructure input) = ⊤
ownerMatches (userMeaning C.searchNotes input) = ⊤
ownerMatches (userMeaning C.listNotes input) = ⊤
ownerMatches (userMeaning C.continueRequest input) = ⊤
ownerMatches (userMeaning (C.searchCode mode) input) = ⊤
ownerMatches (jobMeaning job input) = ⊤

-- The list of affected families is receipt ownership, not request content.
-- Its enumeration may differ after a retry and must not change request identity.
canonicalOwner : C.Owner → C.Owner
canonicalOwner (C.repositoriesOwner families) = C.repositoriesOwner []
canonicalOwner owner = owner

canonical : Meaning → Meaning
canonical (userMeaning C.reindex input) = userMeaning C.reindex (record
  { operationId = C.Mutation.operationId input
  ; owner = canonicalOwner (C.Mutation.owner input)
  ; input = C.Mutation.input input })
canonical (userMeaning intent input) = userMeaning intent input
canonical (jobMeaning C.fleetScan input) = jobMeaning C.fleetScan (record
  { operationId = C.FleetJob.operationId input ; families = [] })
canonical (jobMeaning job input) = jobMeaning job input

-- Repository enumeration is not part of the operation submitted by a client.
canonicalFleetOwnership : ∀ first second →
  C.FleetJob.operationId first ≡ C.FleetJob.operationId second →
  canonical (jobMeaning C.fleetScan first) ≡ canonical (jobMeaning C.fleetScan second)
canonicalFleetOwnership first second same rewrite same = refl

canonicalReindexOwnership : ∀ first second families others →
  C.Mutation.operationId first ≡ C.Mutation.operationId second →
  C.Mutation.input first ≡ C.Mutation.input second →
  C.Mutation.owner first ≡ C.repositoriesOwner families →
  C.Mutation.owner second ≡ C.repositoriesOwner others →
  canonical (userMeaning C.reindex first) ≡ canonical (userMeaning C.reindex second)
canonicalReindexOwnership first second families others id input owner₁ owner₂
  rewrite id | input | owner₁ | owner₂ = refl

module Model (Reply : Set)
  (sameId : (a b : Id) → Dec (a ≡ b))
  (sameMeaning : (a b : Meaning) → Dec (canonical a ≡ canonical b)) where

  data Entry : Set where
    active : Meaning → Entry
    completed : Meaning → Reply → Entry
    used : Entry

  entryOwner : Entry → Maybe C.Owner
  entryOwner (active meaning) = requestOwner meaning
  entryOwner (completed meaning result) = requestOwner meaning
  entryOwner used = nothing

  -- Forgetting any family mentioned by a receipt removes the whole detailed
  -- receipt. The used marker retains neither its owner nor its contents.
  belongs : W.FamilyId → C.Owner → Set
  belongs family C.installationOwner = ⊥
  belongs family (C.repositoryOwner target) = family ≡ target
  belongs family (C.repositoriesOwner targets) = family ∈ targets

  member? : ((a b : W.FamilyId) → Dec (a ≡ b)) →
    (family : W.FamilyId) → (targets : List W.FamilyId) → Dec (family ∈ targets)
  member? same family [] = no (λ ())
  member? same family (target ∷ targets) with same family target
  ... | yes equal = yes (here equal)
  ... | no different with member? same family targets
  ...   | yes found = yes (there found)
  ...   | no absent = no λ { (here equal) → different equal ; (there found) → absent found }

  belongs? : ((a b : W.FamilyId) → Dec (a ≡ b)) →
    (family : W.FamilyId) → (owner : C.Owner) → Dec (belongs family owner)
  belongs? same family C.installationOwner = no (λ ())
  belongs? same family (C.repositoryOwner target) = same family target
  belongs? same family (C.repositoriesOwner targets) = member? same family targets

  forgetEntry : ((a b : W.FamilyId) → Dec (a ≡ b)) → W.FamilyId → Entry → Entry
  forgetEntry same family entry with entryOwner entry
  ... | nothing = entry
  ... | just owner with belongs? same family owner
  ...   | yes _ = used
  ...   | no _ = entry

  forgottenReceiptIsMarker : ∀ same family entry owner → entryOwner entry ≡ just owner →
    belongs family owner → forgetEntry same family entry ≡ used
  forgottenReceiptIsMarker same family entry owner owned member with entryOwner entry | owned
  ... | .(just owner) | refl with belongs? same family owner
  ...   | yes _ = refl
  ...   | no absent = ⊥-elim (absent member)

  unrelatedReceiptPreserved : ∀ same family entry owner → entryOwner entry ≡ just owner →
    ¬ belongs family owner → forgetEntry same family entry ≡ entry
  unrelatedReceiptPreserved same family entry owner owned unrelated with entryOwner entry | owned
  ... | .(just owner) | refl with belongs? same family owner
  ...   | yes member = ⊥-elim (unrelated member)
  ...   | no _ = refl

  forgetKeepsUsedMarker : ∀ same family → forgetEntry same family used ≡ used
  forgetKeepsUsedMarker same family = refl

  Ledger : Set
  Ledger = Id → Maybe Entry

  update : Id → Entry → Ledger → Ledger
  update id entry before selected with sameId id selected
  ... | yes _ = just entry
  ... | no _ = before selected

  updateAt : ∀ id entry before → update id entry before id ≡ just entry
  updateAt id entry before with sameId id id
  ... | yes _ = refl
  ... | no distinct = ⊥-elim (distinct refl)

  updateOther : ∀ id entry before other → ¬ (id ≡ other) →
    update id entry before other ≡ before other
  updateOther id entry before other distinct with sameId id other
  ... | yes same = ⊥-elim (distinct same)
  ... | no _ = refl

  -- Mismatch and used-ID outcomes start a corrective conversation.
  data Decision : Set where
    accept continue askForId askForContext idsDiffer askNewId alreadyUsed : Decision
    replay : Reply → Decision

  decide : Meaning → Maybe Entry → Decision
  decide meaning nothing = accept
  decide meaning (just (active original)) with sameMeaning meaning original
  ... | yes _ = continue
  ... | no _ = askNewId
  decide meaning (just (completed original result)) with sameMeaning meaning original
  ... | yes _ = replay result
  ... | no _ = askNewId
  decide meaning (just used) = alreadyUsed

  -- Guidance asks for the missing information rather than ending the task.
  guidanceFor : Decision → Maybe D.Guidance
  guidanceFor askForId = just (D.makeGuidance
    "A request ID is needed to continue this change safely."
    "Provide a request ID for this change." [] (λ ()) (λ ()))
  guidanceFor askForContext = just (D.makeGuidance
    "I do not have the details of this request."
    "Tell me what you want to do, including the relevant details." [] (λ ()) (λ ()))
  guidanceFor idsDiffer = just (D.makeGuidance
    "The request contains two different request IDs."
    "Use the same request ID throughout this request." [] (λ ()) (λ ()))
  guidanceFor askNewId = just (D.makeGuidance
    "This request ID belongs to a different change."
    "Use a new request ID for the new change." [] (λ ()) (λ ()))
  guidanceFor alreadyUsed = just (D.makeGuidance
    "This request ID was used, but its detailed result is no longer available."
    "Check what was already done before submitting a new request with a new ID." [] (λ ()) (λ ()))
  guidanceFor _ = nothing

  -- Missing identity or meaning is resolved in conversation before admission.
  decideRequest : Maybe Id → Maybe Meaning → Ledger → Decision
  decideRequest nothing meaning ledger = askForId
  decideRequest (just id) nothing ledger = askForContext
  decideRequest (just id) (just meaning) ledger with requestId meaning
  ... | nothing = askForId
  ... | just embedded with sameId id embedded
  ...   | no _ = idsDiffer
  ...   | yes _ = decide meaning (ledger id)

  missingIdRequestsContext : ∀ meaning ledger →
    decideRequest nothing meaning ledger ≡ askForId
  missingIdRequestsContext meaning ledger = refl

  repeatActive : ∀ meaning → decide meaning (just (active meaning)) ≡ continue
  repeatActive meaning with sameMeaning meaning meaning
  ... | yes _ = refl
  ... | no distinct = ⊥-elim (distinct refl)

  repeatCompleted : ∀ meaning result →
    decide meaning (just (completed meaning result)) ≡ replay result
  repeatCompleted meaning result with sameMeaning meaning meaning
  ... | yes _ = refl
  ... | no distinct = ⊥-elim (distinct refl)

  changedMeaningAsks : ∀ meaning original result → ¬ (canonical meaning ≡ canonical original) →
    decide meaning (just (completed original result)) ≡ askNewId
  changedMeaningAsks meaning original result distinct with sameMeaning meaning original
  ... | yes same = ⊥-elim (distinct same)
  ... | no _ = refl

  retiredIdAsks : ∀ meaning → decide meaning (just used) ≡ alreadyUsed
  retiredIdAsks meaning = refl

  record State (Data : Set) : Set where
    constructor state
    field dataState : Data
          ledger : Ledger

  -- The generic conversation keeps both task context and the request ledger.
  askAboutRequest : ∀ {Data Task Fact Progress : Set} {id meaning prompt}
    {task : Task} {known : List Fact} {completed : Progress} {world : State Data} →
    guidanceFor (decideRequest id meaning (State.ledger world)) ≡ just prompt →
    D.Step (D.ask prompt) (D.conversation task known completed world D.working)
      (D.conversation task known completed world (D.awaiting prompt))
  askAboutRequest {prompt = prompt} found = D.askStep prompt

  data Event : Set where
    admission : Id → Meaning → Event
    resumption : Id → Meaning → Event
    completion replayRequest : Id → Meaning → Reply → Event
    retirement : Id → Event

  -- The receipt and the operation outcome are committed in one transition.
  -- Each operation still needs its own independent outcome proof.
  data Step {Data : Set} : Event → State Data → State Data → Set where
    admit : ∀ {dataState ledger id meaning owner} → requestId meaning ≡ just id →
      requestOwner meaning ≡ just owner → ownerMatches meaning → ledger id ≡ nothing →
      Step (admission id meaning) (state dataState ledger) (state dataState (update id (active meaning) ledger))
    resume : ∀ {dataState ledger id meaning original} → ledger id ≡ just (active original) →
      canonical meaning ≡ canonical original → Step (resumption id meaning) (state dataState ledger) (state dataState ledger)
    commit : ∀ {before after ledger id meaning result} → ledger id ≡ just (active meaning) →
      Step (completion id meaning result) (state before ledger) (state after (update id (completed meaning result) ledger))
    replayStep : ∀ {dataState ledger id meaning original result} → ledger id ≡ just (completed original result) →
      canonical meaning ≡ canonical original → Step (replayRequest id meaning result) (state dataState ledger) (state dataState ledger)
    retire : ∀ {dataState ledger id meaning result} → ledger id ≡ just (completed meaning result) →
      Step (retirement id) (state dataState ledger) (state dataState (update id used ledger))

  -- Only the latest completed meaning can execute. Earlier context stays
  -- available for the next clarification and cannot revive an old request.
  data Information : Set where
    complete : Meaning → Information
    context : String → Information

  data Authorized : Event → List Information → Set where
    admitKnown : ∀ {id meaning prior} → Authorized (admission id meaning) (complete meaning ∷ prior)
    resumeKnown : ∀ {id meaning prior} → Authorized (resumption id meaning) (complete meaning ∷ prior)
    commitKnown : ∀ {id meaning result prior} → Authorized (completion id meaning result) (complete meaning ∷ prior)
    replayKnown : ∀ {id meaning result prior} → Authorized (replayRequest id meaning result) (complete meaning ∷ prior)

  -- Completion is intentionally absent: each operation must supply its own
  -- transition and independent outcome, rather than arbitrary data changes.
  data SafeEvent : Event → Set where
    safeAdmission : ∀ {id meaning} → SafeEvent (admission id meaning)
    safeResumption : ∀ {id meaning} → SafeEvent (resumption id meaning)
    safeReplay : ∀ {id meaning result} → SafeEvent (replayRequest id meaning result)

  noGenericCompletion : ∀ {id meaning result} → ¬ SafeEvent (completion id meaning result)
  noGenericCompletion ()

  safeStepPreservesData : ∀ {Data : Set} {event} {before after : State Data} →
    SafeEvent event → Step event before after → State.dataState after ≡ State.dataState before
  safeStepPreservesData safeAdmission (admit matching owned ownerValid absent) = refl
  safeStepPreservesData safeResumption (resume receipt same) = refl
  safeStepPreservesData safeReplay (replayStep receipt same) = refl

  data ConversationEvent : Set where
    dialogueEvent : D.Event Information → ConversationEvent
    requestEvent : Event → ConversationEvent

  data ConversationStep {Task Progress Data : Set} : ConversationEvent →
    D.Conversation Task Information Progress (State Data) → D.Conversation Task Information Progress (State Data) → Set where
    dialogueStep : ∀ {event before after} → D.Step event before after →
      ConversationStep (dialogueEvent event) before after
    requestStep : ∀ {event task known completed before after} →
      Authorized event known → SafeEvent event → Step event before after →
      ConversationStep (requestEvent event)
        (D.conversation task known completed before D.working)
        (D.conversation task known completed after D.working)

  awaitingDoesNotChangeRequestState : ∀ {Task Progress Data : Set}
    {event before after prompt} →
    ConversationStep {Task} {Progress} {Data} event before after →
    D.Conversation.phase before ≡ D.awaiting prompt →
    D.Conversation.world after ≡ D.Conversation.world before
  awaitingDoesNotChangeRequestState (dialogueStep step) waiting = D.conversationDoesNotChangeWorld step
  awaitingDoesNotChangeRequestState (requestStep known safe step) ()

  incompleteContextCannotRun : ∀ {Task Progress Data : Set}
    {event task info prior completed world after} →
    ¬ ConversationStep {Task} {Progress} {Data} (requestEvent event)
      (D.conversation task (context info ∷ prior) completed world D.working) after
  incompleteContextCannotRun (requestStep () safe step)

  emptyContextCannotRun : ∀ {Task Progress Data : Set}
    {event task completed world after} →
    ¬ ConversationStep {Task} {Progress} {Data} (requestEvent event)
      (D.conversation task [] completed world D.working) after
  emptyContextCannotRun (requestStep () safe step)

  admissionRequiresMatchingId : ∀ {Data : Set} {before after : State Data} {id meaning} →
    Step (admission id meaning) before after → requestId meaning ≡ just id
  admissionRequiresMatchingId (admit matchingId owned ownerValid absent) = matchingId

  admissionHasOwner : ∀ {Data : Set} {before after : State Data} {id meaning} →
    Step (admission id meaning) before after → Σ C.Owner (λ owner → requestOwner meaning ≡ just owner)
  admissionHasOwner (admit {owner = owner} matching owned ownerValid absent) = owner , owned

  admissionOwnerMatches : ∀ {Data : Set} {before after : State Data} {id meaning} →
    Step (admission id meaning) before after → ownerMatches meaning
  admissionOwnerMatches (admit matching owned ownerValid absent) = ownerValid

  resumePreservesState : ∀ {Data : Set} {before after : State Data} {id meaning} →
    Step (resumption id meaning) before after → after ≡ before
  resumePreservesState (resume receipt same) = refl

  replayPreservesState : ∀ {Data : Set} {before after : State Data} {id meaning result} →
    Step (replayRequest id meaning result) before after → after ≡ before
  replayPreservesState (replayStep receipt same) = refl

  commitKeepsReceipt : ∀ {Data : Set} {before after : State Data} {id meaning result} →
    Step (completion id meaning result) before after →
    State.ledger after id ≡ just (completed meaning result)
  commitKeepsReceipt (commit {ledger = ledger} {id = id} {meaning = meaning} {result = result} activeReceipt) =
    updateAt id (completed meaning result) ledger

  committedCanReplay : ∀ {Data : Set} {before after : State Data} {id meaning result} →
    Step (completion id meaning result) before after →
    Step (replayRequest id meaning result) after after
  committedCanReplay step = replayStep (commitKeepsReceipt step) refl

  replayReturnsSaved : ∀ {Data : Set} {before after : State Data} {id meaning result} →
    Step (replayRequest id meaning result) before after →
    decide meaning (State.ledger before id) ≡ replay result
  replayReturnsSaved {meaning = meaning} {result = result} (replayStep {original = original} receipt same) rewrite receipt
    with sameMeaning meaning original
  ... | yes _ = refl
  ... | no different = ⊥-elim (different same)

  admissionKeepsOther : ∀ {Data : Set} {before after : State Data} {id meaning} →
    Step (admission id meaning) before after → ∀ other → ¬ (id ≡ other) →
    State.ledger after other ≡ State.ledger before other
  admissionKeepsOther (admit {ledger = ledger} {id = id} {meaning = meaning} matchingId owned ownerValid absent) other distinct =
    updateOther id (active meaning) ledger other distinct

  completionKeepsOther : ∀ {Data : Set} {before after : State Data} {id meaning result} →
    Step (completion id meaning result) before after → ∀ other → ¬ (id ≡ other) →
    State.ledger after other ≡ State.ledger before other
  completionKeepsOther (commit {ledger = ledger} {id = id} {meaning = meaning} {result = result} activeReceipt) other distinct =
    updateOther id (completed meaning result) ledger other distinct

  retirementKeepsMarker : ∀ {Data : Set} {before after : State Data} {id} →
    Step (retirement id) before after → State.ledger after id ≡ just used
  retirementKeepsMarker (retire {ledger = ledger} {id = id} receipt) = updateAt id used ledger

  justCannotBeNothing : ∀ {entry : Entry} → ¬ (just entry ≡ nothing)
  justCannotBeNothing ()

  ledgerOwner : Ledger → Id → Maybe C.Owner
  ledgerOwner ledger id with ledger id
  ... | nothing = nothing
  ... | just entry = entryOwner entry

  retirementDropsOwner : ∀ {Data : Set} {before after : State Data} {id} →
    Step (retirement id) before after → ledgerOwner (State.ledger after) id ≡ nothing
  retirementDropsOwner step rewrite retirementKeepsMarker step = refl

  noteAdmissionOwner : ∀ {Data : Set} {before after : State Data} {request} →
    Step (admission (C.Mutation.operationId request) (userMeaning C.writeNote request)) before after →
    C.Mutation.owner request ≡ C.repositoryOwner
      (C.FamilyTarget.expectedFamily (C.NoteInput.target (C.Mutation.input request)))
  noteAdmissionOwner step = admissionOwnerMatches step

  usedIdCannotBeAdmitted : ∀ {Data : Set} {before after : State Data} {id meaning} →
    State.ledger before id ≡ just used → ¬ Step (admission id meaning) before after
  usedIdCannotBeAdmitted found (admit matchingId owned ownerValid absent) = justCannotBeNothing (trans (sym found) absent)

  usedIsNotActive : ∀ {meaning} → ¬ (just used ≡ just (active meaning))
  usedIsNotActive ()

  usedIsNotCompleted : ∀ {meaning result} → ¬ (just used ≡ just (completed meaning result))
  usedIsNotCompleted ()

  usedMarkerPreserved : ∀ {Data : Set} {before after : State Data} {id event} →
    State.ledger before id ≡ just used → Step event before after → State.ledger after id ≡ just used
  usedMarkerPreserved {id = target} found (admit {ledger = ledger} {id = changed} {meaning = meaning} matching owned ownerValid absent)
    with sameId changed target
  ... | yes refl = ⊥-elim (justCannotBeNothing (trans (sym found) absent))
  ... | no distinct = found
  usedMarkerPreserved found (resume receipt same) = found
  usedMarkerPreserved {id = target} found (commit {ledger = ledger} {id = changed} {meaning = meaning} {result = result} receipt)
    with sameId changed target
  ... | yes refl = ⊥-elim (usedIsNotActive (trans (sym found) receipt))
  ... | no distinct = found
  usedMarkerPreserved found (replayStep receipt same) = found
  usedMarkerPreserved {id = target} found (retire {ledger = ledger} {id = changed} receipt)
    with sameId changed target
  ... | yes refl = ⊥-elim (usedIsNotCompleted (trans (sym found) receipt))
  ... | no distinct = found

  data Steps {Data : Set} : State Data → State Data → Set where
    done : ∀ {current} → Steps current current
    more : ∀ {event before middle after} → Step event before middle → Steps middle after → Steps before after

  usedMarkerPermanent : ∀ {Data : Set} {before after : State Data} {id} →
    State.ledger before id ≡ just used → Steps before after → State.ledger after id ≡ just used
  usedMarkerPermanent found done = found
  usedMarkerPermanent found (more first rest) = usedMarkerPermanent (usedMarkerPreserved found first) rest

  completedIsNotActive : ∀ {oldMeaning newMeaning result} →
    ¬ (just (completed oldMeaning result) ≡ just (active newMeaning))
  completedIsNotActive ()

  completedCannotCommitAgain : ∀ {Data : Set} {before after : State Data} {id oldMeaning newMeaning oldResult newResult} →
    State.ledger before id ≡ just (completed oldMeaning oldResult) →
    ¬ Step (completion id newMeaning newResult) before after
  completedCannotCommitAgain found (commit receipt) = completedIsNotActive (trans (sym found) receipt)
