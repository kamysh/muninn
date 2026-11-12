{-# OPTIONS --safe #-}
-- Note writes and deletes share the request receipt with their state change.
module Muninn.NoteRequests where

import Muninn.CatalogInputs as C
import Muninn.KnowledgeState as K
import Muninn.RequestState as Requests
import Muninn.Dialogue as D
import Muninn.Worktree as W
open import Muninn.Knowledge using (KnowledgeId; KnowledgeItem; ValidKnowledgeItem)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (_∷_)
open import Data.Maybe.Properties using (just-injective)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (Dec; ¬_)

record RepositoryWorld (Other : Set) : Set where
  field notes : K.World
        locations : C.Locator → Maybe W.Checkout
        other : Other

record Resolved {Other : Set} (world : RepositoryWorld Other) (target : C.FamilyTarget) : Set where
  field checkout : W.Checkout
        located : RepositoryWorld.locations world (C.FamilyTarget.location target) ≡ just checkout
        familyMatches : W.Checkout.family checkout ≡ C.FamilyTarget.expectedFamily target

noteFrom : (input : C.NoteInput) (id : KnowledgeId) →
  K.Note (C.FamilyTarget.expectedFamily (C.NoteInput.target input)) id
noteFrom input id = record
  { item = record
      { id = id
      ; family = C.FamilyTarget.expectedFamily (C.NoteInput.target input)
      ; origin = C.NoteInput.origin input
      ; title = C.NoteInput.title input
      ; body = C.NoteInput.body input
      ; tags = C.NoteInput.tags input
      ; relatedFiles = C.NoteInput.relatedFiles input }
  ; familyMatches = refl
  ; idMatches = refl
  ; scope = C.NoteInput.scope input }

data Reply (OtherReply : Set) : Set where
  saved deleted : KnowledgeId → Reply OtherReply
  otherReply : OtherReply → Reply OtherReply

module For (Other OtherReply : Set)
  (sameFamily : (a b : W.FamilyId) → Dec (a ≡ b))
  (sameNote : (a b : KnowledgeId) → Dec (a ≡ b))
  (sameRequest : (a b : Requests.Id) → Dec (a ≡ b))
  (sameMeaning : (a b : Requests.Meaning) → Dec (a ≡ b)) where

  module Notes = K.Operations sameFamily sameNote
  module R = Requests.Model (Reply OtherReply) sameRequest sameMeaning

  -- An automatically assigned ID must be fresh. An explicit existing ID
  -- may be changed only from a checkout where the old note is visible.
  data WriteAllowed (world : RepositoryWorld Other) (input : C.NoteInput)
    (resolved : Resolved world (C.NoteInput.target input)) (id : KnowledgeId) : Set where
    generated : C.NoteInput.id input ≡ nothing →
      (∀ family → K.World.notes (RepositoryWorld.notes world) family id ≡ nothing) →
      WriteAllowed world input resolved id
    explicitNew : C.NoteInput.id input ≡ just id →
      (∀ family → K.World.notes (RepositoryWorld.notes world) family id ≡ nothing) →
      WriteAllowed world input resolved id
    explicitExisting : ∀ {old} → C.NoteInput.id input ≡ just id →
      K.World.notes (RepositoryWorld.notes world) (C.FamilyTarget.expectedFamily (C.NoteInput.target input)) id ≡ just old →
      K.Visible old (Resolved.checkout resolved) → WriteAllowed world input resolved id

  existingWriteVisible : ∀ {world input resolved id old} →
    WriteAllowed world input resolved id →
    K.World.notes (RepositoryWorld.notes world) (C.FamilyTarget.expectedFamily (C.NoteInput.target input)) id ≡ just old →
    K.Visible old (Resolved.checkout resolved)
  existingWriteVisible {input = input} (generated inputId absent) present =
    ⊥-elim (K.justNotNothing (trans (sym present) (absent (C.FamilyTarget.expectedFamily (C.NoteInput.target input)))))
  existingWriteVisible {input = input} (explicitNew inputId absent) present =
    ⊥-elim (K.justNotNothing (trans (sym present) (absent (C.FamilyTarget.expectedFamily (C.NoteInput.target input)))))
  existingWriteVisible {resolved = resolved} (explicitExisting inputId found visible) present =
    subst (λ note → K.Visible note (Resolved.checkout resolved)) (just-injective (trans (sym found) present)) visible

  scopedUnavailable : ∀ {world : RepositoryWorld Other} {target} (resolved : Resolved world target) {noteId}
    (note : K.Note (C.FamilyTarget.expectedFamily target) noteId) selected checkout →
    K.Note.scope note ≡ just selected →
    RepositoryWorld.locations world (C.FamilyTarget.location target) ≡ just checkout →
    ¬ (W.Checkout.id checkout ≡ selected) → ¬ K.Visible note (Resolved.checkout resolved)
  scopedUnavailable resolved note selected checkout scoped location distinct visible =
    K.scopedNoteNotVisibleElsewhere note (Resolved.checkout resolved) selected scoped
      (λ same → distinct (trans (sym (cong W.Checkout.id (just-injective (trans (sym (Resolved.located resolved)) location)))) same)) visible

  replaceNotes : RepositoryWorld Other → K.World → RepositoryWorld Other
  replaceNotes before after = record
    { notes = after
    ; locations = RepositoryWorld.locations before
    ; other = RepositoryWorld.other before }

  writeMeaning : C.Mutation C.NoteInput → Requests.Meaning
  writeMeaning request = Requests.userMeaning C.writeNote request

  deleteMeaning : C.Mutation (C.FamilyTarget × KnowledgeId) → Requests.Meaning
  deleteMeaning request = Requests.userMeaning C.deleteNote request

  data Step : R.Event → R.State (RepositoryWorld Other) → R.State (RepositoryWorld Other) → Set where
    write : ∀ {before ledger request id} →
      (resolved : Resolved before (C.NoteInput.target (C.Mutation.input request))) →
      WriteAllowed before (C.Mutation.input request) resolved id →
      ValidKnowledgeItem (K.Note.item (noteFrom (C.Mutation.input request) id)) →
      K.Visible (noteFrom (C.Mutation.input request) id) (Resolved.checkout resolved) →
      ledger (C.Mutation.operationId request) ≡ just (R.active (writeMeaning request)) →
      Step (R.completion (C.Mutation.operationId request) (writeMeaning request) (saved id))
        (R.state before ledger)
        (R.state (replaceNotes before (Notes.recordNote
          (C.FamilyTarget.expectedFamily (C.NoteInput.target (C.Mutation.input request))) id
          (noteFrom (C.Mutation.input request) id) (RepositoryWorld.notes before)))
          (R.update (C.Mutation.operationId request) (R.completed (writeMeaning request) (saved id)) ledger))
    delete : ∀ {before ledger request target id old} →
      C.Mutation.input request ≡ (target , id) →
      (resolved : Resolved before target) →
      K.World.notes (RepositoryWorld.notes before) (C.FamilyTarget.expectedFamily target) id ≡ just old →
      K.Visible old (Resolved.checkout resolved) →
      ledger (C.Mutation.operationId request) ≡ just (R.active (deleteMeaning request)) →
      Step (R.completion (C.Mutation.operationId request) (deleteMeaning request) (deleted id))
        (R.state before ledger)
        (R.state (replaceNotes before (Notes.deleteNote (C.FamilyTarget.expectedFamily target) id (RepositoryWorld.notes before)))
          (R.update (C.Mutation.operationId request) (R.completed (deleteMeaning request) (deleted id)) ledger))

  -- Each note transition is also the atomic receipt transition for that request.
  asReceiptStep : ∀ {event before after} → Step event before after → R.Step event before after
  asReceiptStep (write resolved allowed valid visible receipt) = R.commit receipt
  asReceiptStep (delete input resolved present visible receipt) = R.commit receipt

  -- Note completion enters through its own transition, never through the
  -- generic receipt relation. Prior context is retained in the conversation.
  data ConversationEvent : Set where
    common : R.ConversationEvent → ConversationEvent
    noteCompletion : R.Event → ConversationEvent

  data ConversationStep {Task Progress : Set} : ConversationEvent →
    D.Conversation Task R.Information Progress (R.State (RepositoryWorld Other)) →
    D.Conversation Task R.Information Progress (R.State (RepositoryWorld Other)) → Set where
    commonStep : ∀ {event before after} → R.ConversationStep event before after →
      ConversationStep (common event) before after
    noteStep : ∀ {before after id meaning result task prior completed} →
      Step (R.completion id meaning result) before after →
      ConversationStep (noteCompletion (R.completion id meaning result))
        (D.conversation task (R.complete meaning ∷ prior) completed before D.working)
        (D.conversation task (R.complete meaning ∷ prior) completed after D.working)

  noteWithConversation : ∀ {Task Progress : Set} {before after id meaning result task prior completed} →
    Step (R.completion id meaning result) before after →
    ConversationStep {Task} {Progress} (noteCompletion (R.completion id meaning result))
      (D.conversation task (R.complete meaning ∷ prior) completed before D.working)
      (D.conversation task (R.complete meaning ∷ prior) completed after D.working)
  noteWithConversation step = noteStep step

  waitingDoesNotChangeState : ∀ {Task Progress : Set} {event before after prompt} →
    ConversationStep {Task} {Progress} event before after →
    D.Conversation.phase before ≡ D.awaiting prompt →
    D.Conversation.world after ≡ D.Conversation.world before
  waitingDoesNotChangeState (commonStep step) waiting = R.awaitingDoesNotChangeRequestState step waiting
  waitingDoesNotChangeState (noteStep step) ()

  writeStoresNote : ∀ {before after request id} →
    Step (R.completion (C.Mutation.operationId request) (writeMeaning request) (saved id)) before after →
    K.World.notes (RepositoryWorld.notes (R.State.dataState after))
      (C.FamilyTarget.expectedFamily (C.NoteInput.target (C.Mutation.input request))) id ≡
      just (noteFrom (C.Mutation.input request) id)
  writeStoresNote (write {before = before} {request = request} {id = id} resolved allowed valid visible receipt) =
    Notes.recordedNote (C.FamilyTarget.expectedFamily (C.NoteInput.target (C.Mutation.input request)))
      id (noteFrom (C.Mutation.input request) id) (RepositoryWorld.notes before)

  writePreservesOtherFamily : ∀ {before after request id} →
    Step (R.completion (C.Mutation.operationId request) (writeMeaning request) (saved id)) before after →
    ∀ other key → ¬ (C.FamilyTarget.expectedFamily (C.NoteInput.target (C.Mutation.input request)) ≡ other) →
    K.World.notes (RepositoryWorld.notes (R.State.dataState after)) other key ≡
    K.World.notes (RepositoryWorld.notes (R.State.dataState before)) other key
  writePreservesOtherFamily (write {before = before} {request = request} {id = id} resolved allowed valid visible receipt) other key distinct =
    Notes.putOtherFamily (C.FamilyTarget.expectedFamily (C.NoteInput.target (C.Mutation.input request)))
      id (noteFrom (C.Mutation.input request) id) (K.World.notes (RepositoryWorld.notes before)) other key distinct

  committedNoteCanReplay : ∀ {before after id meaning result} →
    Step (R.completion id meaning result) before after → R.Step (R.replayRequest id meaning result) after after
  committedNoteCanReplay step = R.committedCanReplay (asReceiptStep step)

  scopedWriteCannotRunElsewhere : ∀ {before after request id old selected checkout} →
    Step (R.completion (C.Mutation.operationId request) (writeMeaning request) (saved id)) before after →
    K.World.notes (RepositoryWorld.notes (R.State.dataState before))
      (C.FamilyTarget.expectedFamily (C.NoteInput.target (C.Mutation.input request))) id ≡ just old →
    K.Note.scope old ≡ just selected →
    RepositoryWorld.locations (R.State.dataState before) (C.FamilyTarget.location (C.NoteInput.target (C.Mutation.input request))) ≡ just checkout →
    ¬ (W.Checkout.id checkout ≡ selected) → ⊥
  scopedWriteCannotRunElsewhere (write resolved allowed valid newVisible receipt) present scoped location distinct =
    scopedUnavailable resolved _ _ _ scoped location distinct (existingWriteVisible allowed present)

  scopedDeleteCannotRunElsewhere : ∀ {before after request target id old selected checkout} →
    C.Mutation.input request ≡ (target , id) →
    Step (R.completion (C.Mutation.operationId request) (deleteMeaning request) (deleted id)) before after →
    K.World.notes (RepositoryWorld.notes (R.State.dataState before)) (C.FamilyTarget.expectedFamily target) id ≡ just old →
    K.Note.scope old ≡ just selected →
    RepositoryWorld.locations (R.State.dataState before) (C.FamilyTarget.location target) ≡ just checkout →
    ¬ (W.Checkout.id checkout ≡ selected) → ⊥
  scopedDeleteCannotRunElsewhere expected (delete input resolved found visible receipt) present scoped location distinct
    with trans (sym input) expected
  ... | refl = scopedUnavailable resolved _ _ _ scoped location distinct
    (subst (λ note → K.Visible note (Resolved.checkout resolved)) (just-injective (trans (sym found) present)) visible)

  deleteRemovesNote : ∀ {before after request target id} →
    C.Mutation.input request ≡ (target , id) →
    Step (R.completion (C.Mutation.operationId request) (deleteMeaning request) (deleted id)) before after →
    K.World.notes (RepositoryWorld.notes (R.State.dataState after)) (C.FamilyTarget.expectedFamily target) id ≡ nothing
  deleteRemovesNote expected (delete {before = before} input resolved found visible receipt)
    with trans (sym input) expected
  ... | refl = Notes.deletedNote _ _ (RepositoryWorld.notes before)

  deletePreservesOtherFamily : ∀ {before after request target id} →
    C.Mutation.input request ≡ (target , id) →
    Step (R.completion (C.Mutation.operationId request) (deleteMeaning request) (deleted id)) before after →
    ∀ other key → ¬ (C.FamilyTarget.expectedFamily target ≡ other) →
    K.World.notes (RepositoryWorld.notes (R.State.dataState after)) other key ≡
    K.World.notes (RepositoryWorld.notes (R.State.dataState before)) other key
  deletePreservesOtherFamily expected (delete {before = before} input resolved found visible receipt) other key distinct
    with trans (sym input) expected
  ... | refl = Notes.removeOtherFamily _ _ (K.World.notes (RepositoryWorld.notes before)) other key distinct

  record VisibleNote (world : RepositoryWorld Other) (target : C.FamilyTarget) (id : KnowledgeId) : Set where
    field resolved : Resolved world target
          note : K.Note (C.FamilyTarget.expectedFamily target) id
          stored : K.World.notes (RepositoryWorld.notes world) (C.FamilyTarget.expectedFamily target) id ≡ just note
          visible : K.Visible note (Resolved.checkout resolved)

  familyWideShared : ∀ world first second id (note : K.Note (C.FamilyTarget.expectedFamily first) id) →
    C.FamilyTarget.expectedFamily first ≡ C.FamilyTarget.expectedFamily second →
    K.World.notes (RepositoryWorld.notes world) (C.FamilyTarget.expectedFamily first) id ≡ just note →
    K.Note.scope note ≡ nothing → (resolved : Resolved world second) → VisibleNote world second id
  familyWideShared world first second id note refl stored unrestricted resolved = record
    { resolved = resolved
    ; note = note
    ; stored = stored
    ; visible = K.familyWideVisible note (Resolved.checkout resolved) (Resolved.familyMatches resolved) unrestricted }

  -- The goal is stated over the world, independently of the transition.
  record WriteGoal (before after : R.State (RepositoryWorld Other))
    (request : C.Mutation C.NoteInput) (id : KnowledgeId) : Set where
    field
      storedNote : K.World.notes (RepositoryWorld.notes (R.State.dataState after))
        (C.FamilyTarget.expectedFamily (C.NoteInput.target (C.Mutation.input request))) id ≡
        just (noteFrom (C.Mutation.input request) id)
      oldVectorRemoved : K.World.vectorProfile (RepositoryWorld.notes (R.State.dataState after))
        (C.FamilyTarget.expectedFamily (C.NoteInput.target (C.Mutation.input request))) id ≡ nothing
      otherNotes : ∀ other key →
        ¬ (C.FamilyTarget.expectedFamily (C.NoteInput.target (C.Mutation.input request)) ≡ other) →
        K.World.notes (RepositoryWorld.notes (R.State.dataState after)) other key ≡
        K.World.notes (RepositoryWorld.notes (R.State.dataState before)) other key
      otherVectors : ∀ other key →
        ¬ (C.FamilyTarget.expectedFamily (C.NoteInput.target (C.Mutation.input request)) ≡ other) →
        K.World.vectorProfile (RepositoryWorld.notes (R.State.dataState after)) other key ≡
        K.World.vectorProfile (RepositoryWorld.notes (R.State.dataState before)) other key
      otherNoteIds : ∀ family key → ¬ (id ≡ key) →
        K.World.notes (RepositoryWorld.notes (R.State.dataState after)) family key ≡
        K.World.notes (RepositoryWorld.notes (R.State.dataState before)) family key
      otherVectorIds : ∀ family key → ¬ (id ≡ key) →
        K.World.vectorProfile (RepositoryWorld.notes (R.State.dataState after)) family key ≡
        K.World.vectorProfile (RepositoryWorld.notes (R.State.dataState before)) family key
      profilesUnchanged : ∀ family →
        K.World.profile (RepositoryWorld.notes (R.State.dataState after)) family ≡
        K.World.profile (RepositoryWorld.notes (R.State.dataState before)) family
      locationsUnchanged : ∀ location →
        RepositoryWorld.locations (R.State.dataState after) location ≡ RepositoryWorld.locations (R.State.dataState before) location
      otherUnchanged : RepositoryWorld.other (R.State.dataState after) ≡ RepositoryWorld.other (R.State.dataState before)
      receiptSaved : R.State.ledger after (C.Mutation.operationId request) ≡ just (R.completed (writeMeaning request) (saved id))
      otherReceipts : ∀ other → ¬ (C.Mutation.operationId request ≡ other) →
        R.State.ledger after other ≡ R.State.ledger before other

  writeMeetsGoal : ∀ {before after request id} →
    Step (R.completion (C.Mutation.operationId request) (writeMeaning request) (saved id)) before after →
    WriteGoal before after request id
  writeMeetsGoal step@(write {before = before} {request = request} {id = id} resolved allowed valid visible receipt) = record
    { storedNote = writeStoresNote step
    ; oldVectorRemoved = Notes.changedNoteHasNoOldVector _ id (RepositoryWorld.notes before) (noteFrom (C.Mutation.input request) id)
    ; otherNotes = writePreservesOtherFamily step
    ; otherVectors = Notes.changedNoteKeepsOtherFamilyVectors _ id (RepositoryWorld.notes before) (noteFrom (C.Mutation.input request) id)
    ; otherNoteIds = Notes.putOtherNote _ id (noteFrom (C.Mutation.input request) id) (K.World.notes (RepositoryWorld.notes before))
    ; otherVectorIds = Notes.changedNoteKeepsOtherVectors _ id (RepositoryWorld.notes before) (noteFrom (C.Mutation.input request) id)
    ; profilesUnchanged = λ family → refl
    ; locationsUnchanged = λ location → refl
    ; otherUnchanged = refl
    ; receiptSaved = R.commitKeepsReceipt (asReceiptStep step)
    ; otherReceipts = R.completionKeepsOther (asReceiptStep step) }

  record DeleteGoal (before after : R.State (RepositoryWorld Other))
    (request : C.Mutation (C.FamilyTarget × KnowledgeId)) (target : C.FamilyTarget) (id : KnowledgeId) : Set where
    field
      removedNote : K.World.notes (RepositoryWorld.notes (R.State.dataState after))
        (C.FamilyTarget.expectedFamily target) id ≡ nothing
      removedVector : K.World.vectorProfile (RepositoryWorld.notes (R.State.dataState after))
        (C.FamilyTarget.expectedFamily target) id ≡ nothing
      otherNotes : ∀ other key → ¬ (C.FamilyTarget.expectedFamily target ≡ other) →
        K.World.notes (RepositoryWorld.notes (R.State.dataState after)) other key ≡
        K.World.notes (RepositoryWorld.notes (R.State.dataState before)) other key
      otherVectors : ∀ other key → ¬ (C.FamilyTarget.expectedFamily target ≡ other) →
        K.World.vectorProfile (RepositoryWorld.notes (R.State.dataState after)) other key ≡
        K.World.vectorProfile (RepositoryWorld.notes (R.State.dataState before)) other key
      otherNoteIds : ∀ family key → ¬ (id ≡ key) →
        K.World.notes (RepositoryWorld.notes (R.State.dataState after)) family key ≡
        K.World.notes (RepositoryWorld.notes (R.State.dataState before)) family key
      otherVectorIds : ∀ family key → ¬ (id ≡ key) →
        K.World.vectorProfile (RepositoryWorld.notes (R.State.dataState after)) family key ≡
        K.World.vectorProfile (RepositoryWorld.notes (R.State.dataState before)) family key
      profilesUnchanged : ∀ family →
        K.World.profile (RepositoryWorld.notes (R.State.dataState after)) family ≡
        K.World.profile (RepositoryWorld.notes (R.State.dataState before)) family
      locationsUnchanged : ∀ location →
        RepositoryWorld.locations (R.State.dataState after) location ≡ RepositoryWorld.locations (R.State.dataState before) location
      otherUnchanged : RepositoryWorld.other (R.State.dataState after) ≡ RepositoryWorld.other (R.State.dataState before)
      receiptSaved : R.State.ledger after (C.Mutation.operationId request) ≡ just (R.completed (deleteMeaning request) (deleted id))
      otherReceipts : ∀ other → ¬ (C.Mutation.operationId request ≡ other) →
        R.State.ledger after other ≡ R.State.ledger before other

  deleteMeetsGoal : ∀ {before after request target id} →
    C.Mutation.input request ≡ (target , id) →
    Step (R.completion (C.Mutation.operationId request) (deleteMeaning request) (deleted id)) before after →
    DeleteGoal before after request target id
  deleteMeetsGoal expected step@(delete {before = before} input resolved found visible receipt)
    with trans (sym input) expected
  ... | refl = record
    { removedNote = Notes.deletedNote _ _ (RepositoryWorld.notes before)
    ; removedVector = Notes.deletedNoteHasNoVector _ _ (RepositoryWorld.notes before)
    ; otherNotes = Notes.removeOtherFamily _ _ (K.World.notes (RepositoryWorld.notes before))
    ; otherVectors = Notes.deletedNoteKeepsOtherFamilyVectors _ _ (RepositoryWorld.notes before)
    ; otherNoteIds = Notes.removeOtherNote _ _ (K.World.notes (RepositoryWorld.notes before))
    ; otherVectorIds = Notes.deletedNoteKeepsOtherVectors _ _ (RepositoryWorld.notes before)
    ; profilesUnchanged = λ family → refl
    ; locationsUnchanged = λ location → refl
    ; otherUnchanged = refl
    ; receiptSaved = R.commitKeepsReceipt (asReceiptStep step)
    ; otherReceipts = R.completionKeepsOther (asReceiptStep step) }

  -- Listing is specified by visible membership, without specifying how search
  -- or ranking is implemented.
  record ListGoal (world : RepositoryWorld Other) (target : C.FamilyTarget)
    (listed : KnowledgeId → Set) : Set₁ where
    field
      sound : ∀ id → listed id → VisibleNote world target id
      complete : ∀ id → VisibleNote world target id → listed id

  noteReplayInConversation : ∀ {Task Progress : Set} {before after id meaning result task prior completed} →
    Step (R.completion id meaning result) before after →
    ConversationStep {Task} {Progress} (common (R.requestEvent (R.replayRequest id meaning result)))
      (D.conversation task (R.complete meaning ∷ prior) completed after D.working)
      (D.conversation task (R.complete meaning ∷ prior) completed after D.working)
  noteReplayInConversation step =
    commonStep (R.requestStep R.replayKnown R.safeReplay (committedNoteCanReplay step))

  retryAfterAnotherNote : ∀ {before after changed meaning result original originalMeaning originalResult} →
    Step (R.completion changed meaning result) before after → ¬ (changed ≡ original) →
    R.State.ledger before original ≡ just (R.completed originalMeaning originalResult) →
    R.Step (R.replayRequest original originalMeaning originalResult) after after
  retryAfterAnotherNote step distinct savedReceipt = R.replayStep
    (trans (R.completionKeepsOther (asReceiptStep step) _ distinct) savedReceipt)

  -- Search may choose a subset, but must never return a note outside the
  -- selected family or worktree scope. Relevance is outside this state model.
  SearchGoal : RepositoryWorld Other → C.FamilyTarget → (KnowledgeId → Set) → Set
  SearchGoal world target returned = ∀ id → returned id → VisibleNote world target id

  completedNoteCannotRunAgain : ∀ {before after id oldMeaning newMeaning oldResult newResult} →
    R.State.ledger before id ≡ just (R.completed oldMeaning oldResult) →
    ¬ Step (R.completion id newMeaning newResult) before after
  completedNoteCannotRunAgain found step = R.completedCannotCommitAgain found (asReceiptStep step)

  -- A saved receipt remains usable after any number of other note changes.
  data OtherNoteSteps (original : Requests.Id) : R.State (RepositoryWorld Other) →
    R.State (RepositoryWorld Other) → Set where
    noOtherNotes : ∀ {current} → OtherNoteSteps original current current
    anotherNote : ∀ {changed meaning result before middle after} → ¬ (changed ≡ original) →
      Step (R.completion changed meaning result) before middle →
      OtherNoteSteps original middle after → OtherNoteSteps original before after

  otherNoteStepsKeepReceipt : ∀ {before after original meaning result} →
    OtherNoteSteps original before after →
    R.State.ledger before original ≡ just (R.completed meaning result) →
    R.State.ledger after original ≡ just (R.completed meaning result)
  otherNoteStepsKeepReceipt noOtherNotes receipt = receipt
  otherNoteStepsKeepReceipt (anotherNote distinct first rest) receipt =
    otherNoteStepsKeepReceipt rest (trans (R.completionKeepsOther (asReceiptStep first) _ distinct) receipt)

  retryAfterOtherNotes : ∀ {before after original meaning result} →
    OtherNoteSteps original before after →
    R.State.ledger before original ≡ just (R.completed meaning result) →
    R.Step (R.replayRequest original meaning result) after after
  retryAfterOtherNotes steps receipt = R.replayStep (otherNoteStepsKeepReceipt steps receipt)
