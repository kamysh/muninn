{-# OPTIONS --safe #-}
-- Family note writes use actual rows and the shared atomic receipt protocol.
module Muninn.KnowledgeWrite where
import Muninn.OwnedState as O
import Muninn.Knowledge as K
import Muninn.KnowledgeViews as Views
import Muninn.KnowledgeLookup as Lookup
import Muninn.KnowledgeRead as Read
import Muninn.Canonical as Canonical
import Muninn.RequestCodecs as Codecs
import Muninn.ExclusionOutcomes as E
import Muninn.RecordAllocation as Allocation
import Muninn.RegistryCreation as Fresh
import Muninn.RetirementControl as Frames
import Muninn.ViewPublication as ViewFrames
import Muninn.ReceiptLedger as Ledger
import Muninn.Dialogue as D
import Muninn.StoredPolicy as Policy
import Muninn.Worktree as W
import Muninn.CatalogInputs as I
import Muninn.RequestIdentity as Identity
import Muninn.ReceiptTypes as Receipt
import Muninn.SearchTarget as Target
import Muninn.RepositoryIdentity as Repository
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false; not; _∧_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String; _++_)
import Data.String as String
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
module DB = O.DB

module Family (family : ℕ) (codec : Views.Codec) (request : I.Mutation I.NoteInput) (chosenId : K.KnowledgeId) where
  input = I.Mutation.input request
  desired : K.KnowledgeItem
  desired = record { id = chosenId; family = I.FamilyTarget.expectedFamily (I.NoteInput.target input)
    ; scope = I.NoteInput.scope input; origin = I.NoteInput.origin input
    ; title = I.NoteInput.title input; body = I.NoteInput.body input
    ; tags = I.NoteInput.tags input; relatedFiles = I.NoteInput.relatedFiles input }
  owner = O.family family
  payload = Views.Codec.encode codec desired
  note = O.recordOf owner (O.note payload)
  saved : String
  saved = "The note is saved."
  waiting : String
  waiting = "The saved note changed while this request was being prepared. Continue the request with the current note."
  guidance : String → D.Prompt
  guidance reason = D.prompt (D.text 'I' (" could not complete the note request: " ++ reason))
    (D.text 'C' "orrect the identified problem or restore access, then continue the saved request.") []

  module Notes = Lookup.Family family codec chosenId
  open Notes public using (Located; inspect; scan; find)

  slot : ∀ world → Maybe (Located world) → ℕ
  slot world nothing = Allocation.freshId world
  slot world (just found) = Located.slot found
  changed : ∀ world → Maybe (Located world) → O.World
  changed world found = DB.write (slot world found) note world
  write : ∀ world → Maybe (Located world) → DB.Transaction String
  write world found = DB.put (slot world found) note (DB.commit saved)
  transaction : DB.Transaction String
  transaction = DB.scan (λ world → write world (find world))
  result : ∀ world found → DB.evaluate (write world found) world ≡ DB.committed saved (changed world found)
  result world found = refl
  actualNoteSaved : ∀ world found → DB.lookup (slot world found) (changed world found) ≡ just note
  actualNoteSaved world found = DB.writeVisible (slot world found) note world
  savedContentDecodes : Views.Codec.decode codec payload ≡ just desired
  savedContentDecodes = Views.Codec.roundTrip codec desired

  frame : ∀ world found → Ledger.ReceiptFrame world (changed world found)
  frame world nothing = Fresh.freshFrame world (Allocation.freshId world) note (Allocation.fresh world) (λ ())
  frame world (just found) = Frames.writeFrame world (Located.slot found)
    (O.recordOf owner (O.note (Located.oldPayload found))) note (Located.stored found) (λ ()) (λ ())
  isolates : ∀ before resultValue after → DB.evaluate transaction before ≡ DB.committed resultValue after → Ledger.ReceiptFrame before after
  isolates before .saved .(changed before (find before)) refl = frame before (find before)
  effect : Ledger.Effect
  effect = record { transaction = transaction; guidance = guidance; isolates = isolates }

  module Guarded (registrationSlot pointer selected : ℕ) (context : D.Context) (observed : Repository.Observation) where
    module Current = Policy.Family family pointer
    module Access = Read.Family family pointer codec
    module Requested = Target.Family family registrationSlot selected (I.FamilyTarget.location (I.NoteInput.target input)) context observed
    -- A narrow scope must name an actual non-retired checkout of this family.
    matchesCheckout : W.CheckoutId → O.Record → Bool
    matchesCheckout wanted (O.recordOf actualOwner (O.checkout info)) =
      E.sameOwner actualOwner owner ∧ (does (Canonical.compare Codecs.checkoutId wanted (O.CheckoutInfo.id info)) ∧ not (O.CheckoutInfo.retired info))
    matchesCheckout wanted row = false
    scopeValid : O.World → Bool
    scopeValid world with K.KnowledgeItem.scope desired
    ... | nothing = true
    ... | just wanted = E.anyRow (λ key row → matchesCheckout wanted row) world
    familyValid : ∀ {world} → Current.Saved world → Bool
    familyValid current = does (Canonical.compare Codecs.familyId (K.KnowledgeItem.family desired) (O.PolicyVersionInfo.familyId (Current.Saved.info current)))
    idValid : O.World → Bool
    idValid world with I.NoteInput.id input
    ... | just wanted = does (Canonical.compare Codecs.knowledgeId wanted chosenId)
    ... | nothing with find world
    ...   | nothing = true
    ...   | just _ = false
    accessValid : O.World → Bool
    accessValid world with Requested.observe world
    ... | nothing = false
    ... | just resolved with Canonical.compare Codecs.familyId (I.FamilyTarget.expectedFamily (I.NoteInput.target input)) (O.RegistrationInfo.id (Requested.Target.registration resolved)) | O.CheckoutInfo.retired (Requested.Target.checkout resolved)
    ...   | yes _ | false with find world
    ...     | nothing = true
    ...     | just old with Access.allowed (Located.oldItem old) (Requested.Target.checkout resolved) | Canonical.compare Codecs.familyId (K.KnowledgeItem.family (Located.oldItem old)) (K.KnowledgeItem.family desired)
    ...       | just _ | yes _ = true
    ...       | _ | _ = false
    accessValid world | just resolved | _ | _ = false
    contentValid : Bool
    contentValid = not (does (I.NoteInput.title input String.≟ "")) ∧ not (does (I.NoteInput.body input String.≟ ""))
    select : ∀ world → Maybe (Current.Saved world) → DB.Transaction String
    select world nothing = DB.abort "I cannot read this repository's current settings. Reconnect and continue the saved request."
    select world (just current) with contentValid
    ... | false = DB.abort "A note needs both a title and a body. Provide the missing text."
    ... | true with familyValid current ∧ scopeValid world ∧ idValid world ∧ accessValid world
    ...   | false = DB.abort "The repository, worktree or note identity does not match this request. Check them and continue."
    ...   | true = write world (find world)
    guarded : DB.Transaction String
    guarded = DB.scan (λ world → select world (Current.observe world))
    selectedFrame : ∀ world current answer after → DB.evaluate (select world current) world ≡ DB.committed answer after → Ledger.ReceiptFrame world after
    selectedFrame world nothing answer after ()
    selectedFrame world (just current) answer after committed with contentValid
    ... | false with committed
    ...   | ()
    selectedFrame world (just current) answer after committed | true with familyValid current ∧ scopeValid world ∧ idValid world ∧ accessValid world
    ... | false with committed
    ...   | ()
    selectedFrame world (just current) answer after committed | true | true rewrite result world (find world) with committed
    ... | refl = frame world (find world)
    guardedCommits : ∀ world current → Current.observe world ≡ just current → contentValid ≡ true →
      familyValid current ∧ scopeValid world ∧ idValid world ∧ accessValid world ≡ true →
      DB.evaluate guarded world ≡ DB.committed saved (changed world (find world))
    guardedCommits world current policy content allowed rewrite policy | content | allowed = refl
    guardedEffect : Ledger.Effect
    guardedEffect = record { transaction = guarded; guidance = guidance
      ; isolates = λ before answer after committed → selectedFrame before (Current.observe before) answer after committed }
    save : ℕ → DB.Transaction Ledger.Reply
    save expected = Ledger.update (I.Mutation.operationId request) (Identity.mutation Identity.kWriteNote request) expected Ledger.complete guardedEffect
    completedRetry : ∀ names expected receiptSlot receiptOwner answer world →
      Ledger.find (I.Mutation.operationId request) world ≡ just (Ledger.found receiptSlot receiptOwner
        (Receipt.finished (Identity.mutation Identity.kWriteNote request) names answer)) →
      DB.execute (save expected) world ≡ (Ledger.saved answer , world)
    completedRetry names expected receiptSlot receiptOwner answer world =
      Ledger.finishedSkipsEffect (I.Mutation.operationId request) (Identity.mutation Identity.kWriteNote request)
        names expected Ledger.complete guardedEffect receiptSlot receiptOwner answer world

    module Completed (before : O.World)
      (performed : DB.evaluate guarded before ≡ DB.committed saved (changed before (find before)))
      (names : Receipt.Names (I.Mutation.operationId request) (Identity.mutation Identity.kWriteNote request))
      (receiptSlot : ℕ) (receiptOwner : O.Owner) (work : Receipt.Work)
      (receiptFound : Ledger.find (I.Mutation.operationId request) before ≡ just (Ledger.found receiptSlot receiptOwner
        (Receipt.active (Identity.mutation Identity.kWriteNote request) names work)))
      (receiptAt : DB.lookup receiptSlot before ≡ just (Ledger.recordAt receiptOwner
        (Receipt.active (Identity.mutation Identity.kWriteNote request) names work))) where
      idRequest = I.Mutation.operationId request
      meaning = Identity.mutation Identity.kWriteNote request
      changedWorld = changed before (find before)
      oldReceipt = Ledger.recordAt {id = idRequest} receiptOwner (Receipt.active meaning names work)
      finalReceipt = Ledger.recordAt {id = idRequest} receiptOwner (Receipt.finished meaning names saved)
      after = DB.write receiptSlot finalReceipt changedWorld
      commits : DB.execute (save (Receipt.generation work)) before ≡ (Ledger.saved saved , after)
      commits = Ledger.committedUpdate idRequest meaning names Ledger.complete guardedEffect receiptSlot receiptOwner work before saved changedWorld receiptFound performed
      receiptInChanged : DB.lookup receiptSlot changedWorld ≡ just oldReceipt
      receiptInChanged = proj₁ (frame before (find before) receiptSlot receiptOwner
        (Receipt.entry idRequest (Receipt.active meaning names work))) receiptAt
      distinct : receiptSlot ≢ slot before (find before)
      distinct = ViewFrames.lookupDistinct changedWorld receiptSlot oldReceipt (slot before (find before)) note
        receiptInChanged (actualNoteSaved before (find before)) (λ ())
      noteSaved : DB.lookup (slot before (find before)) after ≡ just note
      noteSaved = trans (DB.writePreservesOther receiptSlot (slot before (find before)) finalReceipt changedWorld distinct)
        (actualNoteSaved before (find before))
      retry : DB.execute (save (Receipt.generation work)) after ≡ (Ledger.saved saved , after)
      retry = completedRetry names (Receipt.generation work) receiptSlot receiptOwner saved after
        (Ledger.writtenReceiptVisible idRequest receiptSlot receiptOwner (Receipt.finished meaning names saved) changedWorld)
      boundary : ∀ observed → O.Execution.Interrupted (O.Execution.atomic (save (Receipt.generation work)) O.Execution.done) before observed →
        observed ≡ before ⊎ observed ≡ after
      boundary observed interrupted with Ledger.atomicBoundary (save (Receipt.generation work)) before observed interrupted
      ... | inj₁ same = inj₁ same
      ... | inj₂ same = inj₂ (trans same (cong proj₂ commits))
      completedAtomic : ∀ observed reply final → O.Execution.Completed (O.Execution.atomic (save (Receipt.generation work)) O.Execution.done) observed reply final →
        DB.execute (save (Receipt.generation work)) observed ≡ (reply , final)
      completedAtomic observed reply final (O.Execution.committed O.Execution.stop) = refl
      converges : ∀ observed reply final → O.Execution.Interrupted (O.Execution.atomic (save (Receipt.generation work)) O.Execution.done) before observed →
        O.Execution.Completed (O.Execution.atomic (save (Receipt.generation work)) O.Execution.done) observed reply final → final ≡ after
      converges observed reply final interrupted completed with boundary observed interrupted
      ... | inj₁ same = trans (sym (cong proj₂ (completedAtomic observed reply final completed)))
        (trans (cong (λ world → proj₂ (DB.execute (save (Receipt.generation work)) world)) same) (cong proj₂ commits))
      ... | inj₂ same = trans (sym (cong proj₂ (completedAtomic observed reply final completed)))
        (trans (cong (λ world → proj₂ (DB.execute (save (Receipt.generation work)) world)) same) (cong proj₂ retry))
      retrySavesNote : ∀ observed reply final → O.Execution.Interrupted (O.Execution.atomic (save (Receipt.generation work)) O.Execution.done) before observed →
        O.Execution.Completed (O.Execution.atomic (save (Receipt.generation work)) O.Execution.done) observed reply final →
        DB.lookup (slot before (find before)) final ≡ just note
      retrySavesNote observed reply final interrupted completed =
        subst (λ world → DB.lookup (slot before (find before)) world ≡ just note) (sym (converges observed reply final interrupted completed)) noteSaved
