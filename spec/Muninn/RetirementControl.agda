{-# OPTIONS --safe #-}
-- Lifecycle control and its cleanup capture share the existing DB transaction.
module Muninn.RetirementControl where

import Muninn.Retirement as Life
import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.CleanupStorage as Storage
import Muninn.CleanupAdmissionStorage as Insert
import Muninn.RecordAllocation as Allocation
import Muninn.CleanupScheduling as Scheduling
import Muninn.CleanupObservations as Observations
import Muninn.CleanupOrder as Order
import Muninn.CleanupFinalization as Finalization
import Muninn.ReceiptLedger as Ledger
import Muninn.ReceiptTypes as R
import Muninn.CatalogInputs as I
import Muninn.RequestIdentity as Identity
import Muninn.Dialogue as D
import Muninn.RetirementCleanup as Reclaim
import Muninn.ViewPublication as Publication
open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (Bool; true; false)
open import Data.String using (String)
open import Data.List using ([])
import Data.List.Relation.Unary.All as All
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Unit using (tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
module DB = O.DB
module Exec = O.Execution

data Control : Set where
  registration : O.RegistrationInfo → Control
  checkout : O.CheckoutInfo → Control

body : Control → O.Body
body (registration info) = O.registration info
body (checkout info) = O.checkout info

state : Control → Life.State
state (registration info) = Life.registrationState info
state (checkout info) = Life.checkoutState info

update : ℕ → Life.Inspection → Control → Control
update now observed (registration info) = registration (Life.registrationUpdate now observed info)
update now observed (checkout info) = checkout (Life.checkoutUpdate now observed info)

matches : ∀ now observed control → state (update now observed control) ≡ Life.inspect now observed (state control)
matches now observed (registration info) = Life.registrationUpdateMatches now observed info
matches now observed (checkout info) = Life.checkoutUpdateMatches now observed info

noReceipt : ∀ control → O.kind (body control) ≢ O.receiptK
noReceipt (registration info) ()
noReceipt (checkout info) ()

sameKind : ∀ now observed control → O.kind (body (update now observed control)) ≡ O.kind (body control)
sameKind now observed (registration info) = refl
sameKind now observed (checkout info) = refl

noReferences : ∀ control → O.references (body control) ≡ []
noReferences (registration info) = refl
noReferences (checkout info) = refl

placed : ∀ family control → O.Placed (O.recordOf (O.family family) (body control))
placed family (registration info) = O.local
placed family (checkout info) = O.local

referenceSubset : ∀ old new ref → ref ∈ O.references (body new) → ref ∈ O.references (body old)
referenceSubset old (registration info) ref ()
referenceSubset old (checkout info) ref ()

newRetirement : ℕ → Life.Inspection → Control → Bool
newRetirement now observation control with Life.State.phase (state control) | Life.State.phase (Life.inspect now observation (state control))
... | Life.active | Life.retired = true
... | _ | _ = false

writeFrame : ∀ before slot old new → DB.lookup slot before ≡ just old →
  O.kind (O.body old) ≢ O.receiptK → O.kind (O.body new) ≢ O.receiptK →
  Ledger.ReceiptFrame before (DB.write slot new before)
writeFrame before slot old new located oldNotReceipt newNotReceipt key owner receiptData = forward , backward
  where
  forward : DB.lookup key before ≡ just (O.recordOf owner (O.receipt receiptData)) →
    DB.lookup key (DB.write slot new before) ≡ just (O.recordOf owner (O.receipt receiptData))
  forward found with slot ≟ key
  ... | yes refl = ⊥-elim (oldNotReceipt (cong (λ value → O.kind (O.body value)) (just-injective (trans (sym located) found))))
  ... | no different = trans (DB.writePreservesOther slot key new before different) found
  backward : DB.lookup key (DB.write slot new before) ≡ just (O.recordOf owner (O.receipt receiptData)) →
    DB.lookup key before ≡ just (O.recordOf owner (O.receipt receiptData))
  backward found with slot ≟ key
  ... | yes refl = ⊥-elim (newNotReceipt (cong (λ value → O.kind (O.body value)) (just-injective (trans (sym (DB.writeVisible slot new before)) found))))
  ... | no different = trans (sym (DB.writePreservesOther slot key new before different)) found

writeBackward : ∀ world changed new key value → O.kind (O.body new) ≢ O.kind (O.body value) →
  DB.lookup key (DB.write changed new world) ≡ just value → DB.lookup key world ≡ just value
writeBackward world changed new key value different found with changed ≟ key
... | yes refl = ⊥-elim (different (cong (λ stored → O.kind (O.body stored))
  (just-injective (trans (sym (DB.writeVisible changed new world)) found))))
... | no other = trans (sym (DB.writePreservesOther changed key new world other)) found

registrationInjective : ∀ owner first second → O.recordOf owner (O.registration first) ≡ O.recordOf owner (O.registration second) → first ≡ second
registrationInjective owner first .first refl = refl

noopFrame : ∀ (result : String) before reply after → DB.evaluate (DB.commit result) before ≡ DB.committed reply after → Ledger.ReceiptFrame before after
noopFrame result before .result .before refl key owner receiptData = (λ found → found) , (λ found → found)

module Family (selection : E.Rule) (slot now : ℕ) (observation : Life.Inspection)
  (id : I.OperationId) (payload checkpoint continuation : String) (guidance : String → D.Prompt) where
  owner = E.targetOwner selection
  module Tasks = Allocation.Model.Family selection
  module Capture = Scheduling.Model.Family selection

  record Seen (world : O.World) : Set where
    constructor seen
    field control : Control
          located : DB.lookup slot world ≡ just (O.recordOf owner (body control))

  valueAt : ∀ world → (value : Maybe O.Record) → DB.lookup slot world ≡ value → Maybe (Seen world)
  valueAt world (just (O.recordOf actualOwner (O.registration info))) found with E.ownerEqual actualOwner owner
  ... | yes refl = just (seen (registration info) found)
  ... | no other = nothing
  valueAt world (just (O.recordOf actualOwner (O.checkout info))) found with E.ownerEqual actualOwner owner
  ... | yes refl = just (seen (checkout info) found)
  ... | no other = nothing
  valueAt world value found = nothing

  observe : (world : O.World) → Maybe (Seen world)
  observe world = valueAt world (DB.lookup slot world) refl

  replacement : ∀ {world} → Seen world → O.Record
  replacement current = O.recordOf owner (body (update now observation (Seen.control current)))

  changed : ∀ world → Seen world → O.World
  changed world current = DB.write slot (replacement current) world

  follow : ∀ world → Seen world → Ledger.Effect
  follow world current with newRetirement now observation (Seen.control current)
  ... | true = Tasks.effect id payload checkpoint guidance
  ... | false = record { transaction = DB.commit checkpoint; guidance = guidance; isolates = noopFrame checkpoint }

  finishWorld : ∀ world → Seen world → O.World
  finishWorld world current with newRetirement now observation (Seen.control current)
  ... | true = Capture.created id (Allocation.freshId (changed world current)) payload (changed world current)
  ... | false = changed world current

  follows : ∀ world current → DB.evaluate (Ledger.Effect.transaction (follow world current)) (changed world current) ≡
    DB.committed checkpoint (finishWorld world current)
  follows world current with newRetirement now observation (Seen.control current)
  ... | true = Tasks.creates id payload checkpoint (changed world current)
  ... | false = refl

  snapshot : (world : O.World) → Maybe (Seen world) → DB.Transaction String
  snapshot world nothing = DB.abort continuation
  snapshot world (just current) = DB.put slot (replacement current) (Ledger.Effect.transaction (follow world current))

  transaction : DB.Transaction String
  transaction = DB.scan (λ world → snapshot world (observe world))

  controlFrame : ∀ world current → Ledger.ReceiptFrame world (changed world current)
  controlFrame world current = writeFrame world slot (O.recordOf owner (body (Seen.control current))) (replacement current)
    (Seen.located current) (noReceipt (Seen.control current)) (noReceipt (update now observation (Seen.control current)))

  isolates : ∀ before result after → DB.evaluate transaction before ≡ DB.committed result after → Ledger.ReceiptFrame before after
  isolates before result after committed with observe before
  ... | nothing with committed
  ...   | ()
  isolates before result after committed | just current = Publication.composeFrames before (changed before current) after
    (controlFrame before current) (Ledger.Effect.isolates (follow before current) (changed before current) result after committed)

  effect : Ledger.Effect
  effect = record { transaction = transaction; guidance = guidance; isolates = isolates }

  module Current (before : O.World) (validBefore : O.Admissible before) (current : Seen before) (observed : observe before ≡ just current) where
    updated = replacement current
    middle = changed before current
    rawAfter = finishWorld before current

    middleValid : O.Admissible middle
    middleValid = Storage.writeAdmissible before slot (O.recordOf owner (body (Seen.control current))) updated validBefore
      (Seen.located current) refl (sameKind now observation (Seen.control current))
      (placed (E.family selection) (update now observation (Seen.control current)))
      (referenceSubset (Seen.control current) (update now observation (Seen.control current)))

    rawValid : O.Admissible rawAfter
    rawValid with newRetirement now observation (Seen.control current)
    ... | true = Insert.insertAdmissible middle (Allocation.freshId middle) (Capture.task id (Allocation.freshId middle) payload middle)
      middleValid (Allocation.fresh middle) O.local All.[] All.[]
    ... | false = middleValid

    performs : DB.evaluate transaction before ≡ DB.committed checkpoint rawAfter
    performs rewrite observed = follows before current

    lifecycle : state (update now observation (Seen.control current)) ≡ Life.inspect now observation (state (Seen.control current))
    lifecycle = matches now observation (Seen.control current)

    controlVisible : DB.lookup slot rawAfter ≡ just updated
    controlVisible with newRetirement now observation (Seen.control current)
    ... | true = Insert.oldLookup middle (Allocation.freshId middle) (Capture.task id (Allocation.freshId middle) payload middle)
      (Allocation.fresh middle) slot updated (DB.writeVisible slot updated before)
    ... | false = DB.writeVisible slot updated before

    otherRecord : ∀ key value → key ≢ slot → DB.lookup key before ≡ just value → DB.lookup key rawAfter ≡ just value
    otherRecord key value distinct found with newRetirement now observation (Seen.control current)
    ... | true = Insert.oldLookup middle (Allocation.freshId middle) (Capture.task id (Allocation.freshId middle) payload middle)
      (Allocation.fresh middle) key value (trans (DB.writePreservesOther slot key updated before (λ same → distinct (sym same))) found)
    ... | false = trans (DB.writePreservesOther slot key updated before (λ same → distinct (sym same))) found

    cleanupCaptured : newRetirement now observation (Seen.control current) ≡ true →
      DB.lookup (Allocation.freshId middle) rawAfter ≡ just (Capture.task id (Allocation.freshId middle) payload middle)
    cleanupCaptured retiring with newRetirement now observation (Seen.control current)
    ... | true = DB.writeVisible (Allocation.freshId middle) (Capture.task id (Allocation.freshId middle) payload middle) middle
    ... | false with retiring
    ...   | ()

    registrationBeforeCleanup : ∀ key info → DB.lookup key rawAfter ≡ just (O.recordOf owner (O.registration info)) →
      DB.lookup key middle ≡ just (O.recordOf owner (O.registration info))
    registrationBeforeCleanup key info found with newRetirement now observation (Seen.control current)
    ... | true = writeBackward middle (Allocation.freshId middle) (Capture.task id (Allocation.freshId middle) payload middle) key _ (λ ()) found
    ... | false = found

    otherBeforeCleanup : ∀ key value → Allocation.freshId middle ≢ key → DB.lookup key rawAfter ≡ just value → DB.lookup key middle ≡ just value
    otherBeforeCleanup key value different found with newRetirement now observation (Seen.control current)
    ... | true = trans (sym (DB.writePreservesOther (Allocation.freshId middle) key (Capture.task id (Allocation.freshId middle) payload middle) middle different)) found
    ... | false = found

    module Run (input : Identity.Meaning) (names : R.Names id input)
      (receiptSlot : ℕ) (progress : R.Work)
      (located : DB.lookup receiptSlot before ≡ just (Ledger.recordAt {id = id} owner (R.active input names progress)))
      (foundHere : Ledger.find id before ≡ just (Ledger.found receiptSlot owner (R.active input names progress))) where
      -- Cleanup itself has no need to pin the old derived versions. The request
      -- stays active until the existing finalizer verifies all its tasks done.
      change = Ledger.checkpoint []
      next = R.nextWork progress [] checkpoint
      oldReceipt = Ledger.recordAt {id = id} owner (R.active input names progress)
      newReceipt = Ledger.recordAt {id = id} owner (R.active input names next)
      after = DB.write receiptSlot newReceipt rawAfter
      request = Ledger.update id input (R.generation progress) change effect

      commits : DB.execute request before ≡ (Ledger.resume receiptSlot next , after)
      commits = Ledger.committedUpdate id input names change effect receiptSlot owner progress before checkpoint rawAfter foundHere performs

      oldReceiptAt : DB.lookup receiptSlot rawAfter ≡ just oldReceipt
      oldReceiptAt = proj₁ (isolates before checkpoint rawAfter performs receiptSlot owner (R.entry id (R.active input names progress))) located

      afterValid : O.Admissible after
      afterValid = Storage.writeAdmissible rawAfter receiptSlot oldReceipt newReceipt rawValid oldReceiptAt refl refl tt (λ ref ())

      controlNotReceipt : O.kind (O.body updated) ≢ O.receiptK
      controlNotReceipt = noReceipt (update now observation (Seen.control current))

      controlDistinct : receiptSlot ≢ slot
      controlDistinct same = Publication.lookupDistinct rawAfter slot updated receiptSlot oldReceipt controlVisible oldReceiptAt controlNotReceipt (sym same)

      savedControl : DB.lookup slot after ≡ just updated
      savedControl = trans (DB.writePreservesOther receiptSlot slot newReceipt rawAfter controlDistinct) controlVisible

      savedCleanup : newRetirement now observation (Seen.control current) ≡ true →
        DB.lookup (Allocation.freshId middle) after ≡ just (Capture.task id (Allocation.freshId middle) payload middle)
      savedCleanup retiring = trans
        (DB.writePreservesOther receiptSlot (Allocation.freshId middle) newReceipt rawAfter
          (Publication.lookupDistinct rawAfter receiptSlot oldReceipt (Allocation.freshId middle) _ oldReceiptAt (cleanupCaptured retiring) (λ ())))
        (cleanupCaptured retiring)

      retainedOtherKey : ∀ key value → key ≢ slot → receiptSlot ≢ key →
        DB.lookup key before ≡ just value → DB.lookup key after ≡ just value
      retainedOtherKey key value controlOther receiptOther found = trans
        (DB.writePreservesOther receiptSlot key newReceipt rawAfter receiptOther)
        (otherRecord key value controlOther found)

      otherOwnerControlDistinct : ∀ key value → O.owner value ≢ owner → DB.lookup key before ≡ just value → key ≢ slot
      otherOwnerControlDistinct .slot value other found refl = other
        (cong O.owner (just-injective (trans (sym found) (Seen.located current))))

      otherOwnerReceiptDistinct : ∀ key value → O.owner value ≢ owner → DB.lookup key before ≡ just value → receiptSlot ≢ key
      otherOwnerReceiptDistinct .receiptSlot value other found refl = other
        (cong O.owner (just-injective (trans (sym found) located)))

      familyIsolation : ∀ key value → O.owner value ≢ owner → DB.lookup key before ≡ just value → DB.lookup key after ≡ just value
      familyIsolation key value other found = retainedOtherKey key value
        (otherOwnerControlDistinct key value other found) (otherOwnerReceiptDistinct key value other found) found

      NotesAndSettings : O.Record → Set
      NotesAndSettings value = O.kind (O.body value) ≢ O.registrationK × O.kind (O.body value) ≢ O.checkoutK × O.kind (O.body value) ≢ O.receiptK

      controlDifferent : ∀ value → NotesAndSettings value → O.kind (body (Seen.control current)) ≢ O.kind (O.body value)
      controlDifferent value different with Seen.control current
      ... | registration info = λ same → proj₁ different (sym same)
      ... | checkout info = λ same → proj₁ (proj₂ different) (sym same)

      preserveNotesAndSettings : ∀ key value → NotesAndSettings value → DB.lookup key before ≡ just value → DB.lookup key after ≡ just value
      preserveNotesAndSettings key value different found = retainedOtherKey key value
        (λ same → Publication.lookupDistinct before slot _ key value (Seen.located current) found (controlDifferent value different) (sym same))
        (Publication.lookupDistinct before receiptSlot oldReceipt key value located found (λ same → proj₂ (proj₂ different) (sym same))) found

      -- Registry uniqueness is the identity invariant supplied by #32. No
      -- evidence-source choice is introduced by consuming that invariant here.
      OneRegistration : Set
      OneRegistration = ∀ key info → DB.lookup key before ≡ just (O.recordOf owner (O.registration info)) → key ≡ slot

      familyRetired : ∀ newInfo → updated ≡ O.recordOf owner (O.registration newInfo) →
        O.RegistrationInfo.retired newInfo ≡ true → OneRegistration → E.Model.familyRegistered selection after ≡ false
      familyRetired newInfo rowIsRegistration retired one = Reclaim.allRegistrationsRetired selection after (O.Admissible.unique afterValid) eachRetired
        where
        eachRetired : ∀ key info → DB.lookup key after ≡ just (O.recordOf owner (O.registration info)) → O.RegistrationInfo.retired info ≡ true
        eachRetired key info found with slot ≟ key
        ... | yes refl = trans
          (cong O.RegistrationInfo.retired (registrationInjective owner info newInfo
            (trans (sym (just-injective (trans (sym savedControl) found))) rowIsRegistration))) retired
        ... | no different = ⊥-elim (different (sym (one key info original)))
          where
          rawFound = writeBackward rawAfter receiptSlot newReceipt key _ (λ ()) found
          middleFound = registrationBeforeCleanup key info rawFound
          original = trans (sym (DB.writePreservesOther slot key updated before different)) middleFound

      checkoutRetired : ∀ newInfo → updated ≡ O.recordOf owner (O.checkout newInfo) → O.CheckoutInfo.retired newInfo ≡ true →
        E.Model.checkoutLive selection after slot ≡ false
      checkoutRetired newInfo rowIsCheckout retired = Reclaim.checkoutUnavailable selection after slot newInfo
        (trans savedControl (cong just rowIsCheckout)) retired

      taskSlot = Allocation.freshId middle
      captured = Capture.ids taskSlot middle

      receiptInMiddle : DB.lookup receiptSlot middle ≡ just oldReceipt
      receiptInMiddle = proj₁ (controlFrame before current receiptSlot owner (R.entry id (R.active input names progress))) located

      coversFinal : ∀ key value → DB.lookup key after ≡ just value → O.owner value ≡ owner → key ∈ captured
      coversFinal key value found owned with receiptSlot ≟ key
      ... | yes refl = there (E.Model.captureComplete selection middle receiptSlot oldReceipt
        (Observations.lookupMember middle receiptSlot oldReceipt receiptInMiddle) refl)
      ... | no other with taskSlot ≟ key
      ...   | yes refl = here refl
      ...   | no different = there (E.Model.captureComplete selection middle key value
        (Observations.lookupMember middle key value (otherBeforeCleanup key value different rawFound)) owned)
        where rawFound = trans (sym (DB.writePreservesOther receiptSlot key newReceipt rawAfter other)) found

      intent : E.Model.Intent selection after
      intent = record
        { keys = captured; uniqueBefore = O.Admissible.unique afterValid
        ; covers = λ key value present owned → coversFinal key value
            (Order.memberLookup after key value (O.Admissible.unique afterValid) present) owned }

      durableCleanup : newRetirement now observation (Seen.control current) ≡ true →
        DB.lookup taskSlot after ≡ just (O.recordOf owner (O.cleanupWork id (E.Model.Intent.keys intent) payload))
      durableCleanup = savedCleanup

      module Worker = Finalization.Model.Task selection after intent id taskSlot
      module Reclamation = Reclaim.Cleanup selection after intent

      receiptWritten : Ledger.find id after ≡ just (Ledger.found receiptSlot owner (R.active input names next))
      receiptWritten = Ledger.writtenReceiptVisible id receiptSlot owner (R.active input names next) rawAfter

      retry : DB.execute request after ≡ (Ledger.resume receiptSlot next , after)
      retry = Ledger.staleStepSkipsEffect id input names (R.generation progress) change effect receiptSlot owner next after receiptWritten
        (Ledger.nextGenerationDifferent (R.generation progress))

      boundary : ∀ observedWorld → Exec.Interrupted (Exec.atomic request Exec.done) before observedWorld →
        (observedWorld ≡ before) ⊎ (observedWorld ≡ after)
      boundary observedWorld interrupted with Ledger.atomicBoundary request before observedWorld interrupted
      ... | inj₁ same = inj₁ same
      ... | inj₂ same = inj₂ (trans same (cong proj₂ commits))

      completedAtomic : ∀ observedWorld reply final → Exec.Completed (Exec.atomic request Exec.done) observedWorld reply final →
        DB.execute request observedWorld ≡ (reply , final)
      completedAtomic observedWorld reply final (Exec.committed Exec.stop) = refl

      converges : ∀ observedWorld final reply → Exec.Interrupted (Exec.atomic request Exec.done) before observedWorld →
        Exec.Completed (Exec.atomic request Exec.done) observedWorld reply final → final ≡ after
      converges observedWorld final reply interrupted completed with boundary observedWorld interrupted
      ... | inj₁ same = trans (sym (cong proj₂ (completedAtomic observedWorld reply final completed)))
        (trans (cong (λ world → proj₂ (DB.execute request world)) same) (cong proj₂ commits))
      ... | inj₂ same = trans (sym (cong proj₂ (completedAtomic observedWorld reply final completed)))
        (trans (cong (λ world → proj₂ (DB.execute request world)) same) (cong proj₂ retry))

      completes : ∀ world → Σ Ledger.Reply (λ reply → Σ O.World (λ final → Exec.Completed (Exec.atomic request Exec.done) world reply final))
      completes world = proj₁ (DB.execute request world) , proj₂ (DB.execute request world) , Exec.committed Exec.stop
