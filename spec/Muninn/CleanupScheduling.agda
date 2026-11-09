{-# OPTIONS --safe #-}
-- Save a bounded follow-up capture and its existing receipt checkpoint together.
module Muninn.CleanupScheduling where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.FiniteClosure as F
import Muninn.CleanupAdmissionStorage as Insert
import Muninn.CleanupStorage as Storage
import Muninn.CleanupObservations as Observations
import Muninn.CleanupOrder as Order
import Muninn.CleanupLoop as Loop
import Muninn.ReceiptLedger as Ledger
import Muninn.ReceiptTypes as R
import Muninn.Dialogue as D
import Muninn.CatalogInputs as I
import Muninn.RequestIdentity as Identity
open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (Bool)
open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.All as All
open All using (All; [])
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; cong; subst)
module DB = O.DB
module Exec = O.Execution

module Model (excluded : List String → String → Bool) where
  module M = E.Model excluded

  module Family (selection : E.Rule) where
    owner = E.targetOwner selection

    ids : ℕ → O.World → List ℕ
    ids slot world = slot ∷ M.capture selection world

    task : ℕ → String → O.World → O.Record
    task slot payload world = O.recordOf owner (O.cleanupWork (ids slot world) payload)

    created : ℕ → String → O.World → O.World
    created slot payload world = DB.write slot (task slot payload world) world

    createSnapshot : ℕ → String → String → O.World → DB.Transaction String
    createSnapshot slot payload checkpoint world with F.member slot (Insert.reserved world)
    ... | yes reserved = DB.abort checkpoint
    ... | no fresh = DB.put slot (task slot payload world) (DB.commit checkpoint)

    create : ℕ → String → String → DB.Transaction String
    create slot payload checkpoint = DB.scan (createSnapshot slot payload checkpoint)

    creates : ∀ slot payload checkpoint world → Insert.Fresh world slot →
      DB.evaluate (create slot payload checkpoint) world ≡ DB.committed checkpoint (created slot payload world)
    creates slot payload checkpoint world fresh with F.member slot (Insert.reserved world)
    ... | yes reserved = ⊥-elim (fresh reserved)
    ... | no same = refl

    insertedReceipts : ∀ slot payload world → Insert.Fresh world slot → Ledger.ReceiptFrame world (created slot payload world)
    insertedReceipts slot payload world fresh other recordOwner receiptData =
      Insert.oldLookup world slot (task slot payload world) fresh other (O.recordOf recordOwner (O.receipt receiptData)) , backward
      where
      disjoint : task slot payload world ≢ O.recordOf recordOwner (O.receipt receiptData)
      disjoint ()
      backward : DB.lookup other (created slot payload world) ≡ just (O.recordOf recordOwner (O.receipt receiptData)) →
        DB.lookup other world ≡ just (O.recordOf recordOwner (O.receipt receiptData))
      backward found with slot ≟ other
      ... | no different = trans (sym (DB.writePreservesOther slot other (task slot payload world) world different)) found
      ... | yes same = ⊥-elim (disjoint (just-injective (trans (sym (DB.writeVisible slot (task slot payload world) world))
        (trans (cong (λ key → DB.lookup key (created slot payload world)) same) found))))

    isolates : ∀ slot payload checkpoint before result after →
      DB.evaluate (create slot payload checkpoint) before ≡ DB.committed result after → Ledger.ReceiptFrame before after
    isolates slot payload checkpoint before result after committed with F.member slot (Insert.reserved before)
    ... | yes reserved = impossible committed
      where impossible : DB.aborted checkpoint ≡ DB.committed result after → Ledger.ReceiptFrame before after
            impossible ()
    ... | no fresh with committed
    ...   | refl = insertedReceipts slot payload before fresh

    effect : ℕ → String → String → (String → D.Prompt) → Ledger.Effect
    effect slot payload checkpoint guidance = record
      { transaction = create slot payload checkpoint; guidance = guidance
      ; isolates = isolates slot payload checkpoint }

    module Current (before : O.World) (valid : O.Admissible before)
      (slot : ℕ) (payload checkpoint : String) (guidance : String → D.Prompt)
      (fresh : Insert.Fresh before slot)
      (id : I.OperationId) (input : Identity.Meaning) (names : R.Names id input)
      (receiptSlot : ℕ) (progress : R.Work)
      (located : DB.lookup receiptSlot before ≡ just (Ledger.recordAt {id = id} owner (R.active input names progress)))
      (foundHere : Ledger.find id before ≡ just (Ledger.found receiptSlot owner (R.active input names progress))) where

      oldReceipt = Ledger.recordAt {id = id} owner (R.active input names progress)
      next = R.nextWork progress (R.versions progress) checkpoint
      newReceipt = Ledger.recordAt {id = id} owner (R.active input names next)
      captured = ids slot before
      inserted = created slot payload before
      after = DB.write receiptSlot newReceipt inserted
      change = Ledger.checkpoint (R.versions progress)
      work = effect slot payload checkpoint guidance
      transaction = Ledger.update id input (R.generation progress) change work

      commits : DB.execute transaction before ≡ (Ledger.resume receiptSlot next , after)
      commits = Ledger.committedUpdate id input names change work receiptSlot owner progress before checkpoint inserted foundHere
        (creates slot payload checkpoint before fresh)

      receiptDistinct : receiptSlot ≢ slot
      receiptDistinct refl = fresh (Insert.storedReserved before slot oldReceipt located)

      insertedValid : O.Admissible inserted
      insertedValid = Insert.insertAdmissible before slot (task slot payload before) valid fresh O.local [] []

      afterValid : O.Admissible after
      afterValid = Storage.writeAdmissible inserted receiptSlot oldReceipt newReceipt insertedValid
        (Insert.oldLookup before slot (task slot payload before) fresh receiptSlot oldReceipt located)
        refl refl tt (λ ref included → included)

      coveredInserted : ∀ key value → DB.lookup key inserted ≡ just value → O.owner value ≡ owner → key ∈ captured
      coveredInserted key value present owned with slot ≟ key
      ... | yes refl = here refl
      ... | no different = there (M.captureComplete selection before key value (Observations.lookupMember before key value
        (trans (sym (DB.writePreservesOther slot key (task slot payload before) before different)) present)) owned)

      covered : ∀ key value → DB.lookup key after ≡ just value → O.owner value ≡ owner → key ∈ captured
      covered key value present owned with receiptSlot ≟ key
      ... | yes refl = there (M.captureComplete selection before receiptSlot oldReceipt (Observations.lookupMember before receiptSlot oldReceipt located) refl)
      ... | no different = coveredInserted key value (trans (sym (DB.writePreservesOther receiptSlot key newReceipt inserted different)) present) owned

      intent : M.Intent selection after
      intent = record
        { keys = captured; uniqueBefore = O.Admissible.unique afterValid
        ; covers = λ key value present owned → covered key value (Order.memberLookup after key value (O.Admissible.unique afterValid) present) owned }

      savedCapture : DB.lookup slot after ≡ just (O.recordOf owner (O.cleanupWork (M.Intent.keys intent) payload))
      savedCapture = trans (DB.writePreservesOther receiptSlot slot newReceipt inserted receiptDistinct)
        (DB.writeVisible slot (task slot payload before) before)

      savedOriginalWorkset : ∀ original ids note → DB.lookup original before ≡ just (O.recordOf owner (O.cleanupWork ids note)) →
        DB.lookup original after ≡ just (O.recordOf owner (O.cleanupWork ids note))
      savedOriginalWorkset original ids note present = trans (DB.writePreservesOther receiptSlot original newReceipt inserted different)
        (Insert.oldLookup before slot (task slot payload before) fresh original _ present)
        where
        different : receiptSlot ≢ original
        different refl = impossible (just-injective (trans (sym located) present))
          where impossible : oldReceipt ≢ O.recordOf owner (O.cleanupWork ids note)
                impossible ()

      retryObserved : ∀ observed → Ledger.find id observed ≡ just (Ledger.found receiptSlot owner (R.active input names next)) →
        DB.execute transaction observed ≡ (Ledger.resume receiptSlot next , observed)
      retryObserved observed found = Ledger.staleStepSkipsEffect id input names (R.generation progress) change work receiptSlot owner next observed found
        (Ledger.nextGenerationDifferent (R.generation progress))

      retry : DB.execute transaction after ≡ (Ledger.resume receiptSlot next , after)
      retry = retryObserved after (Ledger.writtenReceiptVisible id receiptSlot owner (R.active input names next) inserted)

      retryKeepsCapture : DB.lookup slot (proj₂ (DB.execute transaction after)) ≡ just (O.recordOf owner (O.cleanupWork captured payload))
      retryKeepsCapture = trans (cong (λ result → DB.lookup slot (proj₂ result)) retry) savedCapture

      atomicCapture : ∀ observed → Exec.Interrupted (Exec.atomic transaction Exec.done) before observed → (observed ≡ before) ⊎ (observed ≡ after)
      atomicCapture observed interrupted with Ledger.atomicBoundary transaction before observed interrupted
      ... | inj₁ same = inj₁ same
      ... | inj₂ same = inj₂ (trans same (cong proj₂ commits))

      completedAtomic : ∀ observed reply final → Exec.Completed (Exec.atomic transaction Exec.done) observed reply final →
        DB.execute transaction observed ≡ (reply , final)
      completedAtomic observed reply final (Exec.committed Exec.stop) = refl

      converges : ∀ observed final reply → Exec.Interrupted (Exec.atomic transaction Exec.done) before observed →
        Exec.Completed (Exec.atomic transaction Exec.done) observed reply final → final ≡ after
      converges observed final reply interrupted completed with atomicCapture observed interrupted
      ... | inj₁ same = trans (sym (cong proj₂ (completedAtomic observed reply final completed)))
        (trans (cong (λ world → proj₂ (DB.execute transaction world)) same) (cong proj₂ commits))
      ... | inj₂ same = trans (sym (cong proj₂ (completedAtomic observed reply final completed)))
        (trans (cong (λ world → proj₂ (DB.execute transaction world)) same) (cong proj₂ retry))

      module Worker = Loop.Model.Run excluded selection after intent

      cleanupComplete : Worker.Use.Released after → M.Complete selection after intent after (Worker.Pass.Result.after (Worker.Pass.run after))
      cleanupComplete = Worker.finishes afterValid

      persistsThroughCleanup : ∀ {count final} → Worker.Pass.Trace count after final →
        DB.lookup slot final ≡ just (O.recordOf owner (O.cleanupWork captured payload))
      persistsThroughCleanup trace = Worker.Pass.traceMetadata trace slot _ savedCapture refl
