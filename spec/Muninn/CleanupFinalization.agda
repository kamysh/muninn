{-# OPTIONS --safe #-}
-- Verify the actual fixed workset before removing its own private task.
module Muninn.CleanupFinalization where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.ExclusionClassifier as C
import Muninn.CleanupCompletion as Completion
import Muninn.CleanupLoop as Loop
import Muninn.CleanupEffects as Effects
import Muninn.CleanupStorage as Storage
import Muninn.FiniteClosure as F
import Muninn.ReceiptLedger as Ledger
import Muninn.ReceiptTypes as R
import Muninn.CatalogInputs as I
import Muninn.RequestIdentity as Identity
import Muninn.Dialogue as D
open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (Bool; true)
open import Data.String using (String)
open import Data.List using (List; [])
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Relation.Unary.All as All
open All using (All)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; cong; subst)
module DB = O.DB
module Exec = O.Execution

taskIdentity : O.Body → Maybe (I.OperationId × List ℕ)
taskIdentity (O.cleanupWork id captured payload) = just (id , captured)
taskIdentity _ = nothing

taskIdentity? : ∀ id captured body → Dec (taskIdentity body ≡ just (id , captured))
taskIdentity? id captured body with taskIdentity body
... | nothing = no (λ ())
... | just (storedId , storedKeys) with Ledger.sameId storedId id | Effects.listEqual storedKeys captured
...   | yes refl | yes refl = yes refl
...   | no different | _ = no (λ same → different (cong proj₁ (just-injective same)))
...   | _ | no different = no (λ same → different (cong proj₂ (just-injective same)))

taskBody : ∀ body id captured → taskIdentity body ≡ just (id , captured) →
  Σ String (λ payload → body ≡ O.cleanupWork id captured payload)
taskBody (O.cleanupWork storedId storedKeys payload) id captured same with just-injective same
... | refl = payload , refl

module Model (excluded : List String → String → Bool) where
  module M = E.Model excluded

  module Task (selection : E.Rule) (accepted : O.World) (intent : M.Intent selection accepted)
    (id : I.OperationId) (slot : ℕ) where
    module Final = Completion.Model.Contract excluded selection accepted intent
    owner = E.targetOwner selection
    captured = M.Intent.keys intent

    -- The finite decision is complete because Pending already requires capture membership.
    noPending? : ∀ world → Dec (Final.NoPending world)
    noPending? world with F.choose (λ key → Final.Pending key world) (λ key → Final.pending? key world) captured
    ... | yes (key , included , pending) = no (λ none → none key pending)
    ... | no absent = yes (λ key pending → absent (key , Final.pendingCaptured key world pending , pending))

    TaskAt : O.World → Set
    TaskAt world = C.At world slot (λ value → O.owner value ≡ owner × taskIdentity (O.body value) ≡ just (id , captured))

    taskAt? : ∀ world → Dec (TaskAt world)
    taskAt? world = C.at? world slot _ (λ value → C.both (E.ownerEqual (O.owner value) owner) (taskIdentity? id captured (O.body value)))

    savedRecord : ∀ world → TaskAt world →
      Σ String (λ payload → DB.lookup slot world ≡ just (O.recordOf owner (O.cleanupWork id captured payload)))
    savedRecord world (O.recordOf storedOwner body , found , owned , matches) with taskBody body id captured matches
    ... | payload , refl rewrite owned = payload , found

    Ready : O.World → Set
    Ready world = TaskAt world × Final.NoPending world

    ready? : ∀ world → Dec (Ready world)
    ready? world = C.both (taskAt? world) (noPending? world)

    finishSnapshot : String → String → O.World → DB.Transaction String
    finishSnapshot result continuation world with ready? world
    ... | yes verified = DB.remove slot (DB.commit result)
    ... | no remaining = DB.abort continuation

    finish : String → String → DB.Transaction String
    finish result continuation = DB.scan (finishSnapshot result continuation)

    performs : ∀ world result continuation → Ready world →
      DB.evaluate (finish result continuation) world ≡ DB.committed result (DB.delete slot world)
    performs world result continuation verified with ready? world
    ... | yes same = refl
    ... | no remaining = ⊥-elim (remaining verified)

    continues : ∀ world result continuation → ¬ Ready world →
      DB.evaluate (finish result continuation) world ≡ DB.aborted continuation
    continues world result continuation remaining with ready? world
    ... | yes verified = ⊥-elim (remaining verified)
    ... | no same = refl

    committedReady : ∀ world result continuation reply after →
      DB.evaluate (finish result continuation) world ≡ DB.committed reply after →
      Ready world × after ≡ DB.delete slot world
    committedReady world result continuation reply after committed with ready? world
    ... | yes verified with committed
    ...   | refl = verified , refl
    committedReady world result continuation reply after committed | no remaining = impossible committed
      where impossible : DB.aborted continuation ≡ DB.committed reply after → Ready world × after ≡ DB.delete slot world
            impossible ()

    deleteAdmissible : ∀ world → O.Admissible world → TaskAt world → O.Admissible (DB.delete slot world)
    deleteAdmissible world valid actual with savedRecord world actual
    ... | payload , found = O.deleteUnreferencedPreservesAdmissibility slot world valid
      (O.privateUnreferenced slot world (O.recordOf owner (O.cleanupWork id captured payload)) valid found refl)

    -- A private task cannot be confused with any indexed row, other task or receipt.
    otherRow : ∀ world → TaskAt world → ∀ key value →
      DB.lookup key world ≡ just value → key ≢ slot → DB.lookup key (DB.delete slot world) ≡ just value
    otherRow world actual key value found distinct = trans
      (DB.deletePreservesOther slot key world (λ same → distinct (sym same))) found

    differentKind : ∀ world → TaskAt world → ∀ key value →
      DB.lookup key world ≡ just value → O.kind (O.body value) ≢ O.cleanupWorkK → key ≢ slot
    differentKind world actual .slot value found different refl with savedRecord world actual
    ... | payload , taskFound = different (cong (λ row → O.kind (O.body row)) (just-injective (trans (sym found) taskFound)))

    receiptFrame : ∀ world → TaskAt world → Ledger.ReceiptFrame world (DB.delete slot world)
    receiptFrame world actual key receiptOwner receiptData =
      (λ found → otherRow world actual key _ found (differentKind world actual key _ found (λ ()))) , backward
      where
      backward : DB.lookup key (DB.delete slot world) ≡ just (O.recordOf receiptOwner (O.receipt receiptData)) →
        DB.lookup key world ≡ just (O.recordOf receiptOwner (O.receipt receiptData))
      backward found with slot ≟ key
      ... | yes refl = ⊥-elim (Effects.presentNotAbsent (trans (sym found) (DB.deleteAbsent slot world)))
      ... | no different = trans (sym (DB.deletePreservesOther slot key world different)) found

    effect : String → String → (String → D.Prompt) → Ledger.Effect
    effect result continuation guidance = record
      { transaction = finish result continuation
      ; guidance = guidance
      ; isolates = λ world reply after committed →
          subst (Ledger.ReceiptFrame world) (sym (proj₂ (committedReady world result continuation reply after committed)))
            (receiptFrame world (proj₁ (proj₁ (committedReady world result continuation reply after committed))))
      }

    module Worker = Loop.Model.Run excluded selection accepted intent
    worked = Worker.Pass.Result.after (Worker.Pass.run accepted)
    trail = Worker.Pass.Result.trace (Worker.Pass.run accepted)

    readyAfterCleanup : O.Admissible accepted → TaskAt accepted →
      Worker.Use.Released accepted → Ready worked
    readyAfterCleanup valid actual released =
      (let saved = savedRecord accepted actual in (O.recordOf owner (O.cleanupWork id captured (proj₁ saved)) , Worker.Pass.traceMetadata trail slot _ (proj₂ saved) refl , refl , refl)) ,
      Worker.noPendingAtRest worked (Worker.Pass.traceAdmissible trail valid)
        (Worker.coveredTrace trail Worker.acceptedCovered)
        (Worker.Use.releasedTrace trail valid released)
        (Worker.Pass.Result.noEdit (Worker.Pass.run accepted))

    unresolvedKeepsWork : ∀ before result continuation guidance input names receiptSlot progress →
      ¬ Ready before →
      Ledger.find id before ≡ just (Ledger.found receiptSlot owner (R.active input names progress)) →
      DB.execute (Ledger.update id input (R.generation progress) Ledger.complete (effect result continuation guidance)) before ≡
        (Ledger.continueDialogue receiptSlot progress (guidance continuation) , before)
    unresolvedKeepsWork before result continuation guidance input names receiptSlot progress remaining foundHere
      rewrite foundHere with Identity.sameRequest input input
    ... | no different = ⊥-elim (different refl)
    ... | yes same with R.generation progress ≟ R.generation progress
    ...   | no different = ⊥-elim (different refl)
    ...   | yes generation =
      cong (λ outcome → DB.reply outcome , DB.publish before outcome) (Ledger.sealAborted receiptSlot (λ r → Ledger.recordAt {id = id} owner (R.finished input names r)) Ledger.saved (λ reason → Ledger.continueDialogue receiptSlot progress (guidance reason)) (finish result continuation) before continuation (continues before result continuation remaining))

    module Current (before : O.World) (valid : O.Admissible before) (verified : Ready before)
      (result continuation : String) (guidance : String → D.Prompt)
      (input : Identity.Meaning) (names : R.Names id input)
      (receiptSlot : ℕ) (progress : R.Work)
      (located : DB.lookup receiptSlot before ≡ just (Ledger.recordAt {id = id} owner (R.active input names progress)))
      (foundHere : Ledger.find id before ≡ just (Ledger.found receiptSlot owner (R.active input names progress))) where

      oldReceipt = Ledger.recordAt {id = id} owner (R.active input names progress)
      newReceipt = Ledger.recordAt {id = id} owner (R.finished input names result)
      cleaned = DB.delete slot before
      after = DB.write receiptSlot newReceipt cleaned
      work = effect result continuation guidance
      transaction = Ledger.update id input (R.generation progress) Ledger.complete work

      commits : DB.execute transaction before ≡ (Ledger.saved result , after)
      commits = Ledger.committedUpdate id input names Ledger.complete work receiptSlot owner progress before result cleaned foundHere
        (performs before result continuation verified)

      -- The completion contract is proved from the current decidable store check.
      checkedOutcome : M.Complete selection accepted intent before before
      checkedOutcome = Final.completeWithoutPending before (O.Admissible.unique valid) (proj₂ verified)

      receiptDistinct : receiptSlot ≢ slot
      receiptDistinct = differentKind before (proj₁ verified) receiptSlot oldReceipt located (λ ())

      cleanedValid : O.Admissible cleaned
      cleanedValid = deleteAdmissible before valid (proj₁ verified)

      afterValid : O.Admissible after
      afterValid = Storage.writeAdmissible cleaned receiptSlot oldReceipt newReceipt cleanedValid
        (otherRow before (proj₁ verified) receiptSlot oldReceipt located receiptDistinct)
        refl refl tt (λ ref ())

      taskRemoved : DB.lookup slot after ≡ nothing
      taskRemoved = trans (DB.writePreservesOther receiptSlot slot newReceipt cleaned receiptDistinct) (DB.deleteAbsent slot before)

      receiptFinished : Ledger.find id after ≡ just (Ledger.found receiptSlot owner (R.finished input names result))
      receiptFinished = Ledger.writtenReceiptVisible id receiptSlot owner (R.finished input names result) cleaned

      otherRecord : ∀ key value → key ≢ slot → key ≢ receiptSlot → DB.lookup key before ≡ just value → DB.lookup key after ≡ just value
      otherRecord key value notTask notReceipt found = trans
        (DB.writePreservesOther receiptSlot key newReceipt cleaned (λ same → notReceipt (sym same)))
        (otherRow before (proj₁ verified) key value found notTask)

      indexedRow : ∀ key value → DB.lookup key before ≡ just value → E.indexed value ≡ true → DB.lookup key after ≡ just value
      indexedRow key value found indexed = otherRecord key value
        (λ same → Effects.trueIsNotFalse (trans (sym indexed) (cong E.indexed (just-injective (trans (sym found) (trans (cong (λ key → DB.lookup key before) same) (proj₂ (savedRecord before (proj₁ verified)))))))))
        (λ same → Effects.trueIsNotFalse (trans (sym indexed) (cong E.indexed (just-injective (trans (sym found) (trans (cong (λ key → DB.lookup key before) same) located)))))) found

      otherReceipt : ∀ key receiptOwner receiptData → key ≢ receiptSlot →
        DB.lookup key before ≡ just (O.recordOf receiptOwner (O.receipt receiptData)) →
        DB.lookup key after ≡ just (O.recordOf receiptOwner (O.receipt receiptData))
      otherReceipt key receiptOwner receiptData notReceipt found = otherRecord key _ (differentKind before (proj₁ verified) key _ found (λ ())) notReceipt found

      retryObserved : ∀ observed → Ledger.find id observed ≡ just (Ledger.found receiptSlot owner (R.finished input names result)) →
        DB.execute transaction observed ≡ (Ledger.saved result , observed)
      retryObserved observed found = Ledger.finishedSkipsEffect id input names (R.generation progress) Ledger.complete work receiptSlot owner result observed found

      retry : DB.execute transaction after ≡ (Ledger.saved result , after)
      retry = retryObserved after receiptFinished

      atomicCompletion : ∀ observed → Exec.Interrupted (Exec.atomic transaction Exec.done) before observed →
        observed ≡ before ⊎ observed ≡ after
      atomicCompletion observed interrupted with Ledger.atomicBoundary transaction before observed interrupted
      ... | inj₁ same = inj₁ same
      ... | inj₂ same = inj₂ (trans same (cong proj₂ commits))

      completedAtomic : ∀ observed reply final → Exec.Completed (Exec.atomic transaction Exec.done) observed reply final →
        DB.execute transaction observed ≡ (reply , final)
      completedAtomic observed reply final (Exec.committed Exec.stop) = refl

      converges : ∀ observed final reply → Exec.Interrupted (Exec.atomic transaction Exec.done) before observed →
        Exec.Completed (Exec.atomic transaction Exec.done) observed reply final → final ≡ after
      converges observed final reply interrupted completed with atomicCompletion observed interrupted
      ... | inj₁ same = trans (sym (cong proj₂ (completedAtomic observed reply final completed)))
        (trans (cong (λ world → proj₂ (DB.execute transaction world)) same) (cong proj₂ commits))
      ... | inj₂ same = trans (sym (cong proj₂ (completedAtomic observed reply final completed)))
        (trans (cong (λ world → proj₂ (DB.execute transaction world)) same) (cong proj₂ retry))

      retainsUsedId : Ledger.find id (proj₂ (DB.execute (Ledger.reclaim id) after)) ≡ just (Ledger.found receiptSlot O.installation R.used)
      retainsUsedId = Ledger.reclaimRetainsId id after receiptSlot owner input names result receiptFinished


      reclaimCommits : DB.execute (Ledger.reclaim id) after ≡
        (Ledger.explain Ledger.historyReclaimed , DB.write receiptSlot (Ledger.markerAt id) after)
      reclaimCommits rewrite receiptFinished = refl

      taskAbsentAfterReclaim : DB.lookup slot (proj₂ (DB.execute (Ledger.reclaim id) after)) ≡ nothing
      taskAbsentAfterReclaim = trans (cong (λ outcome → DB.lookup slot (proj₂ outcome)) reclaimCommits)
        (trans (DB.writePreservesOther receiptSlot slot (Ledger.markerAt id) after receiptDistinct) taskRemoved)
