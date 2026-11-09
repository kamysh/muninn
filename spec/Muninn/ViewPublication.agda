{-# OPTIONS --safe #-}
-- One shared commit: filtered copy, current selector, original receipt checkpoint.
module Muninn.ViewPublication where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.CleanupStorage as Storage
import Muninn.CleanupAdmissionStorage as Insert
import Muninn.CleanupObservations as Observations
import Muninn.RecordAllocation as Allocation
import Muninn.SnapshotPreparation as Preparation
import Muninn.ViewReplacement as Replacement
import Muninn.PublicationVisibility as Visibility
import Muninn.PublishedViews as Views
import Muninn.ReceiptLedger as Ledger
import Muninn.ReceiptTypes as R
import Muninn.CatalogInputs as I
import Muninn.RequestIdentity as Identity
import Muninn.Dialogue as D
open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (Bool; true)
open import Data.String using (String)
open import Data.List using (List; [])
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
module DB = O.DB
module Exec = O.Execution

composeFrames : ∀ before middle after → Ledger.ReceiptFrame before middle →
  Ledger.ReceiptFrame middle after → Ledger.ReceiptFrame before after
composeFrames before middle after first second key owner receiptData =
  (λ found → proj₁ (second key owner receiptData) (proj₁ (first key owner receiptData) found)) ,
  (λ found → proj₂ (first key owner receiptData) (proj₂ (second key owner receiptData) found))

insertSnapshotFrame : ∀ world slot copied → Insert.Fresh world slot →
  O.kind (O.body copied) ≡ O.structuralSnapshotK →
  Ledger.ReceiptFrame world (DB.write slot copied world)
insertSnapshotFrame world slot copied fresh kind key owner receiptData =
  Insert.oldLookup world slot copied fresh key _ , backward
  where
  backward : DB.lookup key (DB.write slot copied world) ≡ just (O.recordOf owner (O.receipt receiptData)) →
    DB.lookup key world ≡ just (O.recordOf owner (O.receipt receiptData))
  backward found with slot ≟ key
  ... | yes refl = ⊥-elim (impossible (trans (sym kind)
      (cong (λ value → O.kind (O.body value))
        (just-injective (trans (sym (DB.writeVisible slot copied world)) found)))))
    where impossible : O.structuralSnapshotK ≢ O.receiptK
          impossible ()
  ... | no different = trans (sym (DB.writePreservesOther slot key copied world different)) found

lookupDistinct : ∀ world key old other value → DB.lookup key world ≡ just old →
  DB.lookup other world ≡ just value → O.kind (O.body old) ≢ O.kind (O.body value) → key ≢ other
lookupDistinct world key old .key value oldFound found different refl =
  different (cong (λ row → O.kind (O.body row)) (just-injective (trans (sym oldFound) found)))

module Model where
  module M = E.Model
  module Store = Storage.Model

  module Family (selection : E.Rule) where
    owner = E.targetOwner selection
    module Prepare = Preparation.Model.Family selection
    module Replace = Replacement.Model.Family selection

    module Publication (pointer source selected : ℕ) (result continuation : String) where
      next : ℕ → DB.Transaction String
      next fresh = Replace.Selector.replace pointer source fresh selected result continuation

      transaction : DB.Transaction String
      transaction = Prepare.prepare source next (λ world → DB.abort continuation)

      isolates : ∀ before reply after → DB.evaluate transaction before ≡ DB.committed reply after →
        Ledger.ReceiptFrame before after
      isolates before reply after committed with DB.lookup source before
      ... | nothing = impossible committed
        where impossible : DB.aborted continuation ≡ DB.committed reply after → Ledger.ReceiptFrame before after
              impossible ()
      ... | just value with Observations.snapshotView value
      ...   | Observations.plain nonSnapshot = impossible committed
        where impossible : DB.aborted continuation ≡ DB.committed reply after → Ledger.ReceiptFrame before after
              impossible ()
      ...   | Observations.delta sourceOwner checkout version path answer = impossible committed
        where impossible : DB.aborted continuation ≡ DB.committed reply after → Ledger.ReceiptFrame before after
              impossible ()
      ...   | Observations.snapshot sourceOwner checkout nodes edges payload with E.ownerEqual sourceOwner owner
      ...     | no different = impossible committed
        where impossible : DB.aborted continuation ≡ DB.committed reply after → Ledger.ReceiptFrame before after
              impossible ()
      ...     | yes same = composeFrames before inserted after
        (insertSnapshotFrame before fresh copied (Allocation.fresh before)
          (Store.projectKind selection before original))
        (subst (Ledger.ReceiptFrame inserted)
          (sym (proj₂ (Swapped.committedReady inserted result continuation reply after committed)))
          (Swapped.guardedReceiptFrame inserted
            (proj₁ (Swapped.committedReady inserted result continuation reply after committed))))
        where
        fresh = Allocation.freshId before
        original = O.recordOf sourceOwner (O.structuralSnapshot checkout nodes edges payload)
        copied = M.project selection before original
        inserted = DB.write fresh copied before
        module Swapped = Replace.Selector pointer source fresh selected

      effect : (String → D.Prompt) → Ledger.Effect
      effect guidance = record { transaction = transaction; guidance = guidance; isolates = isolates }

      unresolvedKeepsWork : ∀ before guidance id input names receiptSlot progress →
        DB.evaluate transaction before ≡ DB.aborted continuation →
        Ledger.find id before ≡ just (Ledger.found receiptSlot owner (R.active input names progress)) →
        DB.execute (Ledger.update id input (R.generation progress) (Ledger.checkpoint (R.versions progress)) (effect guidance)) before ≡
          (Ledger.continueDialogue receiptSlot progress (guidance continuation) , before)
      unresolvedKeepsWork before guidance id input names receiptSlot progress unresolved foundHere
        rewrite foundHere with Identity.sameRequest input input
      ... | no different = ⊥-elim (different refl)
      ... | yes same with R.generation progress ≟ R.generation progress
      ...   | no different = ⊥-elim (different refl)
      ...   | yes generation = cong (λ outcome → DB.reply outcome , DB.publish before outcome)
        (Ledger.sealAborted receiptSlot
          (λ r → Ledger.recordAt {id = id} owner (Ledger.updatedState (Ledger.checkpoint (R.versions progress)) input names progress r))
          (Ledger.updatedReply (Ledger.checkpoint (R.versions progress)) receiptSlot progress)
          (λ reason → Ledger.continueDialogue receiptSlot progress (guidance reason)) transaction before continuation unresolved)

      module Current (before : O.World) (valid : O.Admissible before) (viewsValid : Views.Valid before)
        (nodes edges : List ℕ) (payload : String)
        (sourceFound : DB.lookup source before ≡ just (O.recordOf owner (O.structuralSnapshot selected nodes edges payload)))
        (published : DB.lookup pointer before ≡ just (O.recordOf owner (O.publishedView selected source)))
        (registered : M.familyRegistered selection before ≡ true) (live : M.checkoutLive selection before selected ≡ true)
        (guidance : String → D.Prompt)
        (id : I.OperationId) (input : Identity.Meaning) (names : R.Names id input)
        (receiptSlot : ℕ) (progress : R.Work)
        (located : DB.lookup receiptSlot before ≡ just (Ledger.recordAt {id = id} owner (R.active input names progress)))
        (foundHere : Ledger.find id before ≡ just (Ledger.found receiptSlot owner (R.active input names progress))) where

        module Copy = Prepare.Current before valid viewsValid pointer source selected nodes edges payload sourceFound published registered live
        fresh = Copy.slot
        inserted = Copy.after
        copied = Copy.copied
        module Switch = Replace.Selector pointer source fresh selected

        ready : Switch.Ready inserted
        ready =
          (Switch.oldRecord , Copy.oldLookup pointer _ published , refl , refl) ,
          (copied , Copy.copiedVisible , Copy.copiedOwner , Store.projectCheckout selection before Copy.original)

        module Changed = Switch.Current inserted Copy.afterValid Copy.viewsAfter ready
        changed = Changed.after
        work = effect guidance

        prepared : DB.evaluate transaction before ≡ DB.committed result changed
        prepared = trans (Copy.preparesCopy next (λ world → DB.abort continuation))
          (Switch.performs inserted result continuation ready)

        oldReceipt = Ledger.recordAt {id = id} owner (R.active input names progress)
        nextProgress = R.nextWork progress (R.versions progress) result
        newReceipt = Ledger.recordAt {id = id} owner (R.active input names nextProgress)
        after = DB.write receiptSlot newReceipt changed
        change = Ledger.checkpoint (R.versions progress)
        request = Ledger.update id input (R.generation progress) change work

        commits : DB.execute request before ≡ (Ledger.resume receiptSlot nextProgress , after)
        commits = Ledger.committedUpdate id input names change work receiptSlot owner progress before result changed foundHere prepared

        receiptLocated : DB.lookup receiptSlot changed ≡ just oldReceipt
        receiptLocated = proj₁ (isolates before result changed prepared receiptSlot owner (R.entry id (R.active input names progress))) located

        afterValid : O.Admissible after
        afterValid = Storage.writeAdmissible changed receiptSlot oldReceipt newReceipt Changed.afterValid
          receiptLocated refl refl tt (λ ref included → included)

        module SelectorVisibility = Visibility.Model.Write selection inserted pointer Switch.oldRecord Switch.newRecord
          (O.Admissible.unique Copy.afterValid) (Switch.pointerFound inserted (proj₁ ready))
          (Visibility.selector owner selected source) (Visibility.selector owner selected fresh)

        module ReceiptVisibility = Visibility.Model.Write selection changed receiptSlot oldReceipt newReceipt
          (O.Admissible.unique Changed.afterValid) receiptLocated
          (Visibility.receipt owner (R.entry id (R.active input names progress)))
          (Visibility.receipt owner (R.entry id (R.active input names nextProgress)))

        canonical : M.project selection after copied ≡ copied
        canonical = ReceiptVisibility.canonicalPersists copied
          (SelectorVisibility.canonicalPersists copied Copy.copiedCanonical)

        afterReceiptOther : ∀ key value → DB.lookup key changed ≡ just value →
          O.kind (O.body value) ≢ O.receiptK → DB.lookup key after ≡ just value
        afterReceiptOther key value found different = trans
          (DB.writePreservesOther receiptSlot key newReceipt changed
            (lookupDistinct changed receiptSlot oldReceipt key value receiptLocated found (λ same → different (sym same)))) found

        currentVisible : DB.lookup pointer after ≡ just Switch.newRecord
        currentVisible = afterReceiptOther pointer _ Changed.currentVisible (λ ())

        copiedVisible : DB.lookup fresh after ≡ just copied
        copiedVisible = afterReceiptOther fresh copied
          (Changed.oldLookup fresh copied
            (λ same → lookupDistinct inserted pointer Switch.oldRecord fresh copied
              (Switch.pointerFound inserted (proj₁ ready)) Copy.copiedVisible
              (λ kinds → impossibleSelector (trans kinds Copy.copiedKind)) (sym same)) Copy.copiedVisible)
          (λ kinds → impossible (trans (sym Copy.copiedKind) kinds))
          where
          impossible : O.structuralSnapshotK ≢ O.receiptK
          impossible ()
          impossibleSelector : O.publishedViewK ≢ O.structuralSnapshotK
          impossibleSelector ()

        beforeReceiptOther : ∀ key value → DB.lookup key after ≡ just value →
          O.kind (O.body value) ≢ O.receiptK → DB.lookup key changed ≡ just value
        beforeReceiptOther key value found different with receiptSlot ≟ key
        ... | yes refl = ⊥-elim (different (sym (cong (λ row → O.kind (O.body row))
          (just-injective (trans (sym (DB.writeVisible receiptSlot newReceipt changed)) found)))))
        ... | no distinct = trans (sym (DB.writePreservesOther receiptSlot key newReceipt changed distinct)) found

        otherRecord : ∀ key value → DB.lookup key before ≡ just value →
          O.kind (O.body value) ≢ O.publishedViewK → O.kind (O.body value) ≢ O.receiptK →
          DB.lookup key after ≡ just value
        otherRecord key value found nonSelector nonReceipt = afterReceiptOther key value
          (Changed.oldLookup key value
            (λ same → lookupDistinct before pointer Switch.oldRecord key value published found
              (λ kinds → nonSelector (sym kinds)) (sym same))
            (Copy.oldLookup key value found)) nonReceipt

        snapshotPreserved : ∀ key snapshotOwner checkout ns es text →
          DB.lookup key before ≡ just (O.recordOf snapshotOwner (O.structuralSnapshot checkout ns es text)) →
          DB.lookup key after ≡ just (O.recordOf snapshotOwner (O.structuralSnapshot checkout ns es text))
        snapshotPreserved key snapshotOwner checkout ns es text found = otherRecord key _ found (λ ()) (λ ())

        readerPreserved : ∀ key readerOwner refs text →
          DB.lookup key before ≡ just (O.recordOf readerOwner (O.activeReader refs text)) →
          DB.lookup key after ≡ just (O.recordOf readerOwner (O.activeReader refs text))
        readerPreserved key readerOwner refs text found = otherRecord key _ found (λ ()) (λ ())

        capturedWorkPreserved : ∀ key taskOwner taskId ids text →
          DB.lookup key before ≡ just (O.recordOf taskOwner (O.cleanupWork taskId ids text)) →
          DB.lookup key after ≡ just (O.recordOf taskOwner (O.cleanupWork taskId ids text))
        capturedWorkPreserved key taskOwner taskId ids text found = otherRecord key _ found (λ ()) (λ ())

        viewsAfter : Views.Valid after
        viewsAfter = record
          { onePerCheckout = λ first second currentOwner checkout firstRoot secondRoot firstFound secondFound →
              Views.Valid.onePerCheckout Changed.viewsAfter first second currentOwner checkout firstRoot secondRoot
                (beforeReceiptOther first _ firstFound (λ ())) (beforeReceiptOther second _ secondFound (λ ()))
          ; sameCheckout = keepsCheckout }
          where
          keepsCheckout : ∀ currentPointer currentOwner checkout root →
            DB.lookup currentPointer after ≡ just (O.recordOf currentOwner (O.publishedView checkout root)) →
            Views.SnapshotAt after currentOwner checkout root
          keepsCheckout currentPointer currentOwner checkout root found
            with Views.Valid.sameCheckout Changed.viewsAfter currentPointer currentOwner checkout root
              (beforeReceiptOther currentPointer _ found (λ ()))
          ... | ns , es , text , snapshotFound = ns , es , text , afterReceiptOther root _ snapshotFound (λ ())

        receiptWritten : Ledger.find id after ≡ just (Ledger.found receiptSlot owner (R.active input names nextProgress))
        receiptWritten = Ledger.writtenReceiptVisible id receiptSlot owner (R.active input names nextProgress) changed

        retryObserved : ∀ observed → Ledger.find id observed ≡ just (Ledger.found receiptSlot owner (R.active input names nextProgress)) →
          DB.execute request observed ≡ (Ledger.resume receiptSlot nextProgress , observed)
        retryObserved observed found = Ledger.staleStepSkipsEffect id input names (R.generation progress) change work receiptSlot owner nextProgress observed found
          (Ledger.nextGenerationDifferent (R.generation progress))

        retry : DB.execute request after ≡ (Ledger.resume receiptSlot nextProgress , after)
        retry = retryObserved after receiptWritten

        terminates : ∀ world → Σ Ledger.Reply (λ reply → Σ O.World (λ final →
          Exec.Completed (Exec.atomic request Exec.done) world reply final))
        terminates world = proj₁ (DB.execute request world) , proj₂ (DB.execute request world) , Exec.committed Exec.stop

        atomicPublication : ∀ observed → Exec.Interrupted (Exec.atomic request Exec.done) before observed →
          (observed ≡ before) ⊎ (observed ≡ after)
        atomicPublication observed interrupted with Ledger.atomicBoundary request before observed interrupted
        ... | inj₁ same = inj₁ same
        ... | inj₂ same = inj₂ (trans same (cong proj₂ commits))

        completedAtomic : ∀ observed reply final → Exec.Completed (Exec.atomic request Exec.done) observed reply final →
          DB.execute request observed ≡ (reply , final)
        completedAtomic observed reply final (Exec.committed Exec.stop) = refl

        converges : ∀ observed final reply → Exec.Interrupted (Exec.atomic request Exec.done) before observed →
          Exec.Completed (Exec.atomic request Exec.done) observed reply final → final ≡ after
        converges observed final reply interrupted completed with atomicPublication observed interrupted
        ... | inj₁ same = trans (sym (cong proj₂ (completedAtomic observed reply final completed)))
          (trans (cong (λ world → proj₂ (DB.execute request world)) same) (cong proj₂ commits))
        ... | inj₂ same = trans (sym (cong proj₂ (completedAtomic observed reply final completed)))
          (trans (cong (λ world → proj₂ (DB.execute request world)) same) (cong proj₂ retry))
