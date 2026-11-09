{-# OPTIONS --safe #-}
-- Construct a fresh incarnation from the complete stored and weak reservation set.
module Muninn.RecordAllocation where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.CleanupAdmissionStorage as Insert
import Muninn.CleanupAdmission as Admission
import Muninn.CleanupScheduling as Scheduling
import Muninn.ReceiptLedger as Ledger
import Muninn.ReceiptTypes as R
import Muninn.CatalogInputs as I
import Muninn.RequestIdentity as Identity
import Muninn.Dialogue as D
open import Data.Nat using (ℕ; zero; suc; _⊔_; _≤_; _<_ ; s≤s)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; ≤-trans; <-irrefl)
open import Data.Bool using (Bool)
open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
module DB = O.DB
module Exec = O.Execution

largest : List ℕ → ℕ
largest [] = zero
largest (key ∷ keys) = key ⊔ largest keys

memberBound : ∀ keys key → key ∈ keys → key ≤ largest keys
memberBound (key ∷ keys) .key (here refl) = m≤m⊔n key (largest keys)
memberBound (first ∷ keys) key (there present) = ≤-trans (memberBound keys key present) (m≤n⊔m first (largest keys))

freshId : O.World → ℕ
freshId world = suc (largest (Insert.reserved world))

fresh : ∀ world → Insert.Fresh world (freshId world)
fresh world present = <-irrefl refl (memberBound (Insert.reserved world) (freshId world) present)

reservedSmaller : ∀ world key → key ∈ Insert.reserved world → key < freshId world
reservedSmaller world key present = s≤s (memberBound (Insert.reserved world) key present)

allocate : (world : O.World) → Σ ℕ (Insert.Fresh world)
allocate world = freshId world , fresh world

module Model where
  module Family (selection : E.Rule) where
    module Gate = Admission.Model.Family selection
    module Tasks = Scheduling.Model.Family selection

    admit : ∀ {A : Set} → List O.Reference → String → (ℕ → A) → (O.World → A) → DB.Transaction A
    admit refs payload ready replan = DB.scan (λ world → Gate.admit (freshId world) refs payload ready replan)

    admits : ∀ {A : Set} refs payload (ready : ℕ → A) replan world → Gate.Resolved world refs →
      Gate.Clean (Gate.proposed world (freshId world) refs payload) refs → Gate.Allowed world (freshId world) refs payload →
      DB.execute (admit refs payload ready replan) world ≡ (ready (freshId world) , Gate.proposed world (freshId world) refs payload)
    admits refs payload ready replan world resolved clean allowed = Gate.accepts (freshId world) refs payload ready replan world (fresh world) resolved clean allowed

    admissionAdmissible : ∀ {A : Set} refs payload (ready : ℕ → A) replan world → O.Admissible world →
      O.Admissible (proj₂ (DB.execute (admit refs payload ready replan) world))
    admissionAdmissible refs payload ready replan world = Gate.admissionAdmissible (freshId world) refs payload ready replan world

    admissionReceipts : ∀ {A : Set} refs payload (ready : ℕ → A) replan world →
      Ledger.ReceiptFrame world (proj₂ (DB.execute (admit refs payload ready replan) world))
    admissionReceipts refs payload ready replan world = Gate.receiptFrame (freshId world) refs payload ready replan world

    create : I.OperationId → String → String → DB.Transaction String
    create id payload checkpoint = DB.scan (λ world → Tasks.create id (freshId world) payload checkpoint)

    creates : ∀ id payload checkpoint world →
      DB.evaluate (create id payload checkpoint) world ≡ DB.committed checkpoint (Tasks.created id (freshId world) payload world)
    creates id payload checkpoint world = Tasks.creates id (freshId world) payload checkpoint world (fresh world)

    effect : I.OperationId → String → String → (String → D.Prompt) → Ledger.Effect
    effect id payload checkpoint guidance = record
      { transaction = create id payload checkpoint; guidance = guidance
      ; isolates = λ before result after committed → Tasks.isolates id (freshId before) payload checkpoint before result after committed }

    module Current (before : O.World) (valid : O.Admissible before)
      (payload checkpoint : String) (guidance : String → D.Prompt)
      (id : I.OperationId) (input : Identity.Meaning) (names : R.Names id input)
      (receiptSlot : ℕ) (progress : R.Work)
      (located : DB.lookup receiptSlot before ≡ just (Ledger.recordAt {id = id} (E.targetOwner selection) (R.active input names progress)))
      (foundHere : Ledger.find id before ≡ just (Ledger.found receiptSlot (E.targetOwner selection) (R.active input names progress))) where
      module Durable = Tasks.Current before valid (freshId before) payload checkpoint guidance (fresh before) id input names receiptSlot progress located foundHere
      open Durable public using (intent; captured; after; afterValid; next; savedCapture; ownedCapture; savedOriginalWorkset; cleanupComplete; persistsThroughCleanup)
      module Worker = Durable.Worker
      work = effect id payload checkpoint guidance
      transaction = Ledger.update id input (R.generation progress) Durable.change work

      commits : DB.execute transaction before ≡ (Ledger.resume receiptSlot next , after)
      commits = Ledger.committedUpdate id input names Durable.change work receiptSlot (E.targetOwner selection)
        progress before checkpoint Durable.inserted foundHere (creates id payload checkpoint before)

      retryObserved : ∀ observed → Ledger.find id observed ≡ just (Ledger.found receiptSlot (E.targetOwner selection) (R.active input names next)) →
        DB.execute transaction observed ≡ (Ledger.resume receiptSlot next , observed)
      retryObserved observed found = Ledger.staleStepSkipsEffect id input names (R.generation progress) Durable.change work receiptSlot
        (E.targetOwner selection) next observed found (Ledger.nextGenerationDifferent (R.generation progress))

      retry : DB.execute transaction after ≡ (Ledger.resume receiptSlot next , after)
      retry = retryObserved after (Ledger.writtenReceiptVisible id receiptSlot (E.targetOwner selection) (R.active input names next) Durable.inserted)

      atomicCapture : ∀ observed → Exec.Interrupted (Exec.atomic transaction Exec.done) before observed → (observed ≡ before) ⊎ (observed ≡ after)
      atomicCapture observed interrupted with Ledger.atomicBoundary transaction before observed interrupted
      ... | inj₁ same = inj₁ same
      ... | inj₂ same = inj₂ (trans same (cong proj₂ commits))

      completedAtomic : ∀ observed reply final → Exec.Completed (Exec.atomic transaction Exec.done) observed reply final → DB.execute transaction observed ≡ (reply , final)
      completedAtomic observed reply final (Exec.committed Exec.stop) = refl

      converges : ∀ observed final reply → Exec.Interrupted (Exec.atomic transaction Exec.done) before observed →
        Exec.Completed (Exec.atomic transaction Exec.done) observed reply final → final ≡ after
      converges observed final reply interrupted completed with atomicCapture observed interrupted
      ... | inj₁ same = trans (sym (cong proj₂ (completedAtomic observed reply final completed)))
        (trans (cong (λ world → proj₂ (DB.execute transaction world)) same) (cong proj₂ commits))
      ... | inj₂ same = trans (sym (cong proj₂ (completedAtomic observed reply final completed)))
        (trans (cong (λ world → proj₂ (DB.execute transaction world)) same) (cong proj₂ retry))
