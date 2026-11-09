{-# OPTIONS --safe #-}
-- A shared receipt seal for the concrete identity transitions. The caller
-- supplies the actual DB effect and its computed committed world.
module Muninn.IdentityCheckpoint where

import Muninn.OwnedState as O
import Muninn.ReceiptLedger as Ledger
import Muninn.ReceiptTypes as R
import Muninn.RequestIdentity as Identity
import Muninn.CatalogInputs as I
import Muninn.CleanupStorage as Storage
import Muninn.ViewPublication as Frames
open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Data.List using ([])
open import Data.Maybe using (just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
module DB = O.DB
module Exec = O.Execution

ownerDistinct : ∀ world slot old key value → DB.lookup slot world ≡ just old → DB.lookup key world ≡ just value →
  O.owner old ≢ O.owner value → slot ≢ key
ownerDistinct world slot old .slot value first second different refl =
  different (cong O.owner (just-injective (trans (sym first) second)))

module Run (id : I.OperationId) (input : Identity.Meaning) (names : R.Names id input)
  (owner : O.Owner) (slot : ℕ) (progress : R.Work) (checkpoint : String)
  (effect : Ledger.Effect) (before changed : O.World)
  (valid : O.Admissible changed)
  (found : Ledger.find id before ≡ just (Ledger.found slot owner (R.active input names progress)))
  (located : DB.lookup slot before ≡ just (Ledger.recordAt owner (R.active input names progress)))
  (performs : DB.evaluate (Ledger.Effect.transaction effect) before ≡ DB.committed checkpoint changed) where
  change = Ledger.checkpoint []
  next = R.nextWork progress [] checkpoint
  oldReceipt = Ledger.recordAt {id = id} owner (R.active input names progress)
  newReceipt = Ledger.recordAt {id = id} owner (R.active input names next)
  after = DB.write slot newReceipt changed
  request = Ledger.update id input (R.generation progress) change effect

  commits : DB.execute request before ≡ (Ledger.resume slot next , after)
  commits = Ledger.committedUpdate id input names change effect slot owner progress before checkpoint changed found performs

  receiptInChanged : DB.lookup slot changed ≡ just oldReceipt
  receiptInChanged = proj₁ (Ledger.Effect.isolates effect before checkpoint changed performs slot owner (R.entry id (R.active input names progress))) located

  afterValid : O.Admissible after
  afterValid = Storage.writeAdmissible changed slot oldReceipt newReceipt valid receiptInChanged refl refl tt (λ ref ())

  preserves : ∀ key value → DB.lookup key changed ≡ just value → key ≢ slot → DB.lookup key after ≡ just value
  preserves key value present distinct = trans (DB.writePreservesOther slot key newReceipt changed (λ same → distinct (sym same))) present

  preservesData : ∀ key value → DB.lookup key changed ≡ just value → O.kind (O.body value) ≢ O.receiptK → DB.lookup key after ≡ just value
  preservesData key value present nonReceipt = trans
    (DB.writePreservesOther slot key newReceipt changed
      (Frames.lookupDistinct changed slot oldReceipt key value receiptInChanged present (λ same → nonReceipt (sym same)))) present

  written : Ledger.find id after ≡ just (Ledger.found slot owner (R.active input names next))
  written = Ledger.writtenReceiptVisible id slot owner (R.active input names next) changed

  retry : DB.execute request after ≡ (Ledger.resume slot next , after)
  retry = Ledger.staleStepSkipsEffect id input names (R.generation progress) change effect slot owner next after written (Ledger.nextGenerationDifferent (R.generation progress))

  boundary : ∀ observed → Exec.Interrupted (Exec.atomic request Exec.done) before observed → (observed ≡ before) ⊎ (observed ≡ after)
  boundary observed interrupted with Ledger.atomicBoundary request before observed interrupted
  ... | inj₁ same = inj₁ same
  ... | inj₂ same = inj₂ (trans same (cong proj₂ commits))

  completedAtomic : ∀ observed reply final → Exec.Completed (Exec.atomic request Exec.done) observed reply final → DB.execute request observed ≡ (reply , final)
  completedAtomic observed reply final (Exec.committed Exec.stop) = refl

  converges : ∀ observed reply final → Exec.Interrupted (Exec.atomic request Exec.done) before observed →
    Exec.Completed (Exec.atomic request Exec.done) observed reply final → final ≡ after
  converges observed reply final interrupted completed with boundary observed interrupted
  ... | inj₁ same = trans (sym (cong proj₂ (completedAtomic observed reply final completed)))
    (trans (cong (λ world → proj₂ (DB.execute request world)) same) (cong proj₂ commits))
  ... | inj₂ same = trans (sym (cong proj₂ (completedAtomic observed reply final completed)))
    (trans (cong (λ world → proj₂ (DB.execute request world)) same) (cong proj₂ retry))

  completes : ∀ world → Σ Ledger.Reply (λ reply → Σ O.World (λ final → Exec.Completed (Exec.atomic request Exec.done) world reply final))
  completes world = proj₁ (DB.execute request world) , proj₂ (DB.execute request world) , Exec.committed Exec.stop
