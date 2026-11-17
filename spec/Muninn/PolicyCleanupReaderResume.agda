{-# OPTIONS --safe #-}
-- A finished reader releases its hold and the original worker resumes.
module Muninn.PolicyCleanupReaderResume where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.PolicyRuleAdmission as Admission
import Muninn.ReaderRelease as Release
import Muninn.CleanupReceiptPreservation as Receipts
import Muninn.PolicyCleanupWorker as Worker
import Muninn.PolicyCleanupWorkerContinue as Continue
import Muninn.PolicyCleanupWorkerDrain as Drain
import Muninn.CleanupFinalization as Finalization
import Muninn.StoredPolicy as Stored
import Muninn.ReceiptLedger as Ledger
import Muninn.ReceiptTypes as Receipt
import Muninn.CatalogInputs as Input
import Muninn.RequestIdentity as Identity
import Muninn.Dialogue as Dialogue
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool)
open import Data.String using (String)
open import Data.List using (List)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
module DB = O.DB

readerDoesNotMatch : ∀ id key value → O.kind (O.body value) ≡ O.activeReaderK →
  Ledger.inRecord id key value ≡ nothing
readerDoesNotMatch id key (O.recordOf owner body) same with Release.readerBody body same
... | refs , payload , refl = refl

module Model where
  module Outcome = E.Model
  module Family (family pointer : ℕ) (accepted : O.World) (rules : List String)
    (validRules : Admission.Entries (Data.List.map Data.String.toList rules))
    (intent : Outcome.Intent (E.rule family rules validRules) accepted)
    (request : Input.Mutation (Input.PolicyTarget × Input.PolicyDraft)) (taskSlot receiptSlot : ℕ)
    (names : Receipt.Names (Input.Mutation.operationId request) (Identity.mutation Identity.kApplyPolicy request))
    (progress : Receipt.Work) (guidance : String → Dialogue.Prompt) where
    module Policy = Stored.Family family pointer
    module Task = Finalization.Model.Task (E.rule family rules validRules) accepted intent (Input.Mutation.operationId request) taskSlot
    open Worker.Model.Family family pointer accepted rules validRules intent request taskSlot using (id; meaning; owner)
    open Continue.Model.Family family pointer accepted rules validRules intent request taskSlot receiptSlot names progress guidance using (Context; context)
    open Context using (current; seen; valid; task; located; receipt)
    open Drain.Model.Family family pointer accepted rules validRules intent request taskSlot receiptSlot names progress guidance using (drain; Result)

    module At (world : O.World) (ctx : Context world) (readerOwner : O.Owner) (reader : ℕ)
      (actual : Release.ReaderAt readerOwner reader world) where
      replan : O.World → ⊤
      replan _ = tt
      finish = Release.finish readerOwner reader tt replan
      after = proj₂ (DB.execute finish world)
      currentPolicy = current ctx
      info = Policy.Saved.info currentPolicy
      frozen = Policy.Saved.frozen currentPolicy
      version = Policy.Saved.version currentPolicy
      defaultsSlot = Policy.Saved.defaultsSlot currentPolicy

      selected : Policy.selectedPolicy after ≡ just (Policy.policy currentPolicy)
      selected = Policy.selectsKnown after version defaultsSlot info frozen
        (Release.nonReaderRow readerOwner reader tt replan world pointer _ (Policy.Saved.pointerAt currentPolicy) (λ ()))
        (Release.nonReaderRow readerOwner reader tt replan world version _ (Policy.Saved.versionAt currentPolicy) (λ ()))
        (Release.nonReaderRow readerOwner reader tt replan world defaultsSlot _ (Policy.Saved.defaultsAt currentPolicy) (λ ()))

      findAfter : (readerAt : Release.ReaderAt readerOwner reader world) →
        Ledger.find id after ≡ just (Ledger.found receiptSlot owner (Receipt.active meaning names progress))
      findAfter readerAt@(readerValue , readerFound , readerOwned , readerKind) = trans
        (cong (Ledger.find id) (cong proj₂ (Release.executes readerOwner reader tt replan world readerAt)))
        (trans (Receipts.findDeleteNonReceipt id reader world readerValue (O.Admissible.unique (valid ctx)) readerFound
          (readerDoesNotMatch id reader readerValue readerKind)) (receipt ctx))

      nextContext : Context after
      nextContext with Task.savedRecord world (task ctx)
      ... | payload , saved with Policy.observe after in observed
      ...   | nothing = ⊥-elim (impossible selected)
        where
        impossible : Policy.selectedPolicy after ≡ just (Policy.policy currentPolicy) → ⊥
        impossible proof rewrite observed = contradiction proof
          where
          contradiction : nothing ≡ just (Policy.policy currentPolicy) → ⊥
          contradiction ()
      ...   | just new = context new observed nextValid nextTask nextLocated nextReceipt
        where
        nextValid = Release.admissible readerOwner reader tt replan world (valid ctx)
        nextTask : Task.TaskAt after
        nextTask = O.recordOf owner (O.cleanupWork id (Outcome.Intent.keys intent) payload) ,
          Release.nonReaderRow readerOwner reader tt replan world taskSlot _ saved (λ ()) , refl , refl
        nextLocated = Release.nonReaderRow readerOwner reader tt replan world receiptSlot _ (located ctx) (λ ())
        nextReceipt : Ledger.find id after ≡ just (Ledger.found receiptSlot owner (Receipt.active meaning names progress))
        nextReceipt = findAfter actual

      resumed : Result after
      resumed = drain after nextContext
