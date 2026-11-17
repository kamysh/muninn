{-# OPTIONS --safe #-}
-- Automatic follow-up creation retains both worker contexts and the request.
module Muninn.PolicyCleanupScheduledContext where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.PolicyRuleAdmission as Admission
import Muninn.PolicyCleanupBatch as Batch
import Muninn.CleanupFinalization as Finalization
import Muninn.CleanupLoop as Loop
import Muninn.PolicyCleanupWorker as Worker
import Muninn.PolicyCleanupWorkerFollowup as Followup
import Muninn.CleanupDecision as Decision
import Muninn.PolicyCleanupWorkerContinue as Continue
import Muninn.RecordAllocation as Allocation
import Muninn.CleanupScheduling as Scheduling
import Muninn.CleanupAdmissionStorage as Insert
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
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
module DB = O.DB

module Model where
  module Outcome = E.Model
  module Family (family pointer : ℕ) (accepted : O.World) (rules : List String)
    (validRules : Admission.Entries (Data.List.map Data.String.toList rules))
    (intent : Outcome.Intent (E.rule family rules validRules) accepted)
    (request : Input.Mutation (Input.PolicyTarget × Input.PolicyDraft)) (taskSlot receiptSlot : ℕ)
    (names : Receipt.Names (Input.Mutation.operationId request) (Identity.mutation Identity.kApplyPolicy request))
    (progress : Receipt.Work) (guidance : String → Dialogue.Prompt) where
    module Policy = Stored.Family family pointer
    open Worker.Model.Family family pointer accepted rules validRules intent request taskSlot using (id; meaning; owner)
    open Continue.Model.Family family pointer accepted rules validRules intent request taskSlot receiptSlot names progress guidance using (Context)
    open Context using (current; seen; valid; task; located; receipt)
    module At (world : O.World) (ctx : Context world) where
      module Step = Batch.Model.Family.Selected family pointer accepted rules validRules intent id taskSlot (current ctx)
      module Alloc = Allocation.Model.Family.Current Step.selection world (valid ctx)
        "Follow-up cleanup" "Cleanup is progressing." guidance id meaning names receiptSlot progress (located ctx) (receipt ctx)
      module Durable = Alloc.Durable
      open Alloc public using (after; next; afterValid; ownedCapture; savedOriginalWorkset)
      childIntent = Alloc.intent
      slot = Allocation.freshId world
      childRules = E.exclusions Step.selection
      oldReceipt = Ledger.recordAt {id = id} owner (Receipt.active meaning names progress)
      newReceipt = Ledger.recordAt {id = id} owner (Receipt.active meaning names next)
      module Tasks = Scheduling.Model.Family Step.selection
      added = Tasks.task id slot "Follow-up cleanup" world
      inserted = Tasks.created id slot "Follow-up cleanup" world
      keep : ∀ key value → DB.lookup key world ≡ just value → O.kind (O.body value) ≢ O.receiptK → DB.lookup key after ≡ just value
      keep key value found notReceipt = trans
        (DB.writePreservesOther receiptSlot key newReceipt inserted (λ same → notReceipt (cong (λ row → O.kind (O.body row))
          (just-injective (trans (sym found) (trans (cong (λ k → DB.lookup k world) (sym same)) (located ctx)))))))
        (Insert.oldLookup world slot added (Allocation.fresh world) key value found)

      selected = Policy.selectsKnown after (Policy.Saved.version (current ctx)) (Policy.Saved.defaultsSlot (current ctx))
        (Policy.Saved.info (current ctx)) (Policy.Saved.frozen (current ctx))
        (keep pointer _ (Policy.Saved.pointerAt (current ctx)) (λ ()))
        (keep (Policy.Saved.version (current ctx)) _ (Policy.Saved.versionAt (current ctx)) (λ ()))
        (keep (Policy.Saved.defaultsSlot (current ctx)) _ (Policy.Saved.defaultsAt (current ctx)) (λ ()))

      contexts : (Σ (Policy.Saved after) (λ policy → Policy.observe after ≡ just policy))
      contexts with Policy.observe after in observed
      ... | just policy = policy , refl
      ... | nothing = ⊥-elim (impossible selected)
        where
        impossible : Policy.selectedPolicy after ≡ just (Policy.policy (current ctx)) → ⊥
        impossible proof rewrite observed with proof
        ... | ()

      policy = proj₁ contexts
      observed = proj₂ contexts
      nextReceipt = proj₂ ownedCapture
      nextLocated : DB.lookup receiptSlot after ≡ just newReceipt
      nextLocated = DB.writeVisible receiptSlot newReceipt inserted
      module Parent = Finalization.Model.Task (E.rule family rules validRules) accepted intent id taskSlot
      parentTask : Parent.TaskAt after
      parentTask with Parent.savedRecord world (task ctx)
      ... | payload , found = O.recordOf owner (O.cleanupWork id (Outcome.Intent.keys intent) payload) ,
        savedOriginalWorkset taskSlot id (Outcome.Intent.keys intent) payload found , refl , refl

      parentContext : Continue.Model.Family.Context family pointer accepted rules validRules intent request taskSlot receiptSlot names next guidance after
      parentContext = Continue.Model.Family.context policy observed afterValid parentTask nextLocated nextReceipt

      childContext : Continue.Model.Family.Context family pointer after childRules (E.admitted Step.selection) Alloc.intent request slot receiptSlot names next guidance after
      childContext = Continue.Model.Family.context policy observed afterValid
        (O.recordOf owner (O.cleanupWork id (Outcome.Intent.keys Alloc.intent) "Follow-up cleanup") , proj₁ ownedCapture , refl , refl)
        nextLocated nextReceipt

      differentTasks : taskSlot ≢ slot
      differentTasks same with Parent.savedRecord world (task ctx)
      ... | payload , found = Allocation.fresh world (substReserved same found)
        where
        substReserved : taskSlot ≡ slot → DB.lookup taskSlot world ≡ just (O.recordOf owner (O.cleanupWork id (Outcome.Intent.keys intent) payload)) →
          slot ∈ Insert.reserved world
        substReserved refl present = Insert.storedReserved world slot _ present

      module ChildRun = Loop.Model.Run Step.selection after Alloc.intent
      capturedCoverage : ChildRun.Covered after
      capturedCoverage = Durable.covered

      module Decisions = Decision.Model.Family.Current family pointer accepted rules validRules intent id taskSlot (current ctx)
      module ParentAtSelection = Finalization.Model.Task Step.selection accepted Step.intent id taskSlot
      module Blocked (quiet : Step.Pass.NoEdit world)
        (pending : Σ ℕ (λ key → ParentAtSelection.Final.Pending key world))
        (blocker : Σ (ℕ × O.Record) (λ row → row ∈ world × Decisions.Followup.Unscheduled row)) where
        open Followup.Model.Family.At.Blocked family pointer accepted rules validRules intent request taskSlot
          world (current ctx) (seen ctx) (valid ctx) receiptSlot names progress guidance (located ctx) (receipt ctx) (task ctx) quiet pending blocker
          public using (tickSchedules; originalRequestStillActive)
