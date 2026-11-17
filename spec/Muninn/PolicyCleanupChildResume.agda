{-# OPTIONS --safe #-}
-- Resume a covering follow-up after the original task finishes.
module Muninn.PolicyCleanupChildResume where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.PolicyRuleAdmission as Admission
import Muninn.CleanupLoop as Loop
import Muninn.CleanupFinalization as Finalization
import Muninn.PolicyCleanupBatch as Batch
import Muninn.PolicyCleanupWorker as Worker
import Muninn.PolicyCleanupWorkerContinue as Continue
import Muninn.PolicyCleanupAfterFollowup as Handoff
import Muninn.ReceiptTypes as Receipt
import Muninn.CatalogInputs as Input
import Muninn.RequestIdentity as Identity
import Muninn.Dialogue as Dialogue
open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (Bool)
open import Data.String using (String)
open import Data.List using (List)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans)
module DB = O.DB

module Model where
  module Outcome = E.Model
  module Family (family pointer : ℕ) (accepted : O.World) (rules : List String)
    (validRules : Admission.Entries (Data.List.map Data.String.toList rules))
    (intent : Outcome.Intent (E.rule family rules validRules) accepted)
    (childAccepted : O.World) (childRules : List String)
    (childValidRules : Admission.Entries (Data.List.map Data.String.toList childRules))
    (childIntent : Outcome.Intent (E.rule family childRules childValidRules) childAccepted)
    (request : Input.Mutation (Input.PolicyTarget × Input.PolicyDraft))
    (taskSlot childSlot receiptSlot : ℕ)
    (names : Receipt.Names (Input.Mutation.operationId request) (Identity.mutation Identity.kApplyPolicy request))
    (progress : Receipt.Work) (guidance : String → Dialogue.Prompt) where
    open Worker.Model.Family family pointer accepted rules validRules intent request taskSlot using (id)
    open Continue.Model.Family family pointer accepted rules validRules intent request taskSlot receiptSlot names progress guidance using (Context)
    open Context using (current; seen; valid; task; located; receipt)
    module At (world : O.World) (ctx : Context world) (distinct : taskSlot ≢ childSlot) where
      module ChildStep = Batch.Model.Family.Selected family pointer childAccepted childRules childValidRules childIntent id childSlot (current ctx)
      module Child = Finalization.Model.Task ChildStep.selection childAccepted ChildStep.intent id childSlot
      module ChildLoop = Loop.Model.Run ChildStep.selection childAccepted ChildStep.intent
      module Completed (ready : Child.Ready world) (quiet : ChildStep.Pass.NoEdit world) (covered : ChildLoop.Covered world) where
        open Handoff.Model.Family.At.Completed.ParentCanFinish family pointer accepted rules validRules intent childAccepted childRules childValidRules childIntent
          request taskSlot childSlot receiptSlot names progress guidance world ctx distinct ready quiet covered
          using (parentReady; parentQuiet)
        open Continue.Model.Family family pointer childAccepted childRules childValidRules childIntent request childSlot receiptSlot names progress guidance
          using () renaming (context to childContextOf)
        childContext = childContextOf (current ctx) (seen ctx) (valid ctx) (proj₁ ready) (located ctx) (receipt ctx)
        open Handoff.Model.Family.At.Completed family pointer childAccepted childRules childValidRules childIntent accepted rules validRules intent
          request childSlot taskSlot receiptSlot names progress guidance world childContext (λ same → distinct (sym same)) parentReady parentQuiet
          public using (after; nextContext; nextProgress; oldReceipt; newReceipt; cleaned; taskRemoved)

        capturedAfter : ChildLoop.Covered after
        capturedAfter key value found owned with receiptSlot ≟ key
        ... | yes refl = covered receiptSlot oldReceipt (located ctx) refl
        ... | no notReceipt with taskSlot ≟ key
        ...   | yes refl = ⊥-elim (nothingIsJust (trans (sym taskRemoved) found))
          where
          nothingIsJust : nothing ≡ just value → ⊥
          nothingIsJust ()
        ...   | no notTask = covered key value oldLookup owned
          where
          oldLookup : DB.lookup key world ≡ just value
          oldLookup = trans (sym (DB.deletePreservesOther taskSlot key world notTask))
            (trans (sym (DB.writePreservesOther receiptSlot key newReceipt cleaned notReceipt)) found)
