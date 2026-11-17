{-# OPTIONS --safe #-}
-- Child cleanup advances without losing the original task or request.
module Muninn.PolicyCleanupParentContinue where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.PolicyRuleAdmission as Admission
import Muninn.PolicyCleanupWorker as Worker
import Muninn.PolicyCleanupWorkerContinue as Continue
import Muninn.PolicyCleanupRetry as Retry
import Muninn.PolicyCleanupRetryHistory as History
import Muninn.CleanupFinalization as Finalization
import Muninn.CleanupProgress as Progress
import Muninn.StoredPolicy as Stored
import Muninn.ReceiptTypes as Receipt
import Muninn.CatalogInputs as Input
import Muninn.RequestIdentity as Identity
import Muninn.Dialogue as Dialogue
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool)
open import Data.String using (String)
open import Data.List using (List)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
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
    open Worker.Model.Family family pointer accepted rules validRules intent request taskSlot using (id; owner)
    open Continue.Model.Family family pointer accepted rules validRules intent request taskSlot receiptSlot names progress guidance using (Context)
    open Context using (task)
    module Parent = Finalization.Model.Task (E.rule family rules validRules) accepted intent id taskSlot
    module Policy = Stored.Family family pointer
    open Continue.Model.Family family pointer childAccepted childRules childValidRules childIntent request childSlot receiptSlot names progress guidance
      using () renaming (Context to ChildContext; context to mkParentChild)
    open ChildContext using () renaming (current to childCurrent; seen to childSeen; valid to childValid; located to childLocated; receipt to childReceipt)
    open Retry.Model.Family family pointer childAccepted childRules childValidRules childIntent request childSlot receiptSlot names progress guidance using (Path)
    open History.Model.Family family pointer childAccepted childRules childValidRules childIntent request childSlot receiptSlot names progress guidance using (trace; intentFor)

    parentContinues : ∀ world (parent : Context world) (child : ChildContext world) {after last} →
      Path world child after last → Context after
    parentContinues world parent child {after} {last} path with Parent.savedRecord world (task parent)
    ... | payload , found = Continue.Model.Family.context (childCurrent last) (childSeen last) (childValid last)
      (O.recordOf owner (O.cleanupWork id (Outcome.Intent.keys intent) payload) , stillThere , refl , refl)
      (childLocated last) (childReceipt last)
      where
      trail = proj₂ (trace world child path)
      module Pass = Progress.Model.Pass (Policy.rule (childCurrent child)) childAccepted (intentFor (Policy.rule (childCurrent child)))
      stillThere : DB.lookup taskSlot after ≡ just (O.recordOf owner (O.cleanupWork id (Outcome.Intent.keys intent) payload))
      stillThere = Pass.traceMetadata trail taskSlot _ found refl
