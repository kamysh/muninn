{-# OPTIONS --safe #-}
-- One bounded step of an accepted exclusion cleanup request.
module Muninn.PolicyCleanupWorker where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.PolicyRuleAdmission as Admission
import Muninn.CleanupDecision as Decision
import Muninn.CleanupRequest as Request
import Muninn.CleanupEffects as Effects
import Muninn.CleanupFinalization as Finalization
import Muninn.PolicyCleanupBatch as Batch
import Muninn.StoredPolicy as Stored
import Muninn.PolicyCleanupFinish as Finish
import Muninn.RecordAllocation as Allocation
import Muninn.ReceiptLedger as Ledger
import Muninn.ReceiptTypes as Receipt
import Muninn.RequestIdentity as Identity
import Muninn.CatalogInputs as Input
import Muninn.Dialogue as Dialogue
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool)
open import Data.String using (String)
open import Data.List using (List)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
module DB = O.DB

-- Map the reply while preserving each database effect and commit boundary.
mapTransaction : ∀ {A B : Set} → (A → B) → DB.Transaction A → DB.Transaction B
mapTransaction f (DB.commit value) = DB.commit (f value)
mapTransaction f (DB.abort value) = DB.abort (f value)
mapTransaction f (DB.scan next) = DB.scan (λ world → mapTransaction f (next world))
mapTransaction f (DB.read key next) = DB.read key (λ value → mapTransaction f (next value))
mapTransaction f (DB.put key value next) = DB.put key value (mapTransaction f next)
mapTransaction f (DB.remove key next) = DB.remove key (mapTransaction f next)
mapTransaction f (DB.eraseRows count keep next) = DB.eraseRows count keep (mapTransaction f next)

data Reply : Set where
  advanced waiting : Reply
  response : Ledger.Reply → Reply

message : Reply → String
message advanced = "Cleanup is progressing."
message waiting = "Cleanup will continue when the work it is waiting for finishes."
message (response _) = "See the request status for details."

module Model where
  module Outcome = E.Model

  module Family (family pointer : ℕ) (accepted : O.World) (originalRules : List String)
    (validRules : Admission.Entries (Data.List.map Data.String.toList originalRules))
    (original : Outcome.Intent (E.rule family originalRules validRules) accepted)
    (request : Input.Mutation (Input.PolicyTarget × Input.PolicyDraft)) (taskSlot : ℕ) where
    id = Input.Mutation.operationId request
    meaning = Identity.mutation Identity.kApplyPolicy request
    owner = O.family family
    captured = Outcome.Intent.keys original
    module Policy = Stored.Family family pointer
    open Batch.Model.Family family pointer accepted originalRules validRules original id taskSlot using (batch)
    open Finish.Model.Family family pointer accepted originalRules validRules original request taskSlot using (finish)

    module Current {world : O.World} (current : Policy.Saved world) where
      module Step = Batch.Model.Family.Selected family pointer accepted originalRules validRules original id taskSlot current
      open Decision.Model.Family.Current family pointer accepted originalRules validRules original id taskSlot current using (next)

      abstract
        finishStep : ℕ → Receipt.Work → (String → Dialogue.Prompt) → DB.Transaction Reply
        finishStep receiptSlot progress guidance = mapTransaction response
          (finish progress "Cleanup is waiting for remaining work." guidance
            (Ledger.continueDialogue receiptSlot progress (guidance "I cannot read the current repository settings.")))

        finishStepDefinition : ∀ receiptSlot progress guidance →
          finishStep receiptSlot progress guidance ≡ mapTransaction response
            (finish progress "Cleanup is waiting for remaining work." guidance
              (Ledger.continueDialogue receiptSlot progress (guidance "I cannot read the current repository settings.")))
        finishStepDefinition receiptSlot progress guidance = Relation.Binary.PropositionalEquality.refl

        followupStep : Receipt.Work → (String → Dialogue.Prompt) → DB.Transaction Reply
        followupStep progress guidance = mapTransaction response
          (Ledger.update id meaning (Receipt.generation progress) (Ledger.checkpoint (Receipt.versions progress))
            (Allocation.Model.Family.effect Step.selection id "Follow-up cleanup" "Cleanup is progressing." guidance))

        followupStepDefinition : ∀ progress guidance →
          followupStep progress guidance ≡ mapTransaction response
            (Ledger.update id meaning (Receipt.generation progress) (Ledger.checkpoint (Receipt.versions progress))
              (Allocation.Model.Family.effect Step.selection id "Follow-up cleanup" "Cleanup is progressing." guidance))
        followupStepDefinition progress guidance = refl

      perform : ℕ → Receipt.Work → (String → Dialogue.Prompt) → DB.Transaction Reply
      perform receiptSlot progress guidance with next
      ... | Decision.missingTask = DB.commit (response (Ledger.continueDialogue receiptSlot progress (guidance "I cannot find the saved cleanup work. Please provide its context.")))
      ... | Decision.doEdit key = mapTransaction (λ _ → advanced) (batch key Effects.unchanged)
      ... | Decision.doFinish = finishStep receiptSlot progress guidance
      ... | Decision.doWait = DB.commit waiting
      ... | Decision.doFollowup = followupStep progress guidance

    inspect : (world : O.World) → (String → Dialogue.Prompt) → DB.Transaction Reply
    inspect world guidance with Request.observe id meaning owner world
    ... | Request.response reply = DB.commit (response reply)
    ... | Request.wrongOwner receiptSlot progress = DB.commit (response (Ledger.continueDialogue receiptSlot progress (guidance "The saved request belongs to a different repository. Please clarify.")))
    ... | Request.active receiptSlot progress with Policy.observe world
    ...   | nothing = DB.commit (response (Ledger.continueDialogue receiptSlot progress (guidance "I cannot read the current repository settings. Please help restore them.")))
    ...   | just current = Current.perform current receiptSlot progress guidance

    tick : (String → Dialogue.Prompt) → DB.Transaction Reply
    tick guidance = DB.scan λ world → inspect world guidance
