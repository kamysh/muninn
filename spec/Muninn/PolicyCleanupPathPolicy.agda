{-# OPTIONS --safe #-}
-- A run keeps the same effective policy until an external policy change.
module Muninn.PolicyCleanupPathPolicy where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.PolicyRuleAdmission as Admission
import Muninn.PolicyCleanupWorkerContinue as Continue
import Muninn.PolicyCleanupStablePolicy as Stable
import Muninn.PolicyCleanupRetry as Retry
import Muninn.StoredPolicy as Stored
import Muninn.ReceiptTypes as Receipt
import Muninn.CatalogInputs as Input
import Muninn.RequestIdentity as Identity
import Muninn.Dialogue as Dialogue
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool)
open import Data.String using (String)
open import Data.List using (List)
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

module Model where
  module Outcome = E.Model
  module Family (family pointer : ℕ) (accepted : O.World) (rules : List String)
    (validRules : Admission.Entries (Data.List.map Data.String.toList rules))
    (intent : Outcome.Intent (E.rule family rules validRules) accepted)
    (request : Input.Mutation (Input.PolicyTarget × Input.PolicyDraft)) (taskSlot receiptSlot : ℕ)
    (names : Receipt.Names (Input.Mutation.operationId request) (Identity.mutation Identity.kApplyPolicy request))
    (progress : Receipt.Work) (guidance : String → Dialogue.Prompt) where
    module Policy = Stored.Family family pointer
    open Continue.Model.Family family pointer accepted rules validRules intent request taskSlot receiptSlot names progress guidance using (Context)
    open Context using (current)
    open Retry.Model.Family family pointer accepted rules validRules intent request taskSlot receiptSlot names progress guidance using (Path; stop; step)

    sameRule : ∀ world (ctx : Context world) {after last} → Path world ctx after last →
      Policy.rule (current last) ≡ Policy.rule (current ctx)
    sameRule world ctx (stop .world .ctx) = refl
    sameRule world ctx (step .world .ctx available rest) = trans
      (sameRule _ (Continue.Model.Family.At.next family pointer accepted rules validRules intent request taskSlot receiptSlot names progress guidance world ctx available) rest)
      (Stable.Model.Family.At.sameRule family pointer accepted rules validRules intent request taskSlot receiptSlot names progress guidance world ctx available)
