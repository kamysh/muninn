{-# OPTIONS --safe #-}
-- Productive cleanup steps do not change the effective stored policy.
module Muninn.PolicyCleanupStablePolicy where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.PolicyRuleAdmission as Admission
import Muninn.CleanupEffects as Effects
import Muninn.PolicyCleanupBatch as Batch
import Muninn.PolicyCleanupWorker as Worker
import Muninn.PolicyCleanupWorkerSafety as Safety
import Muninn.PolicyCleanupWorkerContinue as Continue
import Muninn.StoredPolicy as Stored
import Muninn.ReceiptTypes as Receipt
import Muninn.CatalogInputs as Input
import Muninn.RequestIdentity as Identity
import Muninn.Dialogue as Dialogue
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool)
open import Data.String using (String)
open import Data.List using (List)
open import Data.Maybe using (just; map)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
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
    open Worker.Model.Family family pointer accepted rules validRules intent request taskSlot using (id; tick)
    open Continue.Model.Family family pointer accepted rules validRules intent request taskSlot receiptSlot names progress guidance using (Context)
    open Context using (current; seen; task; receipt)

    module At (world : O.World) (ctx : Context world) where
      module Step = Batch.Model.Family.Selected family pointer accepted rules validRules intent id taskSlot (current ctx)
      open Continue.Model.Family.At family pointer accepted rules validRules intent request taskSlot receiptSlot names progress guidance world ctx using (next)
      open Safety.Model.Family.At family pointer accepted rules validRules intent request taskSlot world (current ctx) using (tickBatch)
      after = proj₂ (DB.execute (tick guidance) world)

      selected : Step.Pass.Available world → Policy.selectedPolicy after ≡ just (Policy.policy (current ctx))
      selected available with tickBatch receiptSlot names progress guidance (receipt ctx) (seen ctx) (task ctx) available
      ... | key , ready , equalWorld = trans (cong Policy.selectedPolicy equalWorld)
        (Batch.Model.Family.Current.selectedPolicyPreserved family pointer accepted rules validRules intent id taskSlot
          world (current ctx) (seen ctx) (task ctx) key Effects.unchanged)

      nextSelected : ∀ available → Policy.selectedPolicy after ≡ just (Policy.policy (current (next available)))
      nextSelected available = cong (map Policy.policy) (seen (next available))

      samePolicy : ∀ available → Policy.policy (current (next available)) ≡ Policy.policy (current ctx)
      samePolicy available = just-injective (trans (sym (nextSelected available)) (selected available))

      -- The exact saved rows, including admission evidence, survive a worker step.
      module RuleAfter (available : Step.Pass.Available world) where
        chosen = tickBatch receiptSlot names progress guidance (receipt ctx) (seen ctx) (task ctx) available
        key = Data.Product.proj₁ chosen
        equalWorld = proj₂ (proj₂ chosen)
        module BatchStep = Batch.Model.Family.Current family pointer accepted rules validRules intent id taskSlot
          world (current ctx) (seen ctx) (task ctx) key Effects.unchanged
        oldAfter : Policy.Saved after
        oldAfter = Policy.saved (Policy.Saved.version (current ctx)) (Policy.Saved.defaultsSlot (current ctx))
          (Policy.Saved.info (current ctx)) (Policy.Saved.frozen (current ctx))
          (trans (cong (DB.lookup pointer) equalWorld)
            (Outcome.Safety.metadata BatchStep.safety pointer _ (Policy.Saved.pointerAt (current ctx)) refl))
          (trans (cong (DB.lookup (Policy.Saved.version (current ctx))) equalWorld)
            (Outcome.Safety.metadata BatchStep.safety (Policy.Saved.version (current ctx)) _ (Policy.Saved.versionAt (current ctx)) refl))
          (trans (cong (DB.lookup (Policy.Saved.defaultsSlot (current ctx))) equalWorld)
            (Outcome.Safety.metadata BatchStep.safety (Policy.Saved.defaultsSlot (current ctx)) _ (Policy.Saved.defaultsAt (current ctx)) refl))
        sameRule : Policy.rule (current (next available)) ≡ Policy.rule (current ctx)
        sameRule = Policy.ruleDeterministic after (current (next available)) oldAfter

      sameRule : ∀ available → Policy.rule (current (next available)) ≡ Policy.rule (current ctx)
      sameRule available = RuleAfter.sameRule available
