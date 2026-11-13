{-# OPTIONS --safe #-}
-- Finalize a cleanup only under the current stored policy and saved request.
module Muninn.PolicyCleanupFinish where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.StoredPolicy as Stored
import Muninn.PolicyCleanupBatch as Batch
import Muninn.CleanupFinalization as Finalization
import Muninn.ReceiptLedger as Ledger
import Muninn.ReceiptTypes as Receipt
import Muninn.CatalogInputs as Input
import Muninn.RequestIdentity as Identity
import Muninn.Dialogue as Dialogue
open import Data.Nat using (ℕ; suc; _≟_)
open import Data.Bool using (Bool)
open import Data.String using (String)
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
module DB = O.DB

module Model (excluded : List String → String → Bool) where
  module Outcome = E.Model excluded

  module Family (family pointer : ℕ) (accepted : O.World) (originalRules : List String)
    (original : Outcome.Intent (E.rule family originalRules) accepted)
    (request : Input.Mutation (Input.PolicyTarget × Input.PolicyDraft)) (taskSlot : ℕ) where
    id = Input.Mutation.operationId request
    meaning = Identity.mutation Identity.kApplyPolicy request
    acceptedRevision = suc (Input.PolicyTarget.expectedRevision (proj₁ (Input.Mutation.input request)))
    module Work = Batch.Model.Family excluded family pointer accepted originalRules original id taskSlot
    module Policy = Work.Policy

    result : ∀ {world} → Policy.Saved world → String
    result current with O.PolicyVersionInfo.revision (Policy.Saved.info current) ≟ acceptedRevision
    ... | yes _ = "Cleanup complete."
    ... | no _ = "Cleanup used the latest policy; the earlier policy was superseded."

    module Current {world : O.World} (current : Policy.Saved world) where
      module Step = Work.Selected current
      module Task = Finalization.Model.Task excluded Step.selection accepted Step.intent id taskSlot

      update : Receipt.Work → String → (String → Dialogue.Prompt) → DB.Transaction Ledger.Reply
      update progress continuation guidance = DB.scan λ snapshot →
        Ledger.update id meaning (Receipt.generation progress) (Task.change progress snapshot)
          (Task.effect (result current) continuation guidance)

    snapshot : (world : O.World) → Maybe (Policy.Saved world) → Receipt.Work → String →
      (String → Dialogue.Prompt) → Ledger.Reply → DB.Transaction Ledger.Reply
    snapshot world nothing progress continuation guidance missing = DB.abort missing
    snapshot world (just current) progress continuation guidance missing = Current.update current progress continuation guidance

    finish : Receipt.Work → String → (String → Dialogue.Prompt) → Ledger.Reply → DB.Transaction Ledger.Reply
    finish progress continuation guidance missing = DB.scan λ world →
      snapshot world (Policy.observe world) progress continuation guidance missing

    usesCurrent : ∀ world (current : Policy.Saved world) progress continuation guidance missing →
      Policy.observe world ≡ just current →
      DB.evaluate (finish progress continuation guidance missing) world ≡
        DB.evaluate (Current.update current progress continuation guidance) world
    usesCurrent world current progress continuation guidance missing seen rewrite seen = refl

    missingKeepsWorld : ∀ world progress continuation guidance missing → Policy.observe world ≡ nothing →
      DB.execute (finish progress continuation guidance missing) world ≡ (missing , world)
    missingKeepsWorld world progress continuation guidance missing absent rewrite absent = refl

    -- A still-pending captured record prevents finalization. The existing
    -- active receipt and task remain in the unchanged store.
    pendingKeepsRequest : ∀ world (current : Policy.Saved world) progress continuation guidance missing receiptSlot names key →
      Policy.observe world ≡ just current →
      Ledger.find id world ≡ just (Ledger.found receiptSlot (O.family family) (Receipt.active meaning names progress)) →
      Current.Task.Final.Pending current key world →
      DB.execute (finish progress continuation guidance missing) world ≡
        (Ledger.continueDialogue receiptSlot progress (guidance continuation) , world)
    pendingKeepsRequest world current progress continuation guidance missing receiptSlot names key seen found pending rewrite seen =
      Task.unresolvedKeepsWork (Task.change progress world) world (result current) continuation guidance meaning names receiptSlot progress
        (λ ready → proj₂ ready key pending) found
      where module Task = Current.Task current
