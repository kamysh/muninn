{-# OPTIONS --safe #-}
-- Connect policy-guarded task finalization to the independent cleanup outcome.
module Muninn.PolicyCleanupCompletionProof where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.CleanupAlignment as Alignment
import Muninn.PolicyCleanupFinish as Finish
import Muninn.PolicyCleanupBatch as Batch
import Muninn.StoredPolicy as Stored
import Muninn.CleanupFinalization as Finalization
import Muninn.RequestIdentity as Identity
import Muninn.ReceiptLedger as Ledger
import Muninn.ReceiptTypes as Receipt
import Muninn.CatalogInputs as Input
import Muninn.Dialogue as Dialogue
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool)
open import Data.String using (String)
open import Data.List using (List)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; trans)
module DB = O.DB

module Model (excluded : List String → String → Bool) where
  module Outcome = E.Model excluded

  module Family (family pointer : ℕ) (accepted : O.World) (rules : List String)
    (intent : Outcome.Intent (E.rule family rules) accepted)
    (request : Input.Mutation (Input.PolicyTarget × Input.PolicyDraft)) (taskSlot : ℕ) where
    id = Input.Mutation.operationId request
    meaning = Identity.mutation Identity.kApplyPolicy request
    module Policy = Stored.Family family pointer
    open Finish.Model.Family excluded family pointer accepted rules intent request taskSlot
      using (finish; usesCurrent; result)

    module At (before : O.World) (current : Policy.Saved before)
      (seen : Policy.observe before ≡ just current)
      (valid : O.Admissible before)
      (progress : Receipt.Work) (continuation : String) (guidance : String → Dialogue.Prompt)
      (missing : Ledger.Reply) (receiptSlot : ℕ) (names : Receipt.Names id meaning)
      (located : DB.lookup receiptSlot before ≡ just (Ledger.recordAt {id = id} (O.family family) (Receipt.active meaning names progress)))
      (found : Ledger.find id before ≡ just (Ledger.found receiptSlot (O.family family) (Receipt.active meaning names progress))) where
      module Selected = Batch.Model.Family.Selected excluded family pointer accepted rules intent id taskSlot current
      module Task = Finalization.Model.Task excluded Selected.selection accepted Selected.intent id taskSlot

      module Verified (verified : Task.Ready before) where
        open Task.Current before valid verified (result current) continuation guidance meaning names receiptSlot progress located found
          public using (reply; after; commits; checkedOutcome)
        open Alignment.Model.Contract excluded Selected.selection accepted Selected.intent using (completeFromNoPending)

        committed : DB.execute (finish progress continuation guidance missing) before ≡ (reply , after)
        committed = trans
          (cong (λ evaluation → DB.reply evaluation , DB.publish before evaluation)
            (usesCurrent before current progress continuation guidance missing seen)) commits

        currentOutcome : Outcome.Complete Selected.selection accepted Selected.intent before before
        currentOutcome = checkedOutcome

        originalOutcome : ∀ {count} → Selected.Pass.Trace count accepted before → O.Admissible accepted →
          Outcome.Complete Selected.selection accepted Selected.intent accepted before
        originalOutcome trace initialValid = completeFromNoPending trace initialValid (Data.Product.proj₂ verified)
