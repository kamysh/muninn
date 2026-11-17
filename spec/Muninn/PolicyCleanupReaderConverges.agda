{-# OPTIONS --safe #-}
-- Reader release preserves indexed data; interrupted cleanup then reaches its outcome.
module Muninn.PolicyCleanupReaderConverges where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.PolicyRuleAdmission as Admission
import Muninn.ReaderRelease as Release
import Muninn.PolicyCleanupReaderResume as Resume
import Muninn.PolicyCleanupWorkerContinue as Continue
import Muninn.PolicyCleanupRetry as Retry
import Muninn.PolicyCleanupRetryConverges as Converges
import Muninn.ReceiptTypes as Receipt
import Muninn.CatalogInputs as Input
import Muninn.RequestIdentity as Identity
import Muninn.Dialogue as Dialogue
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool)
open import Data.String using (String)
open import Data.List using (List)
open import Data.Product using (_×_)

module Exec = O.Execution

module Model where
  module Outcome = E.Model
  module Family (family pointer : ℕ) (accepted : O.World) (rules : List String)
    (validRules : Admission.Entries (Data.List.map Data.String.toList rules))
    (intent : Outcome.Intent (E.rule family rules validRules) accepted)
    (request : Input.Mutation (Input.PolicyTarget × Input.PolicyDraft)) (taskSlot receiptSlot : ℕ)
    (names : Receipt.Names (Input.Mutation.operationId request) (Identity.mutation Identity.kApplyPolicy request))
    (progress : Receipt.Work) (guidance : String → Dialogue.Prompt) where
    open Continue.Model.Family family pointer accepted rules validRules intent request taskSlot receiptSlot names progress guidance using (Context)
    module At (world : O.World) (ctx : Context world) (readerOwner : O.Owner) (reader : ℕ)
      (actual : Release.ReaderAt readerOwner reader world) where
      open Resume.Model.Family.At family pointer accepted rules validRules intent request taskSlot receiptSlot names progress guidance
        world ctx readerOwner reader actual using (after; nextContext)
      open Retry.Model.Family family pointer accepted rules validRules intent request taskSlot receiptSlot names progress guidance using (build; Run; script)
      open Run using (path)
      planned = build after nextContext
      module Interrupted {observed : O.World} (interruption : Exec.Interrupted (script (path planned)) after observed) where
        open Converges.Model.Family.At family pointer accepted rules validRules intent request taskSlot receiptSlot names progress guidance
          after nextContext (path planned) interruption public
