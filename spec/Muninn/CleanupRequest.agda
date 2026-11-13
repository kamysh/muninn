{-# OPTIONS --safe #-}
-- Recognize an accepted cleanup request using the existing receipt ledger.
module Muninn.CleanupRequest where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.ReceiptLedger as Ledger
import Muninn.ReceiptTypes as Receipt
import Muninn.RequestIdentity as Identity
import Muninn.CatalogInputs as Input
open import Data.Nat using (ℕ)
open import Data.Maybe using (just; nothing)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Observation : Set where
  active wrongOwner : ℕ → Receipt.Work → Observation
  response : Ledger.Reply → Observation

abstract
  observe : Input.OperationId → Identity.Meaning → O.Owner → O.World → Observation
  observe id meaning owner world with Ledger.find id world
  ... | nothing = response (Ledger.explain Ledger.unknownId)
  ... | just saved@(Ledger.found slot receiptOwner (Receipt.active stored names progress)) with Identity.sameRequest meaning stored | E.ownerEqual receiptOwner owner
  ...   | no different | _ = response (Ledger.explain Ledger.differentRequest)
  ...   | yes same | no different = wrongOwner slot progress
  ...   | yes same | yes sameOwner = active slot progress
  observe id meaning owner world | just saved@(Ledger.found slot receiptOwner (Receipt.finished stored names result)) = response (Ledger.existing meaning saved)
  observe id meaning owner world | just saved@(Ledger.found slot receiptOwner Receipt.used) = response (Ledger.existing meaning saved)

  activeObserved : ∀ id meaning owner world slot names progress →
    Ledger.find id world ≡ just (Ledger.found slot owner (Receipt.active meaning names progress)) →
    observe id meaning owner world ≡ active slot progress
  activeObserved id meaning owner world slot names progress found rewrite found
    with Identity.sameRequest meaning meaning | E.ownerEqual owner owner
  ... | no different | _ = ⊥-elim (different refl)
  ... | yes same | no different = ⊥-elim (different refl)
  ... | yes same | yes sameOwner = refl
