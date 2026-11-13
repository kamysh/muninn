{-# OPTIONS --safe #-}
-- Schedule a newer blocker only if no accepted cleanup task already covers it.
module Muninn.CleanupFollowupSelection where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.CleanupBlocker as Blocker
import Muninn.CleanupFinalization as Finalization
import Muninn.CleanupEffects as Effects
import Muninn.ExclusionClassifier as Classifier
import Muninn.FiniteClosure as F
import Muninn.ReceiptLedger as Ledger
import Muninn.CatalogInputs as Input
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool)
open import Data.String using (String)
open import Data.List using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

module Model (excluded : List String → String → Bool) where
  module Outcome = E.Model excluded
  module Current (selection : E.Rule) (accepted : O.World) (intent : Outcome.Intent selection accepted)
    (id : Input.OperationId) (world : O.World) where
    module Find = Blocker.Model.Current excluded selection accepted intent world

    Covers : ℕ → O.Record → Set
    Covers key value = Σ (List ℕ) (λ keys →
      (Finalization.taskIdentity (O.body value) ≡ just (id , keys)) × (key ∈ keys))

    covers? : ∀ key value → Dec (Covers key value)
    covers? key value with Finalization.taskIdentity (O.body value)
    ... | nothing = no (λ { (keys , () , present) })
    ... | just (other , keys) with Ledger.sameId other id
    ...   | no distinct = no (λ { (stored , same , present) → distinct (cong proj₁ (just-injective same)) })
    ...   | yes refl with F.member key keys
    ...     | no absent = no (λ { (stored , same , present) → absent (substMember (just-injective same) present) })
      where
      substMember : ∀ {stored} → (id , keys) ≡ (id , stored) → key ∈ stored → key ∈ keys
      substMember refl present = present
    ...     | yes present = yes (keys , refl , present)

    Covered : ℕ → Set
    Covered key = Σ (ℕ × O.Record) (λ row → row ∈ world × Covers key (proj₂ row))

    covered? : ∀ key → Dec (Covered key)
    covered? key = F.choose (λ row → Covers key (proj₂ row)) (λ row → covers? key (proj₂ row)) world

    Unscheduled : ℕ × O.Record → Set
    Unscheduled row = Find.Blocks row × ¬ Covered (proj₁ row)

    unscheduled? : Dec (Σ (ℕ × O.Record) (λ row → row ∈ world × Unscheduled row))
    unscheduled? = F.choose Unscheduled
      (λ row → Classifier.both (Find.blocks? row) (Effects.not? (covered? (proj₁ row)))) world
