{-# OPTIONS --safe #-}
-- Identify a later indexed record that blocks captured cleanup.
module Muninn.CleanupBlocker where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.ExclusionClassifier as Classifier
import Muninn.FiniteClosure as F
import Muninn.CleanupEffects as Effects
import Muninn.CleanupCompletion as Completion
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true)
open import Data.String using (String)
open import Data.List using (List)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Model (excluded : List String → String → Bool) where
  module Outcome = E.Model excluded

  module Current (selection : E.Rule) (accepted : O.World) (intent : Outcome.Intent selection accepted) (world : O.World) where
    module Assessment = Classifier.Model.Assessment excluded selection world
    module Final = Completion.Model.Contract excluded selection accepted intent
    captured = Outcome.Intent.keys intent
    owner = E.targetOwner selection

    Blocks : ℕ × O.Record → Set
    Blocks row = proj₁ row ∉ captured × (O.owner (proj₂ row) ≡ owner ×
      (E.indexed (proj₂ row) ≡ true ×
       (¬ Outcome.Protected selection world (proj₁ row) ×
        Σ O.Reference (λ ref → ref ∈ O.references (O.body (proj₂ row)) × Final.Candidate (O.target ref) world))))

    abstract
      blocks? : ∀ row → Dec (Blocks row)
      blocks? row = Classifier.both (Effects.not? (F.member (proj₁ row) captured))
        (Classifier.both (E.ownerEqual (O.owner (proj₂ row)) owner)
          (Classifier.both (Classifier.true? (E.indexed (proj₂ row)))
            (Classifier.both (Effects.not? (Assessment.protected? (proj₁ row)))
              (F.choose (λ ref → Final.Candidate (O.target ref) world)
                (λ ref → Final.candidate? (O.target ref) world) (O.references (O.body (proj₂ row)))))))

      blocker? : Dec (Σ (ℕ × O.Record) (λ row → row ∈ world × Blocks row))
      blocker? = F.choose Blocks blocks? world
