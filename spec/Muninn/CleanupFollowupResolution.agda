{-# OPTIONS --safe #-}
-- A complete follow-up removes every blocker it captured for the parent task.
module Muninn.CleanupFollowupResolution where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.ExclusionClassifier as Classifier
import Muninn.CleanupBlocker as Blocker
import Muninn.CleanupLoop as Loop
import Muninn.CleanupOrder as Order
import Data.List.Relation.Unary.All as All
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool)
open import Data.String using (String)
open import Data.List using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (inj₁; inj₂; [_,_])
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Model (excluded : List String → String → Bool) where
  module M = E.Model excluded
  module Assessment = Classifier.Model excluded
  module Run (selection : E.Rule)
    (parentWorld : O.World) (parentIntent : M.Intent selection parentWorld)
    (childWorld : O.World) (childIntent : M.Intent selection childWorld) where
    module Child = Loop.Model.Run excluded selection childWorld childIntent

    module At (world : O.World) (valid : O.Admissible world)
      (covered : Child.Covered world) (complete : Child.Final.NoPending world) where
      module Find = Blocker.Model.Current excluded selection parentWorld parentIntent world

      noBlocker : ¬ (Σ (ℕ × O.Record) (λ row → row ∈ world × Find.Blocks row))
      noBlocker ((source , value) , present , outside , owner , indexed , sourceUnprotected ,
        ref , included , target , targetFound , captured , targetOwner , targetIndexed , targetUnneeded , targetUnprotected)
        with Assessment.Assessment.needed? selection world source
      ... | no sourceUnneeded = complete source
        (value , sourceFound , sourceCaptured , owner , indexed , inj₁ sourceUnneeded)
        where
        sourceFound = Order.memberLookup world source value (O.Admissible.unique valid) present
        sourceCaptured = covered source value sourceFound owner
      ... | yes sourceNeeded with Child.Final.projectionView world value
      ...   | inj₂ (otherOwner , otherIndexed , changed) = complete source
        (value , sourceFound , sourceCaptured , owner , indexed , inj₂ (sourceNeeded , changed))
        where
        sourceFound = Order.memberLookup world source value (O.Admissible.unique valid) present
        sourceCaptured = covered source value sourceFound owner
      ...   | inj₁ canonical = [ targetUnneeded , targetUnprotected ]
        (Child.referenceNeed world source value ref sourceFound included resolved sourceNeeded canonical)
        where
        sourceFound = Order.memberLookup world source value (O.Admissible.unique valid) present
        resolved = All.lookup (All.lookup (O.Admissible.sound valid) present) included
