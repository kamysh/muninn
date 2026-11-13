{-# OPTIONS --safe #-}
-- A quiet cleanup with no held records either completes or finds a newer blocker.
module Muninn.CleanupNoStall where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.ExclusionClassifier as Classifier
import Muninn.CleanupCompletion as Completion
import Muninn.CleanupLoop as Loop
import Muninn.CleanupOrder as Order
import Muninn.CleanupBlocker as Blocker
import Muninn.FiniteClosure as F
import Data.List.Relation.Unary.All as All
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false)
open import Data.String using (String)
open import Data.List using (List)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; [_,_])
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong)
module DB = O.DB

module Model (excluded : List String → String → Bool) where
  module M = E.Model excluded
  module Assessment = Classifier.Model excluded
  module Run (selection : E.Rule) (accepted : O.World) (intent : M.Intent selection accepted) where
    module Work = Loop.Model.Run excluded selection accepted intent
    module Final = Work.Final
    module Pass = Work.Pass
    module Use = Work.Use

    module At (world : O.World) (valid : O.Admissible world)
      (released : Use.Released world) (quiet : Pass.NoEdit world) where
      module Find = Blocker.Model.Current excluded selection accepted intent world
      NoBlocker = ¬ (Σ (ℕ × O.Record) (λ row → row ∈ world × Find.Blocks row))

      sourceCandidate : NoBlocker → ∀ key → Final.Candidate key world →
        (incoming : Completion.Incoming key world) → Final.Candidate (Completion.incomingSource incoming) world
      sourceCandidate noBlock key (target , targetFound , captured , owned , indexed , unneeded , unprotected)
        ((source , value) , present , ref , included , refl) = sourceBranch (F.member source (M.Intent.keys intent))
        where
        trueNotFalse : ¬ (true ≡ false)
        trueNotFalse ()
        sourceFound = Order.memberLookup world source value (O.Admissible.unique valid) present
        resolved = All.lookup (All.lookup (O.Admissible.sound valid) present) included
        targetSame = just-injective (trans (sym (O.Resolves.found resolved)) targetFound)
        sourceOwned = Completion.familyReferenceOwner (O.owner value) (O.owner (O.Resolves.value resolved)) (E.family selection)
          (O.Resolves.rightOwner resolved) (trans (cong O.owner targetSame) owned)
        sourceUnprotected : ¬ M.Protected selection world source
        sourceUnprotected protected = unprotected (M.requireReference source value ref protected sourceFound included resolved)

        sourceBranch : Dec (source ∈ M.Intent.keys intent) → Final.Candidate source world
        sourceBranch (yes sourceCaptured) with Assessment.Assessment.needed? selection world source
        ... | no sourceUnneeded = value , sourceFound , sourceCaptured , sourceOwned ,
          Work.unneededIndexed world source value sourceFound sourceUnneeded , sourceUnneeded , sourceUnprotected
        ... | yes sourceNeeded = ⊥-elim ([ unneeded , unprotected ]
          (Work.referenceNeed world source value ref sourceFound included resolved sourceNeeded
            (Work.canonicalAtRest world source value released quiet sourceFound sourceCaptured sourceNeeded)))
        sourceBranch (no outside) with E.indexed value in sourceIndexed
        ... | true = ⊥-elim (noBlock ((source , value) , present , outside , sourceOwned , sourceIndexed ,
          sourceUnprotected , ref , included , target , targetFound , captured , owned , indexed , unneeded , unprotected))
        ... | false with Assessment.Assessment.needed? selection world source
        ...   | no sourceUnneeded = ⊥-elim (trueNotFalse (trans (sym (Work.unneededIndexed world source value sourceFound sourceUnneeded)) sourceIndexed))
        ...   | yes sourceNeeded with Final.projectionView world value
        ...     | inj₁ canonical = ⊥-elim ([ unneeded , unprotected ]
          (Work.referenceNeed world source value ref sourceFound included resolved sourceNeeded canonical))
        ...     | inj₂ (otherOwner , mustBeIndexed , changed) = ⊥-elim (trueNotFalse (trans (sym mustBeIndexed) sourceIndexed))

      noPending : NoBlocker → Final.NoPending world
      noPending noBlock key pending@(value , found , captured , owned , indexed , remaining) with remaining
      ... | inj₂ (needed , changed) = quiet key (inj₂ (value , found , captured , owned , indexed , needed , released key pending , changed))
      ... | inj₁ unneeded with Final.closedComponentProgress world (Final.candidates world) key valid
        (Final.candidatesComplete world key candidate) (λ chosen present → Final.candidatesSound world chosen present)
        (λ chosen present incoming → Final.candidatesComplete world (Completion.incomingSource incoming)
          (sourceCandidate noBlock chosen (Final.candidatesSound world chosen present) incoming))
        where candidate = value , found , captured , owned , indexed , unneeded , released key pending
      ...   | chosen , present , ready = quiet chosen (inj₁ ready)
