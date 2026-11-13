{-# OPTIONS --safe #-}
-- Small, checked decisions used by one cleanup worker step.
module Muninn.CleanupDecision where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.PolicyCleanupBatch as Batch
import Muninn.CleanupFinalization as Finalization
import Muninn.CleanupBlocker as Blocker
import Muninn.CleanupFollowupSelection as Selection
import Muninn.CatalogInputs as Input
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false)
open import Data.String using (String)
open import Data.List using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Next : Set where
  missingTask doFinish doWait doFollowup : Next
  doEdit : ℕ → Next

module Model (excluded : List String → String → Bool) where
  module Outcome = E.Model excluded

  module Family (family pointer : ℕ) (accepted : O.World) (rules : List String)
    (intent : Outcome.Intent (E.rule family rules) accepted) (id : Input.OperationId) (slot : ℕ) where
    module Work = Batch.Model.Family excluded family pointer accepted rules intent id slot

    module Current {world : O.World} (current : Work.Policy.Saved world) where
      module Step = Work.Selected current
      module Task = Finalization.Model.Task excluded Step.selection accepted Step.intent id slot
      module Find = Blocker.Model.Current excluded Step.selection accepted Step.intent world
      module Followup = Selection.Model.Current excluded Step.selection accepted Step.intent id world

      abstract
        taskPresent : Bool
        taskPresent with Task.taskAt? world
        ... | yes _ = true
        ... | no _ = false

        taskPresentComplete : Task.TaskAt world → taskPresent ≡ true
        taskPresentComplete actual with Task.taskAt? world
        ... | yes _ = refl
        ... | no absent = ⊥-elim (absent actual)

        nextKey : Maybe ℕ
        nextKey with Step.Pass.available? world
        ... | yes (key , captured , ready) = just key
        ... | no _ = nothing

        nextAvailable : Step.Pass.Available world →
          Σ ℕ (λ key → (nextKey ≡ just key) × Step.Pass.Ready key world)
        nextAvailable available with Step.Pass.available? world
        ... | yes (key , captured , ready) = key , refl , ready
        ... | no none = ⊥-elim (none available)

        noPending : Bool
        noPending with Task.noPending? world
        ... | yes _ = true
        ... | no _ = false

        unscheduled : Bool
        unscheduled with Followup.unscheduled?
        ... | yes _ = true
        ... | no _ = false

        next : Next
        next with taskPresent
        ... | false = missingTask
        ... | true with nextKey
        ...   | just key = doEdit key
        ...   | nothing with noPending
        ...     | true = doFinish
        ...     | false with unscheduled
        ...       | true = doFollowup
        ...       | false = doWait

        nextKeyQuiet : Step.Pass.NoEdit world → nextKey ≡ nothing
        nextKeyQuiet quiet with Step.Pass.available? world
        ... | yes (key , captured , ready) = ⊥-elim (quiet key ready)
        ... | no none = refl

        noPendingComplete : Task.Final.NoPending world → noPending ≡ true
        noPendingComplete complete with Task.noPending? world
        ... | yes _ = refl
        ... | no absent = ⊥-elim (absent complete)

        nextForCompletion : Task.TaskAt world → Step.Pass.NoEdit world → Task.Final.NoPending world →
          next ≡ doFinish
        nextForCompletion actual quiet complete
          rewrite taskPresentComplete actual | nextKeyQuiet quiet | noPendingComplete complete = refl

        pendingPresent : Σ ℕ (λ key → Task.Final.Pending key world) → noPending ≡ false
        pendingPresent (key , pending) with Task.noPending? world
        ... | yes none = ⊥-elim (none key pending)
        ... | no _ = refl

        unscheduledPresent : Σ (ℕ × O.Record) (λ row → row ∈ world × Followup.Unscheduled row) → unscheduled ≡ true
        unscheduledPresent present with Followup.unscheduled?
        ... | yes _ = refl
        ... | no absent = ⊥-elim (absent present)

        nextForFollowup : Task.TaskAt world → Step.Pass.NoEdit world →
          Σ ℕ (λ key → Task.Final.Pending key world) →
          Σ (ℕ × O.Record) (λ row → row ∈ world × Followup.Unscheduled row) → next ≡ doFollowup
        nextForFollowup actual quiet pending present
          rewrite taskPresentComplete actual | nextKeyQuiet quiet | pendingPresent pending |
            unscheduledPresent present = refl

        nextForAvailable : Task.TaskAt world → Step.Pass.Available world →
          Σ ℕ (λ key → (next ≡ doEdit key) × Step.Pass.Ready key world)
        nextForAvailable actual available rewrite taskPresentComplete actual with nextAvailable available
        ... | key , selected , ready rewrite selected = key , refl , ready
