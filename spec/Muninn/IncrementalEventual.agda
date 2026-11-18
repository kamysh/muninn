{-# OPTIONS --safe #-}
-- Reported changes publish incrementally; full audits repair missed changes.
module Muninn.IncrementalEventual where

import Muninn.IncrementalObservation as O
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; _≤_; _≤?_; _≟_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

-- The observed snapshot must correspond to the actual reported paths after
-- successful validation. Unreported paths retain the prior published view.
fast : O.Snapshot → O.Snapshot → (O.Path → Bool) → O.Snapshot
fast previous observed reported path =
  if reported path then observed path else previous path

reportedPublished : ∀ previous observed reported path → reported path ≡ true →
  fast previous observed reported path ≡ observed path
reportedPublished previous observed reported path yesHere rewrite yesHere = refl

unreportedRetained : ∀ previous observed reported path → reported path ≡ false →
  fast previous observed reported path ≡ previous path
unreportedRetained previous observed reported path noHere rewrite noHere = refl

-- A successfully validated full audit replaces the selected checkout with
-- the entire observed snapshot, repairing missed changes for all paths.
audit : O.Snapshot → O.Snapshot
audit observed = observed

auditRepairs : ∀ observed path → audit observed path ≡ observed path
auditRepairs observed path = refl

Views : Set
Views = ℕ → O.Snapshot

replace : Views → ℕ → O.Snapshot → Views
replace views selected value checkout with checkout ≟ selected
... | yes _ = value
... | no _ = views checkout

otherCheckoutPreserved : ∀ views selected value other → other ≢ selected → ∀ path →
  replace views selected value other path ≡ views other path
otherCheckoutPreserved views selected value other different path with other ≟ selected
... | yes same = ⊥-elim (different same)
... | no _ = refl

auditInterval : ℕ
auditInterval = 300

auditDue : ℕ → Bool
auditDue elapsed with auditInterval ≤? elapsed
... | yes _ = true
... | no _ = false

auditDueAtInterval : ∀ elapsed → auditInterval ≤ elapsed → auditDue elapsed ≡ true
auditDueAtInterval elapsed enough with auditInterval ≤? elapsed
... | yes _ = refl
... | no notEnough = ⊥-elim (notEnough enough)

auditNotDueBeforeInterval : ∀ elapsed → ¬ (auditInterval ≤ elapsed) → auditDue elapsed ≡ false
auditNotDueBeforeInterval elapsed before with auditInterval ≤? elapsed
... | yes enough = ⊥-elim (before enough)
... | no _ = refl
