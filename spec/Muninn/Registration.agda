{-# OPTIONS --safe #-}
-- Durable creation intent is distinct from an imported/current family policy.
-- Preparation failures retain the reservation; only explicit start (elsewhere)
-- can authorize indexing. Later policy edits do not rewrite creation intent.
module Muninn.Registration where

open import Muninn.Config using (FamilyPolicy)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)
open import Relation.Nullary using (¬_)

record CreationState : Set where
  field creationPolicy : Maybe FamilyPolicy
        creationCompleted : Bool
        creationStarted : Bool

pendingCreation : FamilyPolicy → CreationState
pendingCreation p = record
  { creationPolicy = just p ; creationCompleted = false ; creationStarted = false }

completeCreation : CreationState → CreationState
completeCreation s = record s { creationCompleted = true }

-- Rechecked under the registry lock at AGE graph creation. Imported rows have
-- no intent; completed registrations always require their existing graph.
data MayCreateMissingGraph : CreationState → Set where
  fromPendingIntent : ∀ p → MayCreateMissingGraph (pendingCreation p)

-- FamilyPolicy carries the frozen defaults and family UUID. Failures/retries
-- retain it; completion cannot select a different initial policy.
data CreationStep : CreationState → CreationState → Set where
  retainCreation : ∀ s → CreationStep s s
  finishCreation : ∀ p → CreationStep (pendingCreation p) (completeCreation (pendingCreation p))

recoveryPreservesIntent : ∀ {s t} → CreationStep s t →
  CreationState.creationPolicy t ≡ CreationState.creationPolicy s
recoveryPreservesIntent (retainCreation s) = refl
recoveryPreservesIntent (finishCreation p) = refl

recoveryPreservesIndexingAuthorization : ∀ {s t} → CreationStep s t →
  CreationState.creationStarted t ≡ CreationState.creationStarted s
recoveryPreservesIndexingAuthorization (retainCreation s) = refl
recoveryPreservesIndexingAuthorization (finishCreation p) = refl

completedCreationCannotReplaceGraph : ∀ {s} → CreationState.creationCompleted s ≡ true →
  ¬ MayCreateMissingGraph s
completedCreationCannotReplaceGraph () (fromPendingIntent p)

absentIntentCannotCreateGraph : ∀ {s} → CreationState.creationPolicy s ≡ nothing →
  ¬ MayCreateMissingGraph s
absentIntentCannotCreateGraph () (fromPendingIntent p)

completionRemainsComplete : ∀ {s t} → CreationState.creationCompleted s ≡ true →
  CreationStep s t → CreationState.creationCompleted t ≡ true
completionRemainsComplete complete (retainCreation s) = complete

recoveryDoesNotSubstitutePolicy : ∀ {s t p} → CreationState.creationPolicy s ≡ just p →
  CreationStep s t → CreationState.creationPolicy t ≡ just p
recoveryDoesNotSubstitutePolicy stored step = trans (recoveryPreservesIntent step) stored
