# What registration authorizes

Registration establishes a repository identity and its saved policy. First
start is a separate decision. Saved defaults and the embedding profile
belong to the registered family. Linked worktrees share that policy while
they track and publish their own content.

The registration model can represent an interrupted preparation. Retrying
registration must preserve the original intent and cannot silently authorize
initial indexing. The runtime must resolve the canonical repository identity
and confirm which resources are actually ready before reporting completion.

[Registration adapter](../../crates/core/src/family_policy/registration.rs) · [First-start adapter](../../crates/core/src/family_policy/start.rs) · [Registration and lifecycle checks](../../crates/core/tests/family_persistence.rs)

```agda
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
```

## Distinguish a reserved creation from an established family

A pending creation carries durable intent and can finish creating its
missing graph. A completed or imported registration expects the graph that
belongs to it. A missing graph in that state is a preparation problem,
because silently creating an empty graph would conceal loss of derived data.

```agda
data MayCreateMissingGraph : CreationState → Set where
  fromPendingIntent : ∀ p → MayCreateMissingGraph (pendingCreation p)

-- FamilyPolicy carries the frozen defaults and family UUID. Failures/retries
-- retain it; completion cannot select a different initial policy.
```

## Preserve the initial policy across retries

Creation stores the family identity and frozen defaults before preparation.
A failure leaves the reservation and those settings available for retry.
Completion uses that same initial policy. Later policy edits change the
current revision without rewriting why or how the family was created.
Registration also preserves the separate first-start decision.

```agda
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
```
