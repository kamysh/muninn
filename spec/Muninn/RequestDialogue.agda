{-# OPTIONS --safe #-}
-- A clarification preserves the task, completed work and existing context.
module Muninn.RequestDialogue where

open import Data.String using (String)
open import Data.List using (List; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)
open import Relation.Nullary using (¬_)

record Guidance : Set where
  constructor makeGuidance
  field explanation : String
        nextAction : String
        alternatives : List String
        explanationPresent : ¬ (explanation ≡ "")
        actionPresent : ¬ (nextAction ≡ "")

data Phase : Set where
  working : Phase
  awaiting : Guidance → Phase

record Conversation (Task Fact Progress World : Set) : Set where
  constructor conversation
  field task : Task
        known : List Fact
        completed : Progress
        world : World
        phase : Phase

data Event (Fact : Set) : Set where
  ask : Guidance → Event Fact
  answer : Fact → Event Fact

data Step {Task Fact Progress World : Set} : Event Fact →
  Conversation Task Fact Progress World → Conversation Task Fact Progress World → Set where
  askStep : ∀ {task known completed world} (guidance : Guidance) →
    Step (ask guidance) (conversation task known completed world working)
      (conversation task known completed world (awaiting guidance))
  answerStep : ∀ {task known completed world guidance} (fact : Fact) →
    Step (answer fact) (conversation task known completed world (awaiting guidance))
      (conversation task (fact ∷ known) completed world working)

conversationKeepsTask : ∀ {Task Fact Progress World : Set}
  {event : Event Fact} {before after : Conversation Task Fact Progress World} →
  Step event before after → Conversation.task after ≡ Conversation.task before
conversationKeepsTask (askStep guidance) = refl
conversationKeepsTask (answerStep fact) = refl

conversationKeepsCompletedWork : ∀ {Task Fact Progress World : Set}
  {event : Event Fact} {before after : Conversation Task Fact Progress World} →
  Step event before after → Conversation.completed after ≡ Conversation.completed before
conversationKeepsCompletedWork (askStep guidance) = refl
conversationKeepsCompletedWork (answerStep fact) = refl

conversationDoesNotChangeWorld : ∀ {Task Fact Progress World : Set}
  {event : Event Fact} {before after : Conversation Task Fact Progress World} →
  Step event before after → Conversation.world after ≡ Conversation.world before
conversationDoesNotChangeWorld (askStep guidance) = refl
conversationDoesNotChangeWorld (answerStep fact) = refl

answerKeepsContext : ∀ {Task Fact Progress World : Set}
  {before after : Conversation Task Fact Progress World} {fact} →
  Step (answer fact) before after → Conversation.known after ≡ fact ∷ Conversation.known before
answerKeepsContext (answerStep fact) = refl

-- Previously supplied information remains available after clarification; it may be corrected.
stepKeepsKnown : ∀ {Task Fact Progress World : Set}
  {event : Event Fact} {before after : Conversation Task Fact Progress World} {fact} →
  Step event before after → fact ∈ Conversation.known before → fact ∈ Conversation.known after
stepKeepsKnown (askStep guidance) known = known
stepKeepsKnown (answerStep fact) known = there known

data Steps {Task Fact Progress World : Set} :
  Conversation Task Fact Progress World → Conversation Task Fact Progress World → Set where
  done : ∀ {current} → Steps current current
  more : ∀ {event before middle after} → Step event before middle → Steps middle after → Steps before after

conversationKeepsWorld : ∀ {Task Fact Progress World : Set}
  {before after : Conversation Task Fact Progress World} →
  Steps before after → Conversation.world after ≡ Conversation.world before
conversationKeepsWorld done = refl
conversationKeepsWorld (more first rest) =
  trans (conversationKeepsWorld rest) (conversationDoesNotChangeWorld first)

conversationKeepsKnown : ∀ {Task Fact Progress World : Set}
  {before after : Conversation Task Fact Progress World} {fact} →
  Steps before after → fact ∈ Conversation.known before → fact ∈ Conversation.known after
conversationKeepsKnown done known = known
conversationKeepsKnown (more first rest) known = conversationKeepsKnown rest (stepKeepsKnown first known)
