{-# OPTIONS --safe #-}
module Muninn.ExclusionAcceptance where

open import Data.List using (List; _∷_; map)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂; ∃-syntax; _,_)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
import Muninn.Config as Config
import Muninn.Policy as Policy
import Muninn.CatalogInputs as C
import Muninn.RequestState as Requests

module Model (Record Reply : Set)
  (sameId : (a b : C.OperationId) → Dec (a ≡ b))
  (sameMeaning : (a b : Requests.Meaning) →
    Dec (Requests.canonical a ≡ Requests.canonical b)) where

  module R = Requests.Model Reply sameId sameMeaning

  data Phase : Set where
    current superseded : Phase

  record Task : Set where
    constructor task
    field request : C.OperationId
          revision : ℕ
          captured : List Record
          phase : Phase

  markSuperseded : Task → Task
  markSuperseded (task id revision captured phase) = task id revision captured superseded

  record State : Set where
    constructor state
    field policy : Policy.PolicyState
          records : List Record
          tasks : List Task
          receipts : R.Ledger

  PolicyInput : Set
  PolicyInput = C.Mutation (C.PolicyTarget × C.PolicyDraft)

  meaning : PolicyInput → Requests.Meaning
  meaning input = Requests.userMeaning C.applyPolicy input

  record MatchesDraft (input : PolicyInput) (p : Config.FamilyPolicy) : Set where
    field name : Config.FamilyPolicy.name p ≡ C.PolicyDraft.name (proj₂ (C.Mutation.input input))
          index : Config.FamilyPolicy.index p ≡ C.PolicyDraft.index (proj₂ (C.Mutation.input input))
          limits : Config.FamilyPolicy.limits p ≡ C.PolicyDraft.limits (proj₂ (C.Mutation.input input))
          watcher : Config.FamilyPolicy.watcher p ≡ C.PolicyDraft.watcher (proj₂ (C.Mutation.input input))
          embeddings : Config.FamilyPolicy.embeddings p ≡ C.PolicyDraft.embeddings (proj₂ (C.Mutation.input input))

  target : PolicyInput → C.PolicyTarget
  target input = proj₁ (C.Mutation.input input)

  module Capture where
    accept : State → PolicyInput → Config.FamilyPolicy → State
    accept s input p = state
      (Policy.commitPolicy (State.policy s) p)
      (State.records s)
      (task (C.Mutation.operationId input) (Config.FamilyPolicy.revision p)
        (State.records s) current ∷ map markSuperseded (State.tasks s))
      (R.update (C.Mutation.operationId input) (R.active (meaning input)) (State.receipts s))

    data Step (input : PolicyInput) : State → State → Set where
      accepted : ∀ {s p} →
        Policy.PolicyGuard (C.FamilyTarget.expectedFamily (C.PolicyTarget.target (target input)))
          (C.PolicyTarget.expectedRevision (target input)) (State.policy s) →
        Policy.AdmissiblePolicyChange (State.policy s) p → MatchesDraft input p →
        Requests.ownerMatches (meaning input) →
        State.receipts s (C.Mutation.operationId input) ≡ nothing →
        Step input s (accept s input p)

    accepted-receipt : ∀ {s input p} →
      State.receipts (accept s input p) (C.Mutation.operationId input) ≡ just (R.active (meaning input))
    accepted-receipt {s} {input} {p} = R.updateAt (C.Mutation.operationId input) (R.active (meaning input)) (State.receipts s)

    accepted-capture : ∀ s input p → State.tasks (accept s input p) ≡
      task (C.Mutation.operationId input) (Config.FamilyPolicy.revision p)
        (State.records s) current ∷ map markSuperseded (State.tasks s)
    accepted-capture s input p = refl

    acceptance-preserves-records : ∀ s input p → State.records (accept s input p) ≡ State.records s
    acceptance-preserves-records s input p = refl

    acceptance-preserves-other-receipt : ∀ s input p other →
      ¬ (C.Mutation.operationId input ≡ other) →
      State.receipts (accept s input p) other ≡ State.receipts s other
    acceptance-preserves-other-receipt s input p other distinct =
      R.updateOther (C.Mutation.operationId input) (R.active (meaning input))
        (State.receipts s) other distinct

    just-not-nothing : ∀ {A : Set} {x : A} → ¬ (just x ≡ nothing)
    just-not-nothing ()

    existing-id-cannot-be-accepted : ∀ {s input after entry} →
      State.receipts s (C.Mutation.operationId input) ≡ just entry →
      ¬ Step input s after
    existing-id-cannot-be-accepted present (accepted guard valid draft owner absent)
      = just-not-nothing (trans (sym present) absent)

    accepted-policy : ∀ s input p →
      Policy.PolicyState.current (State.policy (accept s input p)) ≡ p
    accepted-policy s input p = refl

    -- Interruption before the atomic commit keeps the previous world.
    -- Interruption after commit observes the complete accepted world.
    data Attempt (input : PolicyInput) : State → State → Set where
      before-commit : ∀ {s} → Attempt input s s
      after-commit : ∀ {s t} → Step input s t → Attempt input s t

    no-partial-acceptance : ∀ {input before after} →
      Attempt input before after →
      (after ≡ before) ⊎ (∃[ p ] (after ≡ accept before input p))
    no-partial-acceptance before-commit = inj₁ refl
    no-partial-acceptance (after-commit (accepted {p = p} guard valid draft owner absent)) = inj₂ (p , refl)
