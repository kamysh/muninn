{-# OPTIONS --safe #-}
-- Atomic policy persistence, independent of first-start and pause authorization.
module Muninn.Policy where

open import Muninn.Config
open import Muninn.Worktree using (FamilyId; Checkout)
open import Data.Nat using (ℕ; suc)
open import Data.List using (List; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Bool using (Bool)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Relation.Nullary using (¬_)

record PolicyState : Set where
  field current : FamilyPolicy
        history : List FamilyPolicy
        dimension : ℕ
        started : Bool
        pauses : List Bool
        generations : List ℕ

-- Runtime filters retired checkouts before supplying the generation vector;
-- active and suppressed checkouts are invalidated together in one transaction.
commitPolicy : PolicyState → FamilyPolicy → PolicyState
commitPolicy s p = record
  { current = p
  ; history = p ∷ PolicyState.history s
  ; dimension = PolicyState.dimension s
  ; started = PolicyState.started s
  ; pauses = PolicyState.pauses s
  ; generations = map suc (PolicyState.generations s)
  }

record PolicyGuard (family : FamilyId) (revision : ℕ) (s : PolicyState) : Set where
  field familyMatches : family ≡ FamilyPolicy.family (PolicyState.current s)
        revisionMatches : revision ≡ FamilyPolicy.revision (PolicyState.current s)

-- This implementation slice cannot migrate an embedding profile.
record AdmissiblePolicyChange (s : PolicyState) (p : FamilyPolicy) : Set where
  field sameFamily : FamilyPolicy.family p ≡ FamilyPolicy.family (PolicyState.current s)
        nextRevision : FamilyPolicy.revision p ≡ suc (FamilyPolicy.revision (PolicyState.current s))
        sameDefaults : FamilyPolicy.defaults p ≡ FamilyPolicy.defaults (PolicyState.current s)
        sameBackend : EmbeddingSelection.backend (FamilyPolicy.embeddings p) ≡ EmbeddingSelection.backend (FamilyPolicy.embeddings (PolicyState.current s))
        sameModel : EmbeddingSelection.model (FamilyPolicy.embeddings p) ≡ EmbeddingSelection.model (FamilyPolicy.embeddings (PolicyState.current s))
        frozenDimension : DimFrozen (PolicyState.dimension s) p

-- Outcomes distinguish an unchanged document from an actual policy update.
data PolicyOutcome : Set where
  PolicyChanged PolicyUnchanged PolicyConflict : PolicyOutcome

data PolicyStep (family : FamilyId) (revision : ℕ) :
                PolicyState → PolicyOutcome → PolicyState → Set where
  rejectFamily : ∀ {s} → ¬ (family ≡ FamilyPolicy.family (PolicyState.current s)) →
                 PolicyStep family revision s PolicyConflict s
  rejectRevision : ∀ {s} → ¬ (revision ≡ FamilyPolicy.revision (PolicyState.current s)) →
                   PolicyStep family revision s PolicyConflict s
  noChange : ∀ {s} → PolicyGuard family revision s →
             PolicyStep family revision s PolicyUnchanged s
  changePolicy : ∀ {s p} → PolicyGuard family revision s → AdmissiblePolicyChange s p →
                 PolicyStep family revision s PolicyChanged (commitPolicy s p)

policyPreservesAuthorization : ∀ {family revision s outcome t} →
  PolicyStep family revision s outcome t →
  (PolicyState.started t ≡ PolicyState.started s) × (PolicyState.pauses t ≡ PolicyState.pauses s)
policyPreservesAuthorization (rejectFamily mismatch) = refl , refl
policyPreservesAuthorization (rejectRevision mismatch) = refl , refl
policyPreservesAuthorization (noChange guard) = refl , refl
policyPreservesAuthorization (changePolicy guard valid) = refl , refl

stalePolicyCannotWrite : ∀ {family revision s outcome t} →
  ¬ (revision ≡ FamilyPolicy.revision (PolicyState.current s)) →
  PolicyStep family revision s outcome t → t ≡ s
stalePolicyCannotWrite stale (rejectFamily mismatch) = refl
stalePolicyCannotWrite stale (rejectRevision mismatch) = refl
stalePolicyCannotWrite stale (noChange guard) = refl
stalePolicyCannotWrite stale (changePolicy guard valid) = ⊥-elim (stale (PolicyGuard.revisionMatches guard))

wrongFamilyCannotWrite : ∀ {family revision s outcome t} →
  ¬ (family ≡ FamilyPolicy.family (PolicyState.current s)) →
  PolicyStep family revision s outcome t → t ≡ s
wrongFamilyCannotWrite mismatch (rejectFamily proof) = refl
wrongFamilyCannotWrite mismatch (rejectRevision proof) = refl
wrongFamilyCannotWrite mismatch (noChange guard) = refl
wrongFamilyCannotWrite mismatch (changePolicy guard valid) = ⊥-elim (mismatch (PolicyGuard.familyMatches guard))

unchangedPolicyPreservesState : ∀ {family revision s t} →
  PolicyStep family revision s PolicyUnchanged t → t ≡ s
unchangedPolicyPreservesState (noChange guard) = refl

changedPolicyAppendsCurrent : ∀ {family revision s t} →
  PolicyStep family revision s PolicyChanged t →
  PolicyState.history t ≡ PolicyState.current t ∷ PolicyState.history s
changedPolicyAppendsCurrent (changePolicy guard valid) = refl

policyHistoryRetained : ∀ {family revision s outcome t p} →
  PolicyStep family revision s outcome t → p ∈ PolicyState.history s → p ∈ PolicyState.history t
policyHistoryRetained (rejectFamily mismatch) member = member
policyHistoryRetained (rejectRevision mismatch) member = member
policyHistoryRetained (noChange guard) member = member
policyHistoryRetained (changePolicy guard valid) member = there member

changedPolicyInvalidatesEveryCheckout : ∀ {family revision s t} →
  PolicyStep family revision s PolicyChanged t →
  PolicyState.generations t ≡ map suc (PolicyState.generations s)
changedPolicyInvalidatesEveryCheckout (changePolicy guard valid) = refl

policyPreservesDefaults : ∀ {family revision s outcome t} →
  PolicyStep family revision s outcome t →
  FamilyPolicy.defaults (PolicyState.current t) ≡ FamilyPolicy.defaults (PolicyState.current s)
policyPreservesDefaults (rejectFamily mismatch) = refl
policyPreservesDefaults (rejectRevision mismatch) = refl
policyPreservesDefaults (noChange guard) = refl
policyPreservesDefaults (changePolicy guard valid) = AdmissiblePolicyChange.sameDefaults valid

-- Shipped defaults are only an input to creating a new stored policy. Changing
-- the binary's shipped snapshot cannot change resolution of an existing one.
resolveStoredPolicy : PolicyDefaults → FamilyPolicy → EffectiveConfig
resolveStoredPolicy shipped stored = familyConfig stored

binaryDefaultsCannotChangeStoredPolicy : ∀ oldShipped newShipped stored →
  resolveStoredPolicy oldShipped stored ≡ resolveStoredPolicy newShipped stored
binaryDefaultsCannotChangeStoredPolicy oldShipped newShipped stored = refl

-- Any two checkouts using this one family policy resolve exactly the same rules.
checkoutPolicyAgreement : ∀ (a b : Checkout) p →
  CheckoutUsesFamilyPolicy a p → CheckoutUsesFamilyPolicy b p →
  (shippedA shippedB : PolicyDefaults) →
  resolveStoredPolicy shippedA p ≡ resolveStoredPolicy shippedB p
checkoutPolicyAgreement a b p ownsA ownsB shippedA shippedB = refl

record UnconfiguredPolicy : Set where
  field initialFamily : FamilyId
        initialDimension : ℕ
        initialStarted : Bool
        initialPauses : List Bool
        initialGenerations : List ℕ

initializePolicy : UnconfiguredPolicy → FamilyPolicy → PolicyState
initializePolicy before p = record
  { current = p
  ; history = p ∷ Data.List.[]
  ; dimension = UnconfiguredPolicy.initialDimension before
  ; started = UnconfiguredPolicy.initialStarted before
  ; pauses = UnconfiguredPolicy.initialPauses before
  ; generations = UnconfiguredPolicy.initialGenerations before
  }

-- Initialization is explicit and requires a revision-one policy of the family's
-- fixed dimension. There is no transition that manufactures defaults on read.
data PolicyInitialization : UnconfiguredPolicy → PolicyState → Set where
  initializeVersionOne : ∀ {before p} → FamilyPolicy.revision p ≡ 1 →
    FamilyPolicy.family p ≡ UnconfiguredPolicy.initialFamily before →
    DimFrozen (UnconfiguredPolicy.initialDimension before) p →
    PolicyInitialization before (initializePolicy before p)

initializationPreservesAuthorization : ∀ {before after} →
  PolicyInitialization before after →
  (PolicyState.started after ≡ UnconfiguredPolicy.initialStarted before) ×
  (PolicyState.pauses after ≡ UnconfiguredPolicy.initialPauses before)
initializationPreservesAuthorization (initializeVersionOne revision family dimension) = refl , refl

initializedPolicyIsRecorded : ∀ {before after} → PolicyInitialization before after →
  PolicyState.current after ∈ PolicyState.history after
initializedPolicyIsRecorded (initializeVersionOne revision family dimension) = here refl

initializedPolicyHasOwnFamily : ∀ {before after} → PolicyInitialization before after →
  FamilyPolicy.family (PolicyState.current after) ≡ UnconfiguredPolicy.initialFamily before
initializedPolicyHasOwnFamily (initializeVersionOne revision family dimension) = family

policyCurrentRemainsRecorded : ∀ {family revision s outcome t} →
  PolicyStep family revision s outcome t →
  PolicyState.current s ∈ PolicyState.history s → PolicyState.current t ∈ PolicyState.history t
policyCurrentRemainsRecorded (rejectFamily mismatch) recorded = recorded
policyCurrentRemainsRecorded (rejectRevision mismatch) recorded = recorded
policyCurrentRemainsRecorded (noChange guard) recorded = recorded
policyCurrentRemainsRecorded (changePolicy guard valid) recorded = here refl

changedPolicyAdvancesExactlyOnce : ∀ {family revision s t} →
  PolicyStep family revision s PolicyChanged t →
  FamilyPolicy.revision (PolicyState.current t) ≡ suc (FamilyPolicy.revision (PolicyState.current s))
changedPolicyAdvancesExactlyOnce (changePolicy guard valid) = AdmissiblePolicyChange.nextRevision valid
