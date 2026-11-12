{-# OPTIONS --safe #-}
-- Logical persistent state and independent operation outcomes.
module Muninn.ApplicationWorld where

open import Data.List using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; sym; trans)
open import Relation.Nullary using (¬_)

data Kind : Set where
  registration checkout policyHistory policyCurrent : Kind
  note notePosting noteVector : Kind
  fileVersion fileBinding chunk posting vector symbol edge graphSnapshot : Kind
  legacy staging pendingWork reader continuation : Kind
  schemaResource graphResource usage : Kind

record Entry (Key Value : Set) : Set where
  field kind : Kind
        value : Value
        familyReferences : List (Kind × Key)
        installationReferences : List Key

-- A marker has no repository, path, request or result fields.
data Receipt (Family Request Result : Set) : Set where
  active : List Family → Request → Receipt Family Request Result
  completed : List Family → Request → Result → Receipt Family Request Result
  used : Receipt Family Request Result

record World (Family Key Value RequestId Request Result : Set) : Set where
  field familyData : Family → Key → Maybe (Entry Key Value)
        installationData : Key → Maybe Value
        receipts : RequestId → Maybe (Receipt Family Request Result)

-- Ownership of request and result content is an independent semantic input.
-- Receipt metadata must match it. The dispatcher must bind these inputs to
-- the agreed semantics rather than accepting operation-chosen predicates.
WellFormed : ∀ {Family Key Value RequestId Request Result} →
  (Request → Family → Set) → (Result → Family → Set) →
  World Family Key Value RequestId Request Result → Set
WellFormed {Family} {Key} {Value} requestOwns resultOwns world =
  (∀ family key entry expected target → World.familyData world family key ≡ just entry →
    (expected , target) ∈ Entry.familyReferences entry → Σ (Entry Key Value) (λ targetEntry →
      (World.familyData world family target ≡ just targetEntry) × (Entry.kind targetEntry ≡ expected))) ×
  ((∀ family key entry target → World.familyData world family key ≡ just entry →
    target ∈ Entry.installationReferences entry → Σ Value (λ targetValue →
      World.installationData world target ≡ just targetValue)) ×
  ((∀ id owners request family → World.receipts world id ≡ just (active owners request) →
      (requestOwns request family → family ∈ owners) × (family ∈ owners → requestOwns request family)) ×
   (∀ id owners request result family → World.receipts world id ≡ just (completed owners request result) →
      ((requestOwns request family ⊎ resultOwns result family) → family ∈ owners) ×
      (family ∈ owners → (requestOwns request family ⊎ resultOwns result family)))))

-- These predicates are fixed by the outcome model, not by a removal script.
-- Installation records and receipt contents can themselves belong to a family.
NoFamilyData : ∀ {Family Key Value RequestId Request Result} →
  (Value → Family → Set) → (Request → Family → Set) → (Result → Family → Set) → Family →
  World Family Key Value RequestId Request Result → Set
NoFamilyData installationOwns requestOwns resultOwns family world =
  (∀ key → World.familyData world family key ≡ nothing) ×
  ((∀ key value → World.installationData world key ≡ just value → ¬ installationOwns value family) ×
  ((∀ id owners request → World.receipts world id ≡ just (active owners request) → ¬ requestOwns request family) ×
   (∀ id owners request result → World.receipts world id ≡ just (completed owners request result) →
      ¬ (requestOwns request family ⊎ resultOwns result family))))

PreservesOtherFamilies : ∀ {Family Key Value RequestId Request Result} → Family →
  World Family Key Value RequestId Request Result → World Family Key Value RequestId Request Result → Set
PreservesOtherFamilies family before after = ∀ other key → other ≢ family →
  World.familyData after other key ≡ World.familyData before other key

PreservesUnrelatedInstallation : ∀ {Family Key Value RequestId Request Result} →
  (Value → Family → Set) → Family → World Family Key Value RequestId Request Result →
  World Family Key Value RequestId Request Result → Set
PreservesUnrelatedInstallation installationOwns family before after = ∀ key →
  (∀ value → World.installationData before key ≡ just value → ¬ installationOwns value family) →
  World.installationData after key ≡ World.installationData before key

-- Unrelated requests and every existing used-ID marker remain intact.
PreservesUnrelatedReceipts : ∀ {Family Key Value RequestId Request Result} →
  (Request → Family → Set) → (Result → Family → Set) → Family →
  World Family Key Value RequestId Request Result → World Family Key Value RequestId Request Result → Set
PreservesUnrelatedReceipts requestOwns resultOwns family before after =
  (∀ id → World.receipts before id ≡ just used → World.receipts after id ≡ just used) ×
  ((∀ id owners request → World.receipts before id ≡ just (active owners request) → ¬ requestOwns request family →
      World.receipts after id ≡ just (active owners request)) ×
   (∀ id owners request result → World.receipts before id ≡ just (completed owners request result) →
      ¬ (requestOwns request family ⊎ resultOwns result family) →
      World.receipts after id ≡ just (completed owners request result)))

-- The independent goal cannot leave a present family record unchanged.
forgetChangesPresentRecord : ∀ {Family Key Value RequestId Request Result}
  (installationOwns : Value → Family → Set) (requestOwns : Request → Family → Set) (resultOwns : Result → Family → Set)
  (family : Family) (before after : World Family Key Value RequestId Request Result) key entry →
  World.familyData before family key ≡ just entry → NoFamilyData installationOwns requestOwns resultOwns family after →
  World.familyData after family key ≢ World.familyData before family key
forgetChangesPresentRecord installationOwns requestOwns resultOwns family before after key entry present gone unchanged =
  impossible (trans (sym (proj₁ gone key)) (trans unchanged present))
  where
  impossible : ∀ {A : Set} {item : A} → nothing ≡ just item → ⊥
  impossible ()

-- A family-owned installation record must also change, even though it is not
-- stored in the family-owned map.
forgetChangesOwnedInstallation : ∀ {Family Key Value RequestId Request Result}
  (installationOwns : Value → Family → Set) (requestOwns : Request → Family → Set) (resultOwns : Result → Family → Set)
  (family : Family) (before after : World Family Key Value RequestId Request Result) key value →
  World.installationData before key ≡ just value → installationOwns value family →
  NoFamilyData installationOwns requestOwns resultOwns family after →
  World.installationData after key ≢ World.installationData before key
forgetChangesOwnedInstallation installationOwns requestOwns resultOwns family before after key value present owned gone unchanged =
  proj₁ (proj₂ gone) key value (trans unchanged present) owned
