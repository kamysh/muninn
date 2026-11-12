{-# OPTIONS --safe #-}
module Muninn.Continuation where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Product using (∃-syntax; _,_)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- A continuation keeps the identity and remaining ordering of the original
-- result view, not a reference that keeps its underlying data alive.
module Model (View Result : Set) (Available Valid : View → Set)
             (Eligible : View → Result → Set) where

  data State : Set where
    idle : View → List Result → State
    running : View → List Result → State
    restart : State
    finished : State

  -- A call can start only after the stored view is available and still valid.
  -- These observations are supplied by the surrounding application model.
  data Step : State → State → Set where
    begin : ∀ {v rest} → Available v → Valid v → Step (idle v rest) (running v rest)
    invalidate : ∀ {v rest} → ¬ Valid v → Step (idle v rest) restart
    unavailable : ∀ {v rest} → ¬ Available v → Step (idle v rest) restart
    more : ∀ {v page rest} → All (Eligible v) page →
           Step (running v (page ++ rest)) (idle v rest)
    done : ∀ {v page} → All (Eligible v) page →
           Step (running v page) finished

  -- The only continuing response retains the original view and removes a
  -- prefix; no later page may silently select a different view or reorder it.
  same-view : ∀ {v remaining v′ remaining′} →
    Step (running v remaining) (idle v′ remaining′) → v ≡ v′
  same-view (more eligible) = refl

  prefix-consumed : ∀ {v remaining v′ remaining′} →
    Step (running v remaining) (idle v′ remaining′) →
    ∃[ page ] (remaining ≡ page ++ remaining′)
  prefix-consumed (more {page = page} eligible) = page , refl

  -- Only an in-flight call may retain a view; an idle continuation does not.
  data Holds : State → View → Set where
    running-holds : ∀ {v rest} → Holds (running v rest) v

  idle-does-not-hold : ∀ {v rest held} → ¬ Holds (idle v rest) held
  idle-does-not-hold ()

