{-# OPTIONS --safe #-}
module Muninn.Continuation where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Product using (∃-syntax; _,_)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- A continuation keeps the identity and returned pages of the original
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
    more : ∀ {v page previous} → All (Eligible v) page →
           Step (running v previous) (idle v (previous ++ page))
    done : ∀ {v previous page} → All (Eligible v) page →
           Step (running v previous) finished

  -- A continuing response retains the original view and the pages already
  -- returned, even if approximate retrieval discovers stronger matches later.
  same-view : ∀ {v remaining v′ remaining′} →
    Step (running v remaining) (idle v′ remaining′) → v ≡ v′
  same-view (more eligible) = refl

  pages-preserved : ∀ {v remaining v′ remaining′} →
    Step (running v remaining) (idle v′ remaining′) →
    ∃[ page ] (remaining′ ≡ remaining ++ page)
  pages-preserved (more {page = page} eligible) = page , refl

  -- Only an in-flight call may retain a view; an idle continuation does not.
  data Holds : State → View → Set where
    running-holds : ∀ {v rest} → Holds (running v rest) v

  idle-does-not-hold : ∀ {v rest held} → ¬ Holds (idle v rest) held
  idle-does-not-hold ()

