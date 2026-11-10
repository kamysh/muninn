{-# OPTIONS --safe #-}
-- Durable work identity and phase, independent of the MCP connection.
module Muninn.WorkQueue where
import Muninn.CatalogInputs as I
import Data.Bool
open import Data.Nat using (ℕ; suc)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

data Phase : Set where queued running paused : Phase

record Info : Set where
  constructor work
  field id parent : I.OperationId
        job : I.Job
        input : I.JobInput job
        phase : Phase
        generation : ℕ

-- Saved continuations identify their accepted request; cancellation can remove
-- them without deleting another request or guessing from a text description.
record Continuation : Set where
  field parent : I.OperationId
        payload : String

move : Phase → Info → Info
move phase before = record before { phase = phase; generation = suc (Info.generation before) }

sameRequest : ∀ phase before → Info.id (move phase before) ≡ Info.id before × Info.parent (move phase before) ≡ Info.parent before
sameRequest phase before = refl , refl

runnable : Phase → Data.Bool.Bool
runnable queued = Data.Bool.true
runnable running = Data.Bool.true
runnable paused = Data.Bool.false
