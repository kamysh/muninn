{-# OPTIONS --safe #-}
-- Durable work identity and phase, independent of the MCP connection.
module Muninn.WorkQueue where
import Muninn.CatalogInputs as I
import Data.Bool
import Muninn.Worktree as W
import Muninn.Types as T
import Muninn.PaginationData as Pagination
open import Data.Maybe using (Maybe)
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

-- Read requests do not become mutation receipts. A pending first search saves
-- its complete typed input and stable scope; arranged indexing has a job ID.
data Search : Set where
  code : I.SearchMode → I.SearchInput → Search
  structural : I.StructuralInput → Search
  notes : I.FamilyTarget → String → I.Page → Search
  listNotes : I.FamilyTarget → I.Page → Search

location : Search → I.Locator
location (code mode input) = I.SearchInput.location input
location (structural input) = I.StructuralInput.location input
location (notes target query page) = I.FamilyTarget.location target
location (listNotes target page) = I.FamilyTarget.location target

record SavedSearch : Set where
  constructor savedSearch
  field request : Search
        family : W.FamilyId
        checkout : W.CheckoutId
        incarnation : T.UUID

-- Saved continuations identify their accepted request; cancellation can remove
-- them without deleting another request or guessing from a text description.
data Payload : Set where
  message : String → Payload
  page : Pagination.Payload → Payload

record Continuation : Set where
  field parent : I.OperationId
        payload : Payload
        search : Maybe SavedSearch

move : Phase → Info → Info
move phase before = record before { phase = phase; generation = suc (Info.generation before) }

sameRequest : ∀ phase before → Info.id (move phase before) ≡ Info.id before × Info.parent (move phase before) ≡ Info.parent before
sameRequest phase before = refl , refl

runnable : Phase → Data.Bool.Bool
runnable queued = Data.Bool.true
runnable running = Data.Bool.true
runnable paused = Data.Bool.false
