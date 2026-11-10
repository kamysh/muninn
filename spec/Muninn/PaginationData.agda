{-# OPTIONS --safe #-}
-- Private cursor data contains identities and scores, never copies of code.
module Muninn.PaginationData where
import Muninn.CatalogInputs as I
import Muninn.Types as T
import Muninn.Worktree as W
import Muninn.RetrievalNumerics as Numeric
open import Data.Nat using (ℕ; _+_; _≤_)
open import Data.List using (List; length; []; _∷_; _++_; concatMap)
open import Data.Maybe using (Maybe)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_)

data Query : Set where
  code : I.SearchMode → I.SearchInput → Query
  structural : I.StructuralInput → Query
  notes : I.FamilyTarget → String → I.Page → Query
  listNotes : I.FamilyTarget → I.Page → Query

data Scope : Set where
  checkout : W.FamilyId → W.CheckoutId → T.UUID → Scope
  family : W.FamilyId → Scope

-- Exact occurrence identities distinguish repeated relationship references.
data Ref : Set where
  codeRef : T.FilePath → ℕ → ℕ → Maybe ℕ → Ref
  symbolRef : T.FilePath → ℕ → ℕ → Ref
  edgeRef : ℕ → ℕ → Ref
  noteRef : ℕ → Maybe ℕ → Ref
data Root : Set where
  snapshot policy : ℕ → Root
  item : Ref → Root
ids : Ref → List ℕ
ids (codeRef path key version vector) = key ∷ version ∷ Data.Maybe.maybe (λ slot → slot ∷ []) [] vector
ids (symbolRef path key version) = key ∷ version ∷ []
ids (edgeRef key ordinal) = key ∷ []
ids (noteRef key vector) = key ∷ Data.Maybe.maybe (λ slot → slot ∷ []) [] vector
rootIds : Root → List ℕ
rootIds (snapshot key) = key ∷ []
rootIds (policy key) = key ∷ []
rootIds (item ref) = ids ref

-- This logical view identity is bound to actual source records by admission.
-- It does not prescribe a new physical graph, table, or snapshot architecture.
record View : Set where
  field id : T.UUID
        scope : Scope
        roots : List Root
        policyVersion : ℕ
        profile : Maybe W.EmbeddingKey
        dictionaryVersion algorithmVersion : String
        precision : I.Precision

-- Scores are stored by their exact rational image, not lossy decimal copies.
record Score : Set where
  field numerator denominator : ℕ
        positiveDenominator : 1 ≤ denominator
record Item : Set where
  field ref : Ref
        score : Maybe Score

-- Known rows grow by suffixes. Pending source identities are a finite workset;
-- a retrieval batch is not a maximum size for the query's result set.
record Plan : Set where
  field id : I.OperationId
        query : Query
        view : View
        known : List Item
        pending : List Ref
        queryVector : Maybe (List Numeric.Binary32)
        revision : ℕ
weakIds : Plan → List ℕ
weakIds plan = View.policyVersion (Plan.view plan) ∷
  (concatMap rootIds (View.roots (Plan.view plan)) ++
    (concatMap (λ row → ids (Item.ref row)) (Plan.known plan) ++ concatMap ids (Plan.pending plan)))

record Receipt (start : ℕ) : Set where
  field size end : ℕ
        rows : List Item
        next : Maybe T.UUID
        positiveSize : 1 ≤ size
        boundedSize : size ≤ 1000
        boundedRows : length rows ≤ size
        endCorrect : end ≡ start + length rows

-- A token's recorded page never changes when a later batch extends the plan.
record Token : Set where
  field id : T.UUID
        query : I.OperationId
        start : ℕ
        served : Maybe (Receipt start)

data Payload : Set where
  plan : Plan → Payload
  token : Token → Payload
