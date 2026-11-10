{-# OPTIONS --safe #-}
-- Every examined source identity is classified; omission needs non-matching
-- evidence. Finite source progress cannot turn a batch budget into a result cap.
module Muninn.PaginationTraversal where
import Muninn.PaginationData as P
import Muninn.Pagination as Page
import Muninn.Types as T
open import Data.Nat using (ℕ; _≤_; _<_; zero; suc; z≤n; s≤s)
open import Data.List using (List; []; _∷_; _++_; length; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)

data Identity : Set where
  code symbol : T.FilePath → ℕ → Identity
  edge : ℕ → ℕ → Identity
  note : ℕ → Identity
identity : P.Ref → Identity
identity (P.codeRef path key version vector) = code path key
identity (P.symbolRef path key version) = symbol path key
identity (P.edgeRef key occurrence) = edge key occurrence
identity (P.noteRef key vector) = note key

-- Match is fixed by the query outcome (text, cosine, fused or structural),
-- independently of this traversal and its statement sequence.
module Source (Match : P.Ref → P.Item → Set) where
  data Classified (ref : P.Ref) : Set where
    match : (row : P.Item) → P.Item.ref row ≡ ref → Match ref row → Classified ref
    omit : (∀ row → Match ref row → ⊥) → Classified ref
  found : ∀ {refs} → All Classified refs → List P.Item
  found [] = []
  found (match row same evidence ∷ rest) = row ∷ found rest
  found (omit evidence ∷ rest) = found rest
  sound : ∀ {refs} (classified : All Classified refs) row → row ∈ found classified → Match (P.Item.ref row) row
  sound (match first refl evidence ∷ rest) .first (here refl) = evidence
  sound (match first same evidence ∷ rest) row (there present) = sound rest row present
  sound (omit evidence ∷ rest) row present = sound rest row present
  examined : ∀ {refs} (classified : All Classified refs) row → row ∈ found classified → P.Item.ref row ∈ refs
  examined (match first same evidence ∷ rest) .first (here refl) = here same
  examined (match first same evidence ∷ rest) row (there present) = there (examined rest row present)
  examined (omit evidence ∷ rest) row present = there (examined rest row present)
  complete : ∀ {refs} (classified : All Classified refs) ref → ref ∈ refs →
    (row : P.Item) → Match ref row →
    (∀ a b → Match ref a → Match ref b → a ≡ b) → row ∈ found classified
  complete (match first same evidence ∷ rest) ref (here refl) row matches unique =
    here (sym (unique first row evidence matches))
  complete (omit absent ∷ rest) ref (here refl) row matches unique with absent row matches
  ... | ()
  complete (match first same evidence ∷ rest) ref (there present) row matches unique = there (complete rest ref present row matches unique)
  complete (omit absent ∷ rest) ref (there present) row matches unique = complete rest ref present row matches unique

  allMatchingRepresented : ∀ {refs} (classified : All Classified refs) ref → ref ∈ refs →
    (row : P.Item) → Match ref row → Σ P.Item (λ foundRow → foundRow ∈ found classified × P.Item.ref foundRow ≡ ref)
  allMatchingRepresented (match first same evidence ∷ rest) ref (here refl) row matches = first , here refl , same
  allMatchingRepresented (omit absent ∷ rest) ref (here refl) row matches with absent row matches
  ... | ()
  allMatchingRepresented (match first same evidence ∷ rest) ref (there present) row matches with allMatchingRepresented rest ref present row matches
  ... | foundRow , included , sameRef = foundRow , there included , sameRef
  allMatchingRepresented (omit absent ∷ rest) ref (there present) row matches = allMatchingRepresented rest ref present row matches

  module Work (original : P.Plan) where
    module State = Page.State original
    batch : (before : P.Plan) (first rest : List P.Ref) →
      P.Plan.pending before ≡ first ++ rest → 0 < length first → length first ≤ 1000 →
      All Classified first → State.Batch before
    batch before first rest partition advances bounded classified = record
      { examined = first; remaining = rest; found = found classified
      ; partition = partition; advances = advances; bounded = bounded
      ; fromExamined = examined classified }
    -- Any nonempty pending work has a bounded next step, regardless of the
    -- number of matches already returned. Classification may require a provider
    -- reply; no arbitrary retry/time cutoff is part of this transition.
    one : ∀ before ref rest → P.Plan.pending before ≡ ref ∷ rest → Classified ref → State.Batch before
    one before ref rest pending classified = batch before (ref ∷ []) rest pending (s≤s z≤n) (s≤s z≤n) (classified ∷ [])
    progress : ∀ before first rest partition advances bounded classified →
      length (P.Plan.pending (State.extend before (batch before first rest partition advances bounded classified))) < length (P.Plan.pending before)
    progress before first rest partition advances bounded classified = State.decreases before (batch before first rest partition advances bounded classified)

  -- This is structural recursion on the captured finite source, not a retry
  -- counter or a time limit. The interactive worker takes bounded prefixes of
  -- this same classification, keeping the remainder durably until it is done.
  drain : (plan : P.Plan) → All Classified (P.Plan.pending plan) → P.Plan
  drain plan classified = record plan { known = P.Plan.known plan ++ found classified; pending = [] }
  drained : ∀ plan classified → P.Plan.pending (drain plan classified) ≡ []
  drained plan classified = refl
