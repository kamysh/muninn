{-# OPTIONS --safe #-}
-- Finite page/traversal transitions preserve the query, view and old pages.
module Muninn.Pagination where
import Muninn.PaginationData as P
import Muninn.CatalogInputs as I
import Muninn.Types as T
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans)
open import Data.List using (List; []; _∷_; _++_; length; take; drop)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; subst; sym; trans)

module State (original : P.Plan) where
  -- A source batch must make concrete finite progress. Source-specific match
  -- and ordering evidence is supplied by the fixed query outcome adapter.
  record Batch (before : P.Plan) : Set where
    field examined remaining : List P.Ref
          found : List P.Item
          partition : P.Plan.pending before ≡ examined ++ remaining
          advances : 0 < length examined
          bounded : length examined ≤ 1000
          fromExamined : ∀ row → row ∈ found → P.Item.ref row ∈ examined
  extend : ∀ before → Batch before → P.Plan
  extend before batch = record before
    { known = P.Plan.known before ++ Batch.found batch
    ; pending = Batch.remaining batch
    ; revision = suc (P.Plan.revision before) }

  sameQuery : ∀ before batch → P.Plan.query (extend before batch) ≡ P.Plan.query before
  sameQuery before batch = refl
  sameView : ∀ before batch → P.Plan.view (extend before batch) ≡ P.Plan.view before
  sameView before batch = refl
  prefix : ∀ before batch → P.Plan.known (extend before batch) ≡ P.Plan.known before ++ Batch.found batch
  prefix before batch = refl

  lengthAppend : ∀ {A : Set} (first second : List A) → length (first ++ second) ≡ length first + length second
  lengthAppend [] second = refl
  lengthAppend (x ∷ first) second = cong suc (lengthAppend first second)
  positiveSuffix : ∀ {A : Set} (first second : List A) → 0 < length first → length second < length (first ++ second)
  positiveSuffix [] second ()
  positiveSuffix {A} (x ∷ first) second positive = s≤s (suffix first second)
    where
    suffix : ∀ (first second : List A) → length second ≤ length (first ++ second)
    suffix [] second = Data.Nat.Properties.≤-refl
    suffix (x ∷ first) second = Data.Nat.Properties.m≤n⇒m≤1+n (suffix first second)
  decreases : ∀ before batch → length (P.Plan.pending (extend before batch)) < length (P.Plan.pending before)
  decreases before batch = subst (λ rows → length (Batch.remaining batch) < length rows)
    (sym (Batch.partition batch)) (positiveSuffix (Batch.examined batch) (Batch.remaining batch) (Batch.advances batch))

-- A page interval is frozen when first served; replay does not fill it again
-- from later appended batches. No per-file filtering appears in this operation.
slice : ℕ → ℕ → List P.Item → List P.Item
slice start size rows = take size (drop start rows)
takeBound : ∀ limit (rows : List P.Item) → length (take limit rows) ≤ limit
takeBound zero rows = z≤n
takeBound (suc limit) [] = z≤n
takeBound (suc limit) (row ∷ rows) = s≤s (takeBound limit rows)
pageBound : ∀ start (page : I.Page) rows → length (slice start (I.Page.size page) rows) ≤ 1000
pageBound start page rows = ≤-trans (takeBound (I.Page.size page) (drop start rows)) (I.Page.bounded page)

end : P.Plan → P.Token → I.Page → ℕ
end plan token page = P.Token.start token + length (slice (P.Token.start token) (I.Page.size page) (P.Plan.known plan))
data Next (plan : P.Plan) (token : P.Token) (page : I.Page) : Set where
  done : end plan token page ≡ length (P.Plan.known plan) → P.Plan.pending plan ≡ [] → Next plan token page
  more : end plan token page < length (P.Plan.known plan) ⊎ P.Plan.pending plan ≢ [] → T.UUID → Next plan token page
nextId : ∀ {plan token page} → Next plan token page → Maybe T.UUID
nextId (done complete noWork) = nothing
nextId (more remaining id) = just id
noPrematureEnd : ∀ plan token page (next : Next plan token page) → nextId next ≡ nothing →
  end plan token page ≡ length (P.Plan.known plan) × P.Plan.pending plan ≡ []
noPrematureEnd plan token page (done complete noWork) ended = complete , noWork
noPrematureEnd plan token page (more remaining id) ()

freeze : (plan : P.Plan) (token : P.Token) (page : I.Page) → Next plan token page → P.Token
freeze plan token page next = record token
  { served = just record
    { size = I.Page.size page
    ; end = P.Token.start token + length (slice (P.Token.start token) (I.Page.size page) (P.Plan.known plan))
    ; rows = slice (P.Token.start token) (I.Page.size page) (P.Plan.known plan)
    ; next = nextId next
    ; positiveSize = I.Page.positive page; boundedSize = I.Page.bounded page
    ; boundedRows = takeBound (I.Page.size page) (drop (P.Token.start token) (P.Plan.known plan))
    ; endCorrect = refl } }
frozenStart : ∀ plan token page next → P.Token.start (freeze plan token page next) ≡ P.Token.start token
frozenStart plan token page next = refl

-- Repeating a served token returns its recorded interval. The store adapter
-- must validate current eligibility in the same atomic database snapshot.
serve : (plan : P.Plan) (token : P.Token) (page : I.Page) → Next plan token page → P.Token
serve plan token page next with P.Token.served token
... | just receipt = token
... | nothing = freeze plan token page next
replay : ∀ plan token page next receipt → P.Token.served token ≡ just receipt → serve plan token page next ≡ token
replay plan token page next receipt recorded rewrite recorded = refl
recordedPageDoesNotMixBatches : ∀ first second token page firstNext secondNext receipt → P.Token.served token ≡ just receipt →
  serve first token page firstNext ≡ serve second token page secondNext
recordedPageDoesNotMixBatches first second token page firstNext secondNext receipt recorded rewrite recorded = refl

defaultPage : I.Page
defaultPage = record { size = 10; positive = s≤s z≤n; bounded = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))))); continuation = nothing }

successor : ∀ {start} → I.OperationId → (receipt : P.Receipt start) → T.UUID → P.Token
successor query receipt id = record { id = id; query = query; start = P.Receipt.end receipt; served = nothing }
noSkippedInterval : ∀ {start} query (receipt : P.Receipt start) id →
  P.Token.start (successor query receipt id) ≡ start + length (P.Receipt.rows receipt)
noSkippedInterval query receipt id = P.Receipt.endCorrect receipt
