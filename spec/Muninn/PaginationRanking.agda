{-# OPTIONS --safe #-}
-- Saved code result order is taken from the actual retrieval/ranking model.
module Muninn.PaginationRanking where
import Muninn.PaginationData as P
import Muninn.Retrieval as R
import Muninn.RetrievalNumerics as N
import Muninn.RetrievalText as Text
import Muninn.HybridRanking as Hybrid
import Muninn.HybridNumbers as H
import Muninn.OwnedState as O
import Muninn.StoredPolicy as Policy
import Muninn.PublishedViews as Published
import Muninn.ContentViews as Content
import Muninn.SearchView as View
import Muninn.RepositoryProfile as Profile
import Muninn.VectorData as V
import Muninn.Config as C
import Muninn.CatalogInputs as I
import Muninn.Types as T
import Muninn.PaginationTraversal as Traverse
import Muninn.RequestCodecs as Codecs
import Muninn.Canonical as Canonical
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; map)
open import Data.Bool using (Bool; true; false; not)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻; ∈-map⁺)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Relation.Nullary using (yes; no)
open import Data.Empty using (⊥-elim)
open import Data.Unit using (tt)
import Data.Nat as Nat

rank : N.Rank → P.Score
rank score = record { numerator = N.Rank.numerator score; denominator = N.Rank.denominator score; positiveDenominator = N.Rank.denominatorPositive score }
fused : H.Score → P.Score
fused score = record { numerator = H.Score.numerator score; denominator = H.Score.denominator score; positiveDenominator = H.Score.denominatorPositive score }
Unique : List P.Item → Set
Unique = AllPairs (λ first second → Traverse.identity (P.Item.ref first) ≢ Traverse.identity (P.Item.ref second))

module Family (family checkout pointer : ℕ) (world : O.World)
  (policy : Policy.Family.Saved family pointer world) (viewsValid : Published.Valid world)
  (filesValid : Content.Family.WellFormed (Policy.Family.rule family pointer policy) world)
  (view : View.Family.Stored family checkout world)
  (resolved : Profile.Resolved (C.FamilyPolicy.embeddings (Policy.Family.policy family pointer policy)))
  (request : I.SearchInput) (english : Text.Engine) where
  module Query = R.Family family checkout pointer world policy viewsValid filesValid view resolved request english
  module Source = Query.Source
  module Hit = Source.Eligible.CodeHit
  module FT = Query.Fulltext

  descriptor : T.UUID → P.Scope → P.View
  descriptor id scope = record
    { id = id; scope = scope
    ; roots = P.snapshot (View.Family.Stored.root view) ∷ P.policy pointer ∷ []
    ; policyVersion = Policy.Family.Saved.version policy
    ; profile = just Source.profile; dictionaryVersion = Text.Engine.dictionaryVersion english
    ; algorithmVersion = "muninn-code-ranking-v1"; precision = I.SearchInput.precision request }

  textItem : FT.Candidate → P.Item
  textItem candidate = record
    { ref = P.codeRef (Hit.path hit) (Hit.key hit) (Hit.version hit) nothing
    ; score = just (rank (FT.rank candidate)) }
    where hit = FT.Candidate.hit candidate
  textOrder : FT.Universe → List P.Item
  textOrder universe = map textItem (FT.Selection.ordered (FT.Universe.items universe))
  everyTextCandidateRetained : ∀ universe candidate → candidate ∈ FT.Universe.items universe → textItem candidate ∈ textOrder universe
  everyTextCandidateRetained universe candidate present = ∈-map⁺ textItem (FT.Selection.orderedComplete (FT.Universe.items universe) candidate present)

  textPlan : I.OperationId → T.UUID → P.Scope → (universe : FT.Universe) → Unique (textOrder universe) → P.Plan
  textPlan id viewId scope universe unique = record
    { id = id; query = P.code I.fulltext request; view = descriptor viewId scope
    ; known = textOrder universe; pending = []; queryVector = nothing; revision = 0 }

  -- Concrete match predicates for the generic finite classifier. They name
  -- actual retrieval evidence and fixed scores, never an operation-chosen goal.
  record TextMatch (plan : P.Plan) (ref : P.Ref) (row : P.Item) : Set where
    field candidate : FT.Candidate
          sameQuery : P.Plan.query plan ≡ P.code I.fulltext request
          sourceIdentity : Traverse.identity ref ≡ Traverse.identity (P.Item.ref (textItem candidate))
          savedIdentity : P.Item.ref row ≡ ref
          actualScore : P.Item.score row ≡ P.Item.score (textItem candidate)

  seen : P.Ref → List P.Item → Bool
  seen ref [] = false
  seen (P.codeRef path key version vector) (row ∷ rows) with P.Item.ref row
  ... | P.codeRef otherPath otherKey otherVersion otherVector with Canonical.compare Codecs.path path otherPath | key Nat.≟ otherKey
  ...   | yes _ | yes _ = true
  ...   | _ | _ = seen (P.codeRef path key version vector) rows
  seen (P.codeRef path key version vector) (row ∷ rows) | _ = seen (P.codeRef path key version vector) rows
  seen ref (row ∷ rows) = seen ref rows
  unseen : List P.Ref → List P.Item → List P.Ref
  unseen [] known = []
  unseen (ref ∷ refs) known with seen ref known
  ... | true = unseen refs known
  ... | false = ref ∷ unseen refs known
  unseenIncluded : ∀ refs known ref → ref ∈ refs → seen ref known ≡ false → ref ∈ unseen refs known
  unseenIncluded (first ∷ refs) known ref present fresh with seen first known in observed
  ... | false with present
  ...   | here refl = here refl
  ...   | there later = there (unseenIncluded refs known ref later fresh)
  unseenIncluded (first ∷ refs) known ref (here refl) fresh | true = ⊥-elim (subst Data.Bool.T (Relation.Binary.PropositionalEquality.trans (Relation.Binary.PropositionalEquality.sym observed) fresh) tt)
  unseenIncluded (first ∷ refs) known ref (there later) fresh | true = unseenIncluded refs known ref later fresh

  module Semantic (query : Query.QueryVector) (inventory : Source.Inventory) where
    module Sem = Query.Semantic query inventory
    -- The saved reference includes the exact association incarnation, so later
    -- embedding backfill cannot silently replace a vector in the saved view.
    record Association (candidate : Sem.Candidate) : Set where
      field slot : ℕ
            located : O.DB.lookup slot world ≡ just (O.recordOf (O.family family)
              (O.vector (Hit.key (Sem.Candidate.hit candidate)) (V.usable (Source.Semantic.value (Sem.Candidate.vector candidate)))))
    item : (candidate : Sem.Candidate) → Association candidate → P.Item
    item candidate association = record
      { ref = P.codeRef (Hit.path hit) (Hit.key hit) (Hit.version hit) (just (Association.slot association))
      ; score = just (rank (Sem.rank candidate)) }
      where hit = Sem.Candidate.hit candidate
    order : Sem.Universe → (associations : ∀ candidate → Association candidate) → List P.Item
    order universe associations = map (λ candidate → item candidate (associations candidate)) (Sem.Selection.ordered (Sem.Universe.items universe))
    everySemanticCandidateRetained : ∀ universe associations candidate → candidate ∈ Sem.Universe.items universe → item candidate (associations candidate) ∈ order universe associations
    everySemanticCandidateRetained universe associations candidate present = ∈-map⁺ (λ candidate → item candidate (associations candidate)) (Sem.Selection.orderedComplete (Sem.Universe.items universe) candidate present)
    cachedQuery : List N.Binary32
    cachedQuery = N.Stored32.words (Query.QueryVector.stored32 query)
    queryIsTheActualProviderValue : map N.widen cachedQuery ≡ V.Value.values (Query.QueryVector.value query)
    queryIsTheActualProviderValue = N.Stored32.exactWidening (Query.QueryVector.stored32 query)

    record Match (plan : P.Plan) (ref : P.Ref) (row : P.Item) : Set where
      field candidate : Sem.Candidate
            association : Association candidate
            sameQuery : P.Plan.query plan ≡ P.code I.semantic request
            sameVector : P.Plan.queryVector plan ≡ just cachedQuery
            sourceIdentity : ref ≡ P.Item.ref (item candidate association)
            actualResult : row ≡ item candidate association

    data Frozen (hit : Source.Hit) : Set where
      unavailable : Source.Vector.linkedReady world (Hit.key hit) (Hit.text hit) ≡ nothing → Frozen hit
      available : (ready : Source.Semantic hit) (slot : ℕ) →
        O.DB.lookup slot world ≡ just (O.recordOf (O.family family) (O.vector (Hit.key hit) (V.usable (Source.Semantic.value ready)))) → Frozen hit
    reference : ∀ hit → Frozen hit → P.Ref
    reference hit (unavailable absent) = P.codeRef (Hit.path hit) (Hit.key hit) (Hit.version hit) nothing
    reference hit (available ready slot located) = P.codeRef (Hit.path hit) (Hit.key hit) (Hit.version hit) (just slot)
    sourceRefs : (∀ hit → Frozen hit) → List P.Ref
    sourceRefs frozen = map (λ hit → reference hit (frozen hit)) (Source.Inventory.items inventory)
    remaining : (∀ hit → Frozen hit) → List P.Item → List P.Ref
    remaining frozen known with I.SearchInput.precision request
    ... | I.exact = []
    ... | I.approximate = unseen (sourceRefs frozen) known
    allUnseenCaptured : ∀ frozen known hit → hit ∈ Source.Inventory.items inventory →
      seen (reference hit (frozen hit)) known ≡ false → I.SearchInput.precision request ≡ I.approximate →
      reference hit (frozen hit) ∈ remaining frozen known
    allUnseenCaptured frozen known hit present fresh approximate rewrite approximate =
      unseenIncluded (sourceRefs frozen) known (reference hit (frozen hit)) (∈-map⁺ (λ hit → reference hit (frozen hit)) present) fresh
    plan : I.OperationId → T.UUID → P.Scope → (universe : Sem.Universe) →
      (associations : ∀ candidate → Association candidate) → (∀ hit → Frozen hit) → Unique (order universe associations) → P.Plan
    plan id viewId scope universe associations frozen unique = record
      { id = id; query = P.code I.semantic request; view = descriptor viewId scope
      ; known = order universe associations; pending = remaining frozen (order universe associations)
      ; queryVector = just cachedQuery; revision = 0 }

  module PoolFusion (overrides : H.Overrides (I.SearchInput.ranking request)) (query : Query.QueryVector) (inventory : Source.Inventory)
    (textPool : List FT.Candidate) (semanticPool : List (Query.Semantic.Candidate query inventory)) where
    module Pipeline = Hybrid.Family.Using family checkout pointer world policy viewsValid filesValid view resolved request english overrides query inventory
    module Input = Pipeline.Pools textPool semanticPool
    module Sem = Query.Semantic query inventory
    module Embeddings = Semantic query inventory
    -- A text-origin candidate that is also semantic keeps that association too.
    -- This is source metadata, not a second ranking or a new candidate quota.
    record Links : Set where
      field association : ∀ candidate → Embeddings.Association candidate
            semanticSlot : Input.Origin → Maybe ℕ
            slotCorrect : ∀ origin candidate → Input.hit origin ≡ Sem.Candidate.hit candidate →
              candidate ∈ semanticPool → semanticSlot origin ≡ just (Embeddings.Association.slot (association candidate))
    module Evaluated (evaluation : Input.Evaluation) (links : Links) where
      module Results = Input.Evaluated evaluation
      item : Input.Origin → P.Item
      item origin = record
        { ref = P.codeRef (Hit.path hit) (Hit.key hit) (Hit.version hit) (Links.semanticSlot links origin)
        ; score = just (fused (Input.Evaluation.score evaluation origin)) }
        where hit = Input.hit origin
      order : List P.Item
      order = map item Results.ordered
      keepsEveryCandidate : ∀ origin → origin ∈ Input.candidates → item origin ∈ order
      keepsEveryCandidate origin present = ∈-map⁺ item (Results.everyCandidateRanked origin present)
      record Match (plan : P.Plan) (ref : P.Ref) (row : P.Item) : Set where
        field origin : Input.Origin
              inPool : origin ∈ Input.candidates
              sameQuery : P.Plan.query plan ≡ P.code I.hybrid request
              sameVector : P.Plan.queryVector plan ≡ just Embeddings.cachedQuery
              sourceIdentity : ref ≡ P.Item.ref (item origin)
              actualResult : row ≡ item origin
      plan : I.OperationId → T.UUID → P.Scope → (∀ hit → Embeddings.Frozen hit) → Unique order → P.Plan
      plan id viewId scope frozen unique = record
        { id = id; query = P.code I.hybrid request; view = descriptor viewId scope
        ; known = order; pending = Embeddings.remaining frozen order
        ; queryVector = just Embeddings.cachedQuery; revision = 0 }
      -- Store the complete ordered modality union. The response page size and
      -- approximate retrieval budget are never applied a second time here.

  module Fusion (overrides : H.Overrides (I.SearchInput.ranking request)) (query : Query.QueryVector) (inventory : Source.Inventory)
    (legs : Hybrid.Family.Using.Legs family checkout pointer world policy viewsValid filesValid view resolved request english overrides query inventory) where
    module InitialPipeline = Hybrid.Family.Using family checkout pointer world policy viewsValid filesValid view resolved request english overrides query inventory
    module Initial = InitialPipeline.Inputs legs
    open PoolFusion overrides query inventory Initial.textPool Initial.semanticPool public
