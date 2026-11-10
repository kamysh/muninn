{-# OPTIONS --safe #-}
-- A complete deterministic fusion pipeline over actual eligible modality hits.
module Muninn.HybridRanking where
import Muninn.Retrieval as Retrieval
import Muninn.RetrievalSelection as Selection
import Muninn.RetrievalText as Text
import Muninn.HybridNumbers as N
import Muninn.OwnedState as O
import Muninn.StoredPolicy as Policy
import Muninn.SearchView as View
import Muninn.PublishedViews as Published
import Muninn.ContentViews as Content
import Muninn.RepositoryProfile as Profile
import Muninn.AdmittedSelection as Admission
import Muninn.Config as C
import Muninn.CatalogInputs as I
import Muninn.Types as T
open import Muninn.Float using (Float; _*F_)
open import Data.Nat using (ℕ; suc; _≤_; _<_)
open import Data.Nat.Properties using (≤-trans)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; map; take; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong)

module Family (family checkout pointer : ℕ) (world : O.World)
  (policy : Policy.Family.Saved family pointer world) (viewsValid : Published.Valid world)
  (filesValid : Content.Family.WellFormed (Policy.Family.rule family pointer policy) world)
  (view : View.Family.Stored family checkout world)
  (resolved : Profile.Resolved (C.FamilyPolicy.embeddings (Policy.Family.policy family pointer policy)))
  (request : I.SearchInput) (english : Text.Engine) where
  module Query = Retrieval.Family family checkout pointer world policy viewsValid filesValid view resolved request english
  module Source = Query.Source
  module Hit = Source.Eligible.CodeHit
  module FT = Query.Fulltext
  effective = Policy.Family.policy family pointer policy
  admitted = Policy.validFrom (Policy.Family.Saved.info policy) (Policy.Family.Saved.frozen policy)

  vendor : Source.Hit → Bool
  vendor hit with Admission.classify effective admitted (Hit.gitDefault hit) (T.FilePath.value (Hit.path hit)) false
  ... | C.T2 = true
  ... | _ = false

  module Using (overrides : N.Overrides (I.SearchInput.ranking request)) (queryVector : Query.QueryVector) (inventory : Source.Inventory) where
    module Sem = Query.Semantic queryVector inventory
    limit = I.Page.size (I.SearchInput.page request)
    budget = N.budget limit
    weight = N.Score.value (N.Weight.score (N.Overrides.multiplier overrides))
    record Legs : Set where
      field text : List FT.Candidate
            semantic : Sem.Universe
            textComplete : I.SearchInput.precision request ≡ I.exact → ∀ candidate → FT.Selection.Present candidate text
            textScored : I.SearchInput.precision request ≡ I.exact → ∀ hit → Query.Words.Match Query.query (Hit.text hit) → Query.Words.Score Query.query (Hit.text hit)
            textPostings : I.SearchInput.precision request ≡ I.exact → ∀ hit → Source.Vector.posted world (Hit.key hit) ≡ just (Hit.text hit)
            textUnique : ∀ candidate → FT.Selection.count candidate text ≤ 1
            semanticUnique : ∀ candidate → Sem.Selection.count candidate (Sem.Universe.items semantic) ≤ 1
            textApproxBound : I.SearchInput.precision request ≡ I.approximate → length text ≤ budget
            semanticApproxBound : I.SearchInput.precision request ≡ I.approximate → length (Sem.Universe.items semantic) ≤ budget
            textApproxBest : I.SearchInput.precision request ≡ I.approximate → ∀ candidate result → result ∈ text →
              FT.Selection.before candidate result ≡ true → FT.Selection.Present candidate text
            textApproxFills : I.SearchInput.precision request ≡ I.approximate → length text < budget → ∀ candidate → FT.Selection.Present candidate text

    module Inputs (legs : Legs) where
      textOrdered = FT.Selection.ordered (Legs.text legs)
      semanticOrdered = Sem.Selection.ordered (Sem.Universe.items (Legs.semantic legs))
      choose : ∀ {A : Set} → List A → List A
      choose rows with I.SearchInput.precision request
      ... | I.exact = rows
      ... | I.approximate = take budget rows
      textPool = choose textOrdered
      semanticPool = choose semanticOrdered
      textHits = map FT.Candidate.hit textPool
      semanticHits = map Sem.Candidate.hit semanticPool

      data Origin : Set where
        text : FT.Candidate → Origin
        semantic : Sem.Candidate → Origin
      hit : Origin → Source.Hit
      hit (text candidate) = FT.Candidate.hit candidate
      hit (semantic candidate) = Sem.Candidate.hit candidate
      contains : Source.Hit → List Source.Hit → Bool
      contains selected [] = false
      contains selected (first ∷ rest) with Source.same selected first
      ... | true = true
      ... | false = contains selected rest
      remaining : List Sem.Candidate → List Origin
      remaining [] = []
      remaining (first ∷ rest) with contains (Sem.Candidate.hit first) textHits
      ... | true = remaining rest
      ... | false = semantic first ∷ remaining rest
      candidates : List Origin
      candidates = map text textPool ++ remaining semanticPool
      position : Source.Hit → List Source.Hit → Maybe ℕ
      position selected [] = nothing
      position selected (first ∷ rest) with Source.same selected first
      ... | true = just 0
      ... | false = Maybe.map suc (position selected rest)
      textPosition : Origin → Maybe ℕ
      textPosition origin = position (hit origin) textHits
      semanticPosition : Origin → Maybe ℕ
      semanticPosition origin = position (hit origin) semanticHits
      raw : Origin → Float
      raw origin = N.fused (textPosition origin) (semanticPosition origin)
      scoreValue : Origin → Float
      scoreValue origin with vendor (hit origin)
      ... | false = raw origin
      ... | true = raw origin *F weight

      -- The adapter owes the actual computed binary64 score, never a substitute
      -- confidence or an arbitrary number. Zero is an admitted ranking value.
      record Evaluation : Set where
        field score : Origin → N.Score
              calculated : ∀ origin → N.Score.value (score origin) ≡ scoreValue origin
      module Evaluated (evaluation : Evaluation) where
        score = Evaluation.score evaluation
        module Sort = Selection.By Origin (λ origin → Hit.key (hit origin)) (λ origin → Hit.path (hit origin))
          (λ origin → N.Score.numerator (score origin)) (λ origin → N.Score.denominator (score origin))
        ordered = Sort.ordered candidates
        everyCandidateRanked : ∀ origin → origin ∈ candidates → origin ∈ ordered
        everyCandidateRanked = Sort.orderedComplete candidates
        results = Sort.page limit candidates
        resultBound : length results ≤ 1000
        resultBound = ≤-trans (Sort.pageBound limit candidates) (I.Page.bounded (I.SearchInput.page request))
        fromModalityUnion : ∀ origin → origin ∈ results → origin ∈ candidates
        fromModalityUnion origin present = Sort.pageSound limit candidates origin present
        actualChunk : ∀ origin → origin ∈ results → O.DB.lookup (Hit.key (hit origin)) world ≡
          just (O.recordOf (O.family family) (O.chunk (Hit.version (hit origin)) (Hit.text (hit origin))))
        actualChunk origin present = Hit.chunkAt (hit origin)
        selectedFile : ∀ origin → origin ∈ results → Source.Eligible.Files.visible world checkout (Hit.path (hit origin)) ≡
          just (Content.entry (Hit.version (hit origin)) (Hit.gitDefault (hit origin)))
        selectedFile origin present = Hit.fileAt (hit origin)
        record Response : Set where
          field rows : List Origin
                canonical : rows ≡ results
                coverage : Source.Summary inventory
        response : Response
        response = record { rows = results; canonical = refl; coverage = Source.summary inventory }
        deterministic : ∀ first second → Response.rows first ≡ Response.rows second
        deterministic first second = trans (Response.canonical first) (sym (Response.canonical second))
