{-# OPTIONS --safe #-}
-- Actual text/vector matches, explicit coverage and exact/approximate outcomes.
module Muninn.Retrieval where
import Muninn.OwnedState as O
import Muninn.SearchView as View
import Muninn.StoredPolicy as Policy
import Muninn.ContentViews as Content
import Muninn.PublishedViews as Published
import Muninn.RepositoryProfile as Profile
import Muninn.Config as Config
import Muninn.VectorData as V
import Muninn.ArtifactIdentity as Equal
import Muninn.RetrievalNumerics as Numeric
import Muninn.RetrievalCorpus as Corpus
import Muninn.RetrievalText as Text
import Muninn.RetrievalSelection as Select
import Muninn.CatalogInputs as I
import Muninn.Types as T
import Muninn.Worktree as W
open import Data.Bool using (true)
open import Data.Nat using (ℕ; _≤_; _<_)
open import Data.Nat.Properties using (≤-trans)
open import Data.List using (List; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (just)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans)

module Family (family checkout pointer : ℕ) (world : O.World)
  (policy : Policy.Family.Saved family pointer world)
  (viewsValid : Published.Valid world)
  (filesValid : Content.Family.WellFormed (Policy.Family.rule family pointer policy) world)
  (view : View.Family.Stored family checkout world)
  (resolved : Profile.Resolved (Config.FamilyPolicy.embeddings (Policy.Family.policy family pointer policy)))
  (request : I.SearchInput) (english : Text.Engine) where
  module Source = Corpus.Family family checkout pointer world policy viewsValid filesValid view resolved
  module Hit = Source.Eligible.CodeHit
  profile = Source.profile
  query = I.SearchInput.query request
  limit = I.Page.size (I.SearchInput.page request)

  module Words = Text.Using english
  module Fulltext where
    record Candidate : Set where
      field hit : Source.Hit
            posting : Source.Vector.posted world (Hit.key hit) ≡ just (Hit.text hit)
            matches : Words.Match query (Hit.text hit)
            measured : Words.Score query (Hit.text hit)
    rank : Candidate → Numeric.Rank
    rank candidate = Words.Score.rank (Candidate.measured candidate)
    module Selection = Select.For Candidate (λ c → Hit.key (Candidate.hit c)) (λ c → Hit.path (Candidate.hit c)) rank
    record Universe : Set where
      field items : List Candidate
            postingComplete : ∀ hit → Source.Vector.posted world (Hit.key hit) ≡ just (Hit.text hit)
            scored : ∀ hit → Words.Match query (Hit.text hit) → Words.Score query (Hit.text hit)
            complete : ∀ candidate → Selection.Present candidate items
    -- Full-text search uses the complete matching set, independently of vectors.
    record Response (universe : Universe) : Set where
      field results : List Candidate
            canonical : results ≡ Selection.page limit (Universe.items universe)
            top : Selection.Top limit (Universe.items universe) results
    bounded : ∀ universe (response : Response universe) → length (Response.results response) ≤ 1000
    bounded universe response = ≤-trans (Selection.Top.bounded (Response.top response)) (I.Page.bounded (I.SearchInput.page request))
    matchesEveryTerm : ∀ candidate word → word ∈ Text.Engine.normalize english query →
      word ∈ Text.Engine.normalize english (Hit.text (Candidate.hit candidate))
    matchesEveryTerm candidate = Words.Match.allWords (Candidate.matches candidate)

  record QueryVector : Set where
    field value : V.Value
          currentProfile : V.Value.profile value ≡ profile
          originalQuery : V.Value.source value ≡ query
          stored32 : Numeric.Stored32 (V.Value.values value)
  queryDimension : ∀ (input : QueryVector) → V.Valid (W.EmbeddingKey.dimension profile) (V.Value.values (QueryVector.value input))
  queryDimension input = subst (λ key → V.Valid (W.EmbeddingKey.dimension key) (V.Value.values (QueryVector.value input)))
    (QueryVector.currentProfile input) (V.Value.valid (QueryVector.value input))

  module Semantic (input : QueryVector) (inventory : Source.Inventory) where
    queryValues = V.Value.values (QueryVector.value input)
    record Candidate : Set where
      field hit : Source.Hit
            vector : Source.Semantic hit
            similarity : Numeric.Cosine queryValues (V.Value.values (Source.Semantic.value vector))
    rank : Candidate → Numeric.Rank
    rank candidate = Numeric.Cosine.rank (Candidate.similarity candidate)
    module Selection = Select.For Candidate (λ c → Hit.key (Candidate.hit c)) (λ c → Hit.path (Candidate.hit c)) rank
    -- No candidate can be omitted because its valid score was inconvenient:
    -- every real vector gets an exhaustive positive/nonpositive evaluation.
    record Universe : Set where
      field coverage : Source.SemanticInventory inventory
            evaluated : ∀ hit → hit ∈ Source.Inventory.items inventory → (ready : Source.Semantic hit) →
              Numeric.Evaluation queryValues (V.Value.values (Source.Semantic.value ready))
            items : List Candidate
            complete : ∀ candidate → Selection.Present candidate items
    record Response (universe : Universe) : Set where
      field pool : List Candidate
            selectedFromUniverse : ∀ candidate → candidate ∈ pool → Selection.Present candidate (Universe.items universe)
            exactPool : I.SearchInput.precision request ≡ I.exact → ∀ candidate → candidate ∈ Universe.items universe → Selection.Present candidate pool
            results : List Candidate
            canonical : results ≡ Selection.page limit pool
            topInPool : Selection.Top limit pool results
            exactTop : I.SearchInput.precision request ≡ I.exact → Selection.Top limit (Universe.items universe) results
            coverageSummary : Source.Summary inventory
    bounded : ∀ universe (response : Response universe) → length (Response.results response) ≤ 1000
    bounded universe response = ≤-trans (Selection.Top.bounded (Response.topInPool response)) (I.Page.bounded (I.SearchInput.page request))
    exactHasNoOmittedNearerMatch : ∀ universe (response : Response universe) →
      I.SearchInput.precision request ≡ I.exact → ∀ candidate result → candidate ∈ Universe.items universe → result ∈ Response.results response →
      Selection.before candidate result ≡ true → Selection.Present candidate (Response.results response)
    exactHasNoOmittedNearerMatch universe response exact = Selection.Top.noBetterOmitted (Response.exactTop response exact)
    everyReturnedVectorValid : ∀ candidate → V.Valid (W.EmbeddingKey.dimension profile) (V.Value.values (Source.Semantic.value (Candidate.vector candidate)))
    everyReturnedVectorValid candidate = Source.validVector (Candidate.hit candidate) (Candidate.vector candidate)
    sameVectorLength : ∀ candidate → length queryValues ≡ length (V.Value.values (Source.Semantic.value (Candidate.vector candidate)))
    sameVectorLength candidate = trans (proj₁ (proj₂ (queryDimension input)))
      (sym (proj₁ (proj₂ (everyReturnedVectorValid candidate))))
    everySemanticScorePositive : ∀ candidate → 0 < Numeric.Rank.numerator (rank candidate)
    everySemanticScorePositive candidate = Numeric.Rank.positive (rank candidate)
    everySemanticScoreBounded : ∀ candidate → Numeric.Rank.numerator (rank candidate) ≤ Numeric.Rank.denominator (rank candidate)
    everySemanticScoreBounded candidate = Numeric.Cosine.bounded (Candidate.similarity candidate)
    exactKeepsEveryMatchWhenPageHasRoom : ∀ universe (response : Response universe) →
      I.SearchInput.precision request ≡ I.exact → length (Response.results response) < limit →
      ∀ candidate → candidate ∈ Universe.items universe → Selection.Present candidate (Response.results response)
    exactKeepsEveryMatchWhenPageHasRoom universe response exact = Selection.Top.fills (Response.exactTop response exact)
