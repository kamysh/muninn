# What a text or semantic search result must establish

The selected published checkout and its current policy determine which files
are eligible. Text matches must refer to the postings for those files.
Semantic results must refer to stored vectors associated with their content.
Text readiness and the presence of vectors are separate observations.

Exact retrieval requires a complete eligible universe. Approximate
retrieval supplies a candidate guarantee with a different strength. The
model ties the returned page, numerical values and coverage to the selected
mode. The adapter supplies actual Postgres postings and vector decoding.

[Retrieval requirements](../RETRIEVAL.md) · [Worktree query adapter](../../crates/core/src/worktrees/search.rs) · [Persistence tests](../../crates/core/tests/family_persistence/worktrees.rs)

```agda
{-# OPTIONS --safe #-}
-- Actual text/vector matches, explicit coverage and exact/approximate outcomes.
module Muninn.Retrieval where
import Muninn.OwnedState as O
import Muninn.StoredPolicy as Policy
import Muninn.ContentViews as Content
import Muninn.PublishedViews as Published
import Muninn.VectorData as V
import Muninn.Worktree as W
import Muninn.RetrievalNumerics as Numeric
import Muninn.RetrievalCorpus as Corpus
import Muninn.RetrievalText as Text
import Muninn.RetrievalSelection as Select
open import Data.Bool using (Bool; true)
open import Data.Nat using (ℕ; _≤_; _<_)
open import Data.Nat.Properties using (≤-trans)
open import Data.List using (List; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans)

-- The catalog keeps search content opaque; the retrieval boundary binds the
-- query text, page limit and precision flag for the selected checkout. That
-- binding is adapter evidence (#52), not a parsed request in the dispatcher.
module Family (family checkout pointer : ℕ) (world : O.World)
  (policy : Policy.Family.Saved family pointer world)
  (viewsValid : Published.Valid world)
  (filesValid : Content.Family.WellFormed (Policy.Family.rule family pointer policy) world)
  (profile : W.EmbeddingKey)
  (decode : String → Maybe V.State)
  (decodeConsistent : ∀ key text → Content.Consistent
    (Corpus.candidate (O.family family) profile decode key text) world)
  (query : String) (limit : ℕ) (pageCap : limit ≤ 1000) (exact : Bool)
  (english : Text.Engine) where
  module Source = Corpus.Family family checkout pointer world policy viewsValid filesValid profile decode decodeConsistent
  module Hit = Source.Hit

  module Words = Text.Using english
```

## Require matching postings from visible chunks

Full-text results are backed by a stored posting for the chunk in the
selected view. A file retained only for a sibling checkout cannot contribute
its text. The English query engine supplies the matching and rank evidence.
Full-text search can return results before a chunk has a usable embedding.

```agda
  module Fulltext where
    record Candidate : Set where
      field hit : Source.Hit
            posting : Source.postedAt (Hit.key hit) ≡ just (Hit.text hit)
            matches : Words.Match query (Hit.text hit)
            measured : Words.Score query (Hit.text hit)
    rank : Candidate → Numeric.Rank
    rank candidate = Words.Score.rank (Candidate.measured candidate)
    module Selection = Select.For Candidate (λ c → Hit.key (Candidate.hit c)) (λ c → Hit.path (Candidate.hit c)) rank
    record Universe : Set where
      field items : List Candidate
            postingComplete : ∀ hit → Source.postedAt (Hit.key hit) ≡ just (Hit.text hit)
            scored : ∀ hit → Words.Match query (Hit.text hit) → Words.Score query (Hit.text hit)
            complete : ∀ candidate → Selection.Present candidate items
    -- Full-text search uses the complete matching set, independently of vectors.
    record Response (universe : Universe) : Set where
      field results : List Candidate
            canonical : results ≡ Selection.page limit (Universe.items universe)
            top : Selection.Top limit (Universe.items universe) results
    bounded : ∀ universe (response : Response universe) → length (Response.results response) ≤ 1000
    bounded universe response = ≤-trans (Selection.Top.bounded (Response.top response)) pageCap
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

```

## Separate eligibility, coverage, and ranking

The query vector must come from the original query and match the selected
embedding profile. Coverage accounts for the selected inventory, including
chunks that are pending. Only usable vectors contribute semantic candidates,
and each evaluated candidate needs a valid positive cosine score.

Approximate search may rank a smaller candidate pool. Exact search must
compare every eligible semantic candidate and cannot omit a nearer match
or leave a partly filled page when eligible matches remain. Both modes
respect the page limit of 1,000 results.

```agda
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
            exactPool : exact ≡ true → ∀ candidate → candidate ∈ Universe.items universe → Selection.Present candidate pool
            results : List Candidate
            canonical : results ≡ Selection.page limit pool
            topInPool : Selection.Top limit pool results
            exactTop : exact ≡ true → Selection.Top limit (Universe.items universe) results
            coverageSummary : Source.Summary inventory
    bounded : ∀ universe (response : Response universe) → length (Response.results response) ≤ 1000
    bounded universe response = ≤-trans (Selection.Top.bounded (Response.topInPool response)) pageCap
    exactHasNoOmittedNearerMatch : ∀ universe (response : Response universe) →
      exact ≡ true → ∀ candidate result → candidate ∈ Universe.items universe → result ∈ Response.results response →
      Selection.before candidate result ≡ true → Selection.Present candidate (Response.results response)
    exactHasNoOmittedNearerMatch universe response exactMode = Selection.Top.noBetterOmitted (Response.exactTop response exactMode)
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
      exact ≡ true → length (Response.results response) < limit →
      ∀ candidate → candidate ∈ Universe.items universe → Selection.Present candidate (Response.results response)
    exactKeepsEveryMatchWhenPageHasRoom universe response exactMode = Selection.Top.fills (Response.exactTop response exactMode)
```
