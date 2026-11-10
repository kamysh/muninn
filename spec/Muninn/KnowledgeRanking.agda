{-# OPTIONS --safe #-}
-- Rank actual note matches using the same reciprocal-rank fusion as search.
module Muninn.KnowledgeRanking where
import Muninn.OwnedState as O
import Muninn.KnowledgeViews as Views
import Muninn.KnowledgeRead as Read
import Muninn.RepositoryProfile as Profile
import Muninn.RetrievalText as Text
import Muninn.RetrievalNumerics as Numeric
import Muninn.RetrievalSelection as Selection
import Muninn.HybridNumbers as N
import Muninn.Types as T
import Muninn.VectorData as V
open import Muninn.Float using (Float)
open import Data.Nat using (ℕ; suc; _≟_; _≤_)
open import Data.Bool using (Bool; true; false)
open import Data.String using (String)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_)
import Data.Maybe as Maybe
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_)

module Family (family pointer : ℕ) (codec : Views.Codec) (world : O.World)
  (active : Profile.Family.Active family pointer world)
  (checkout : Views.Family.Checkout family pointer codec world)
  (query : String) (english : Text.Engine)
  (input : Read.Family.Search.QueryVector family pointer codec world active checkout query english) where
  module Source = Read.Family.Source family pointer codec
  module Search = Read.Family.Search family pointer codec world active checkout query english
  module Words = Text.Using english
  current = Profile.Family.Active.current active
  record TextHit : Set where
    field visible : Source.Visible world current checkout
          matched : Words.Match query (Source.text (Source.Note.item (Source.Visible.note visible)))
          score : Words.Score query (Source.text (Source.Note.item (Source.Visible.note visible)))
  record SemanticHit : Set where
    field visible : Source.Visible world current checkout
          embedded : Source.Embedded world active (Source.Visible.note visible)
          score : Numeric.Cosine (V.Value.values (Search.QueryVector.value input)) (V.Value.values (Source.Embedded.value embedded))
  textKey : TextHit → ℕ
  textKey hit = Source.Note.key (Source.Visible.note (TextHit.visible hit))
  semanticKey : SemanticHit → ℕ
  semanticKey hit = Source.Note.key (Source.Visible.note (SemanticHit.visible hit))
  emptyPath : ∀ {A : Set} → A → T.FilePath
  emptyPath _ = record { value = "" }
  module TextOrder = Selection.For TextHit textKey emptyPath (λ hit → Words.Score.rank (TextHit.score hit))
  module SemanticOrder = Selection.For SemanticHit semanticKey emptyPath (λ hit → Numeric.Cosine.rank (SemanticHit.score hit))
  data Origin : Set where
    text : TextHit → Origin
    semantic : SemanticHit → Origin
  key : Origin → ℕ
  key (text hit) = textKey hit
  key (semantic hit) = semanticKey hit
  contains : ℕ → List ℕ → Bool
  contains wanted [] = false
  contains wanted (first ∷ rest) with wanted ≟ first
  ... | yes _ = true
  ... | no _ = contains wanted rest
  remaining : List ℕ → List SemanticHit → List Origin
  remaining textKeys [] = []
  remaining textKeys (hit ∷ hits) with contains (semanticKey hit) textKeys
  ... | true = remaining textKeys hits
  ... | false = semantic hit ∷ remaining textKeys hits
  position : ℕ → List ℕ → Maybe ℕ
  position wanted [] = nothing
  position wanted (first ∷ rest) with wanted ≟ first
  ... | yes _ = just 0
  ... | no _ = Maybe.map suc (position wanted rest)
  -- The source lists represent all eligible matches, not an arbitrary batch.
  record Legs : Set where
    field textHits : List TextHit
          semanticHits : List SemanticHit
          textComplete : ∀ candidate → Σ TextHit (λ found → found ∈ textHits × textKey found ≡ textKey candidate)
          semanticComplete : ∀ candidate → Σ SemanticHit (λ found → found ∈ semanticHits × semanticKey found ≡ semanticKey candidate)
          textUnique : ∀ candidate → TextOrder.count candidate textHits ≤ 1
          semanticUnique : ∀ candidate → SemanticOrder.count candidate semanticHits ≤ 1
  module Pools (legs : Legs) where
    textHits = Legs.textHits legs
    semanticHits = Legs.semanticHits legs
    textOrdered = TextOrder.ordered textHits
    semanticOrdered = SemanticOrder.ordered semanticHits
    textKeys = map textKey textOrdered
    semanticKeys = map semanticKey semanticOrdered
    candidates = map text textOrdered ++ remaining textKeys semanticOrdered
    fused : Origin → Float
    fused origin = N.fused (position (key origin) textKeys) (position (key origin) semanticKeys)
    record Scores : Set where
      field score : Origin → N.Score
            calculated : ∀ origin → N.Score.value (score origin) ≡ fused origin
    module Ranked (scores : Scores) where
      module Order = Selection.By Origin key emptyPath
        (λ origin → N.Score.numerator (Scores.score scores origin))
        (λ origin → N.Score.denominator (Scores.score scores origin))
      results = Order.ordered candidates
      everyCandidateRanked : ∀ origin → origin ∈ candidates → origin ∈ results
      everyCandidateRanked = Order.orderedComplete candidates
      allResultsAreCandidates : ∀ origin → origin ∈ results → origin ∈ candidates
      allResultsAreCandidates origin = Order.orderedSound candidates origin
