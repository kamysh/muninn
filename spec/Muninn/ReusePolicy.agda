{-# OPTIONS --safe #-}
-- Compatible completed analysis and vector work is retained and reused.
module Muninn.ReusePolicy where

import Muninn.Worktree as W
import Muninn.ArtifactIdentity as Identity
import Muninn.CompletedWork as Completed
import Muninn.VectorData as Vector
open import Muninn.Float using (Float)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; _<_; _≤_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (just)
open import Data.Bool using (false)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (map′; _×-dec_)

record AnalysisInput : Set where
  constructor analysisInput
  field family : W.FamilyId
        meaning : W.AnalysisMeaning

analysisInput? : (first second : AnalysisInput) → Dec (first ≡ second)
analysisInput? first second = map′ (λ { (refl , refl) → refl }) (λ { refl → refl , refl })
  (Identity.FamilyId? (AnalysisInput.family first) (AnalysisInput.family second) ×-dec
   Identity.AnalysisMeaning? (AnalysisInput.meaning first) (AnalysisInput.meaning second))

record VectorInput : Set where
  constructor vectorInput
  field family : W.FamilyId
        profile : W.EmbeddingKey
        bytes : List (Fin 256)

vectorInput? : (first second : VectorInput) → Dec (first ≡ second)
vectorInput? first second = map′ (λ { (refl , refl , refl) → refl }) (λ { refl → refl , refl , refl })
  (Identity.FamilyId? (VectorInput.family first) (VectorInput.family second) ×-dec
   (Identity.EmbeddingKey? (VectorInput.profile first) (VectorInput.profile second) ×-dec
    Identity.byteList? (VectorInput.bytes first) (VectorInput.bytes second)))

analysisOf : W.FileVersion → AnalysisInput
analysisOf version = analysisInput (W.FileVersion.family version)
  (W.analysisMeaning (W.FileVersion.analysisKey version))

vectorOf : W.EmbeddingArtifact → VectorInput
vectorOf artifact = vectorInput (W.VersionRef.family (W.EmbeddingArtifact.version artifact))
  (W.EmbeddingArtifact.key artifact) (W.EmbeddingArtifact.input artifact)

compatibleAnalysisSameInput : ∀ first second → W.AnalysisCompatible first second →
  analysisOf first ≡ analysisOf second
compatibleAnalysisSameInput first second (refl , refl) = refl

compatibleVectorSameInput : ∀ first second → W.EmbeddingCompatible first second →
  vectorOf first ≡ vectorOf second
compatibleVectorSameInput first second (refl , refl , refl) = refl

-- Spans are exact half-open byte intervals, not line numbers or text values.
ValidSpan : W.AnalysisMeaning → W.AnalyzedChunk → Set
ValidSpan input chunk =
  W.ByteSpan.start (W.AnalyzedChunk.span chunk) < W.ByteSpan.end (W.AnalyzedChunk.span chunk) ×
  W.ByteSpan.end (W.AnalyzedChunk.span chunk) ≤ length (W.AnalysisMeaning.bytes input)

UniqueSpans : List W.AnalyzedChunk → Set
UniqueSpans [] = ⊤
UniqueSpans (first ∷ rest) =
  All (λ next → W.AnalyzedChunk.span first ≢ W.AnalyzedChunk.span next) rest × UniqueSpans rest

ValidAnalysis : AnalysisInput → List W.AnalyzedChunk → Set
ValidAnalysis input chunks = All (ValidSpan (AnalysisInput.meaning input)) chunks × UniqueSpans chunks

ValidVector : VectorInput → List Float → Set
ValidVector input values = Vector.Valid (W.EmbeddingKey.dimension (VectorInput.profile input)) values

module Analysis = Completed.For AnalysisInput (List W.AnalyzedChunk) analysisInput?
module Vectors = Completed.For VectorInput (List Float) vectorInput?
module AnalysisCache = Analysis.Certified ValidAnalysis
module VectorCache = Vectors.Certified ValidVector

-- Normal indexing uses these cache actions: a completed compatible value makes
-- calculation impossible, and its validity follows from the saved cache.
analysisHitReuses : ∀ input (before : AnalysisCache.Cache) value →
  Analysis.Store.lookup input (AnalysisCache.Cache.rows before) ≡ just value →
  Analysis.invokesProvider (AnalysisCache.nextAction input before) ≡ false
analysisHitReuses input before value found =
  Analysis.hitCannotCalculate input (AnalysisCache.Cache.rows before) value found (AnalysisCache.nextAction input before)

vectorHitReuses : ∀ input (before : VectorCache.Cache) value →
  Vectors.Store.lookup input (VectorCache.Cache.rows before) ≡ just value →
  Vectors.invokesProvider (VectorCache.nextAction input before) ≡ false
vectorHitReuses input before value found =
  Vectors.hitCannotCalculate input (VectorCache.Cache.rows before) value found (VectorCache.nextAction input before)


analysisSurvivesYield : ∀ input (before after : AnalysisCache.Cache) chunks →
  Analysis.Store.lookup input (AnalysisCache.Cache.rows before) ≡ just chunks →
  Analysis.Store.lookup input (AnalysisCache.Cache.rows after) ≡ Analysis.Store.lookup input (AnalysisCache.Cache.rows before) →
  Analysis.invokesProvider (AnalysisCache.nextAction input after) ≡ false
analysisSurvivesYield input before after chunks found preserved =
  Analysis.survivingCheckpointReuses input (AnalysisCache.Cache.rows before) (AnalysisCache.Cache.rows after)
    chunks found preserved (AnalysisCache.nextAction input after)

vectorSurvivesYield : ∀ input (before after : VectorCache.Cache) vector →
  Vectors.Store.lookup input (VectorCache.Cache.rows before) ≡ just vector →
  Vectors.Store.lookup input (VectorCache.Cache.rows after) ≡ Vectors.Store.lookup input (VectorCache.Cache.rows before) →
  Vectors.invokesProvider (VectorCache.nextAction input after) ≡ false
vectorSurvivesYield input before after vector found preserved =
  Vectors.survivingCheckpointReuses input (VectorCache.Cache.rows before) (VectorCache.Cache.rows after)
    vector found preserved (VectorCache.nextAction input after)

analysisReuseValid : ∀ input (before : AnalysisCache.Cache) chunks →
  Analysis.Store.lookup input (AnalysisCache.Cache.rows before) ≡ just chunks → ValidAnalysis input chunks
analysisReuseValid input before chunks found = AnalysisCache.reusedValueValid input before chunks found

vectorReuseValid : ∀ input (before : VectorCache.Cache) vector →
  Vectors.Store.lookup input (VectorCache.Cache.rows before) ≡ just vector → ValidVector input vector
vectorReuseValid input before vector found = VectorCache.reusedValueValid input before vector found

-- Ordinary reconciliation never discards completed work. Only an explicit
-- clean rebuild clears the selected family; other families are preserved.
data Reindex : Set where
  ordinary : Reindex
  clean : W.FamilyId → Reindex

record Caches : Set where
  constructor caches
  field analyses : W.FamilyId → AnalysisCache.Cache
        vectors : W.FamilyId → VectorCache.Cache

module Reindexing (sameFamily : (a b : W.FamilyId) → Dec (a ≡ b)) where
  run : Reindex → Caches → Caches
  run ordinary before = before
  run (clean family) before = caches (clearAnalysis family before) (clearVectors family before)
    where
    clearAnalysis : W.FamilyId → Caches → W.FamilyId → AnalysisCache.Cache
    clearAnalysis target previous selected with sameFamily target selected
    ... | yes _ = AnalysisCache.empty
    ... | no _ = Caches.analyses previous selected
    clearVectors : W.FamilyId → Caches → W.FamilyId → VectorCache.Cache
    clearVectors target previous selected with sameFamily target selected
    ... | yes _ = VectorCache.empty
    ... | no _ = Caches.vectors previous selected

  ordinaryKeepsWork : ∀ before → run ordinary before ≡ before
  ordinaryKeepsWork before = refl

  cleanKeepsOtherAnalysis : ∀ family selected before → ¬ (family ≡ selected) →
    Caches.analyses (run (clean family) before) selected ≡ Caches.analyses before selected
  cleanKeepsOtherAnalysis family selected before different with sameFamily family selected
  ... | yes same = ⊥-elim (different same)
  ... | no _ = refl

  cleanKeepsOtherVectors : ∀ family selected before → ¬ (family ≡ selected) →
    Caches.vectors (run (clean family) before) selected ≡ Caches.vectors before selected
  cleanKeepsOtherVectors family selected before different with sameFamily family selected
  ... | yes same = ⊥-elim (different same)
  ... | no _ = refl
