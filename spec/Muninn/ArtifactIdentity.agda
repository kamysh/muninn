{-# OPTIONS --safe #-}
-- Exact comparison of every semantic profile/span field.
module Muninn.ArtifactIdentity where

import Muninn.Worktree as W
import Muninn.Types as T
open import Data.List.Properties using () renaming (≡-dec to list?)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to byte?)
open import Data.List using (List)
open import Data.Nat using () renaming (_≟_ to nat?)
open import Data.String using () renaming (_≟_ to string?)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (map′; _×-dec_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

byteList? : ∀ (first second : List (Fin 256)) → Dec (first ≡ second)
byteList? = list? byte?

AnalysisMeaning? : ∀ (first second : W.AnalysisMeaning) → Dec (first ≡ second)
AnalysisMeaning? first second = map′
  (λ { (refl , refl , refl , refl , refl , refl , refl , refl , refl) → refl })
  (λ { refl → refl , refl , refl , refl , refl , refl , refl , refl , refl })
  ((byteList? (W.AnalysisMeaning.bytes first) (W.AnalysisMeaning.bytes second)) ×-dec (string? (W.AnalysisMeaning.parserVersion first) (W.AnalysisMeaning.parserVersion second)) ×-dec (string? (W.AnalysisMeaning.grammarVersion first) (W.AnalysisMeaning.grammarVersion second)) ×-dec (string? (W.AnalysisMeaning.extractorVersion first) (W.AnalysisMeaning.extractorVersion second)) ×-dec (string? (W.AnalysisMeaning.chunkerVersion first) (W.AnalysisMeaning.chunkerVersion second)) ×-dec (string? (W.AnalysisMeaning.normalizationVersion first) (W.AnalysisMeaning.normalizationVersion second)) ×-dec (string? (W.AnalysisMeaning.analysisConfig first) (W.AnalysisMeaning.analysisConfig second)) ×-dec (string? (W.AnalysisMeaning.language first) (W.AnalysisMeaning.language second)) ×-dec (nat? (W.AnalysisMeaning.maxChunkBytes first) (W.AnalysisMeaning.maxChunkBytes second)))

ByteSpan? : ∀ (first second : W.ByteSpan) → Dec (first ≡ second)
ByteSpan? first second = map′
  (λ { (refl , refl) → refl })
  (λ { refl → refl , refl })
  ((nat? (W.ByteSpan.start first) (W.ByteSpan.start second)) ×-dec (nat? (W.ByteSpan.end first) (W.ByteSpan.end second)))

EmbeddingKey? : ∀ (first second : W.EmbeddingKey) → Dec (first ≡ second)
EmbeddingKey? first second = map′
  (λ { (refl , refl , refl , refl , refl , refl , refl) → refl })
  (λ { refl → refl , refl , refl , refl , refl , refl , refl })
  ((string? (W.EmbeddingKey.backend first) (W.EmbeddingKey.backend second)) ×-dec (string? (W.EmbeddingKey.model first) (W.EmbeddingKey.model second)) ×-dec (string? (W.EmbeddingKey.configuration first) (W.EmbeddingKey.configuration second)) ×-dec (string? (W.EmbeddingKey.profileRevision first) (W.EmbeddingKey.profileRevision second)) ×-dec (string? (W.EmbeddingKey.normalizationVersion first) (W.EmbeddingKey.normalizationVersion second)) ×-dec (string? (W.EmbeddingKey.task first) (W.EmbeddingKey.task second)) ×-dec (nat? (W.EmbeddingKey.dimension first) (W.EmbeddingKey.dimension second)))

FamilyId? : ∀ (first second : W.FamilyId) → Dec (first ≡ second)
FamilyId? first second = map′ (λ { refl → refl }) (λ { refl → refl })
  (string? (T.UUID.value (W.FamilyId.value first)) (T.UUID.value (W.FamilyId.value second)))
