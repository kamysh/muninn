# How Muninn decides whether two artifacts are the same

Reuse saves parsing, chunking, and embedding work. Reusing an artifact under
the wrong inputs can produce a result from the wrong bytes, location, or
embedding profile. These comparisons give callers either evidence that the
modeled inputs are equal or evidence that equality is impossible.

See [worktree identity and views](Worktree.lagda.md) and the
[file-version preparation code](../../crates/core/src/worktrees/prepared.rs).

```agda
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

```

## Compare the actual inputs to analysis

The bytes must match in order. The analysis also depends on the language,
parser, grammar, extractor, chunker, normalization, analysis configuration,
and chunk byte limit. A change to any of these can change the meaning of
an otherwise identical file. A digest can narrow the database lookup. The
equality decision itself compares the analysis inputs.

```agda
byteList? : ∀ (first second : List (Fin 256)) → Dec (first ≡ second)
byteList? = list? byte?

AnalysisMeaning? : ∀ (first second : W.AnalysisMeaning) → Dec (first ≡ second)
AnalysisMeaning? first second = map′
  (λ { (refl , refl , refl , refl , refl , refl , refl , refl , refl) → refl })
  (λ { refl → refl , refl , refl , refl , refl , refl , refl , refl , refl })
  ((byteList? (W.AnalysisMeaning.bytes first) (W.AnalysisMeaning.bytes second)) ×-dec (string? (W.AnalysisMeaning.parserVersion first) (W.AnalysisMeaning.parserVersion second)) ×-dec (string? (W.AnalysisMeaning.grammarVersion first) (W.AnalysisMeaning.grammarVersion second)) ×-dec (string? (W.AnalysisMeaning.extractorVersion first) (W.AnalysisMeaning.extractorVersion second)) ×-dec (string? (W.AnalysisMeaning.chunkerVersion first) (W.AnalysisMeaning.chunkerVersion second)) ×-dec (string? (W.AnalysisMeaning.normalizationVersion first) (W.AnalysisMeaning.normalizationVersion second)) ×-dec (string? (W.AnalysisMeaning.analysisConfig first) (W.AnalysisMeaning.analysisConfig second)) ×-dec (string? (W.AnalysisMeaning.language first) (W.AnalysisMeaning.language second)) ×-dec (nat? (W.AnalysisMeaning.maxChunkBytes first) (W.AnalysisMeaning.maxChunkBytes second)))

```

## Keep separate source occurrences separate

A chunk's modeled position is a half-open byte range. For example, a span
from byte 10 to byte 14 contains bytes 10 through 13. Identical text at
another offset is a different occurrence. Comparing both endpoints preserves
that distinction when a search reports where the text came from.

```agda
ByteSpan? : ∀ (first second : W.ByteSpan) → Dec (first ≡ second)
ByteSpan? first second = map′
  (λ { (refl , refl) → refl })
  (λ { refl → refl , refl })
  ((nat? (W.ByteSpan.start first) (W.ByteSpan.start second)) ×-dec (nat? (W.ByteSpan.end first) (W.ByteSpan.end second)))

```

## Match the whole embedding profile

The provider, model, configuration, profile revision, normalization, task,
and dimension all contribute to the profile. Two models can return vectors
of equal length while putting the same text in different places in their
vector spaces. The comparison checks the entire profile, and the worktree
model separately requires equal normalized input bytes for vector reuse.

```agda
EmbeddingKey? : ∀ (first second : W.EmbeddingKey) → Dec (first ≡ second)
EmbeddingKey? first second = map′
  (λ { (refl , refl , refl , refl , refl , refl , refl) → refl })
  (λ { refl → refl , refl , refl , refl , refl , refl , refl })
  ((string? (W.EmbeddingKey.backend first) (W.EmbeddingKey.backend second)) ×-dec (string? (W.EmbeddingKey.model first) (W.EmbeddingKey.model second)) ×-dec (string? (W.EmbeddingKey.configuration first) (W.EmbeddingKey.configuration second)) ×-dec (string? (W.EmbeddingKey.profileRevision first) (W.EmbeddingKey.profileRevision second)) ×-dec (string? (W.EmbeddingKey.normalizationVersion first) (W.EmbeddingKey.normalizationVersion second)) ×-dec (string? (W.EmbeddingKey.task first) (W.EmbeddingKey.task second)) ×-dec (nat? (W.EmbeddingKey.dimension first) (W.EmbeddingKey.dimension second)))

```

## Compare ownership and checkout identity explicitly

A family ID identifies the shared ownership boundary. A checkout ID identifies
one published view within that boundary. The 1.4.0 publication proofs use
checkout equality to update one slot and prove that the others stay intact.
A path can move or be reused by a replacement checkout, so these tests
compare the stored UUID values.

```agda
FamilyId? : ∀ (first second : W.FamilyId) → Dec (first ≡ second)
FamilyId? first second = map′ (λ { refl → refl }) (λ { refl → refl })
  (string? (T.UUID.value (W.FamilyId.value first)) (T.UUID.value (W.FamilyId.value second)))

CheckoutId? : ∀ (first second : W.CheckoutId) → Dec (first ≡ second)
CheckoutId? first second = map′ (λ { refl → refl }) (λ { refl → refl })
  (string? (T.UUID.value (W.CheckoutId.value first)) (T.UUID.value (W.CheckoutId.value second)))
```
