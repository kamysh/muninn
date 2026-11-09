{-# OPTIONS --safe #-}
-- First occurrence of each exact byte span wins; source payloads are preserved.
module Muninn.CanonicalChunks where

import Muninn.Worktree as W
import Muninn.Types as T
open import Data.String using (String)
import Muninn.ArtifactIdentity as Identity
open import Data.List using (List; []; _∷_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.All as All
open All using (All; []; _∷_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (_<_; _≤_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans)

UniqueSpans : List W.AnalyzedChunk → Set
UniqueSpans [] = ⊤
UniqueSpans (first ∷ rest) = All (λ next → W.AnalyzedChunk.span first ≢ W.AnalyzedChunk.span next) rest × UniqueSpans rest

dropSpan : W.ByteSpan → List W.AnalyzedChunk → List W.AnalyzedChunk
dropSpan span [] = []
dropSpan span (first ∷ rest) with Identity.ByteSpan? span (W.AnalyzedChunk.span first)
... | yes same = dropSpan span rest
... | no different = first ∷ dropSpan span rest

dropSubset : ∀ span chunks chunk → chunk ∈ dropSpan span chunks → chunk ∈ chunks
dropSubset span [] chunk ()
dropSubset span (first ∷ rest) chunk present with Identity.ByteSpan? span (W.AnalyzedChunk.span first)
... | yes same = there (dropSubset span rest chunk present)
... | no different with present
...   | here equal = here equal
...   | there later = there (dropSubset span rest chunk later)

dropPreserves : ∀ span chunks chunk → span ≢ W.AnalyzedChunk.span chunk → chunk ∈ chunks → chunk ∈ dropSpan span chunks
dropPreserves span (first ∷ rest) .first different (here refl) with Identity.ByteSpan? span (W.AnalyzedChunk.span first)
... | yes same = ⊥-elim (different same)
... | no distinct = here refl
dropPreserves span (first ∷ rest) chunk different (there present) with Identity.ByteSpan? span (W.AnalyzedChunk.span first)
... | yes same = dropPreserves span rest chunk different present
... | no distinct = there (dropPreserves span rest chunk different present)

dropDifferent : ∀ span chunks → All (λ chunk → span ≢ W.AnalyzedChunk.span chunk) (dropSpan span chunks)
dropDifferent span [] = []
dropDifferent span (first ∷ rest) with Identity.ByteSpan? span (W.AnalyzedChunk.span first)
... | yes same = dropDifferent span rest
... | no different = different ∷ dropDifferent span rest

dropUnique : ∀ span chunks → UniqueSpans chunks → UniqueSpans (dropSpan span chunks)
dropUnique span [] unique = tt
dropUnique span (first ∷ rest) (separate , unique) with Identity.ByteSpan? span (W.AnalyzedChunk.span first)
... | yes same = dropUnique span rest unique
... | no different = All.tabulate (λ {chunk} present → All.lookup separate (dropSubset span rest chunk present)) , dropUnique span rest unique

canonical : List W.AnalyzedChunk → List W.AnalyzedChunk
canonical [] = []
canonical (first ∷ rest) = first ∷ dropSpan (W.AnalyzedChunk.span first) (canonical rest)

unique : ∀ chunks → UniqueSpans (canonical chunks)
unique [] = tt
unique (first ∷ rest) = dropDifferent (W.AnalyzedChunk.span first) (canonical rest) ,
  dropUnique (W.AnalyzedChunk.span first) (canonical rest) (unique rest)

subset : ∀ chunks chunk → chunk ∈ canonical chunks → chunk ∈ chunks
subset (first ∷ rest) .first (here refl) = here refl
subset (first ∷ rest) chunk (there present) = there (subset rest chunk
  (dropSubset (W.AnalyzedChunk.span first) (canonical rest) chunk present))

completeSpan : ∀ chunks chunk → chunk ∈ chunks →
  Σ W.AnalyzedChunk (λ kept → kept ∈ canonical chunks × W.AnalyzedChunk.span kept ≡ W.AnalyzedChunk.span chunk)
completeSpan (first ∷ rest) .first (here refl) = first , here refl , refl
completeSpan (first ∷ rest) chunk (there present) with completeSpan rest chunk present
... | kept , found , same with Identity.ByteSpan? (W.AnalyzedChunk.span first) (W.AnalyzedChunk.span kept)
...   | yes equal = first , here refl , trans equal same
...   | no different = kept , there (dropPreserves (W.AnalyzedChunk.span first) (canonical rest) kept different found) , same

-- Any independently specified payload/bounds law survives canonicalization.
preserves : ∀ (Valid : W.AnalyzedChunk → Set) chunks → All Valid chunks → All Valid (canonical chunks)
preserves Valid chunks valid = All.tabulate (λ {chunk} present → All.lookup valid (subset chunks chunk present))

ValidSpan : W.AnalysisMeaning → W.AnalyzedChunk → Set
ValidSpan key chunk = W.ByteSpan.start (W.AnalyzedChunk.span chunk) < W.ByteSpan.end (W.AnalyzedChunk.span chunk) ×
  W.ByteSpan.end (W.AnalyzedChunk.span chunk) ≤ length (W.AnalysisMeaning.bytes key)

ValidChunk : W.AnalysisMeaning → W.AnalyzedChunk → Set
ValidChunk key chunk = ValidSpan key chunk ×
  (W.AnalyzedChunk.content chunk ≢ "" ×
    T.LineRange.start (W.AnalyzedChunk.range chunk) ≤ T.LineRange.end (W.AnalyzedChunk.range chunk))
