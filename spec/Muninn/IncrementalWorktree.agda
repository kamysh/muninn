{-# OPTIONS --safe #-}
-- Work proportional to reported paths, conditional on complete observations.
module Muninn.IncrementalWorktree where

import Muninn.IncrementalObservation as Observation
import Muninn.IncrementalStructure as Structure
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Relation.Nullary using (yes; no; ¬_)
open import Data.Empty using (⊥-elim)

countWhere : (Observation.Path → Bool) → List Observation.Path → ℕ
countWhere predicate [] = zero
countWhere predicate (path ∷ paths) with predicate path
... | true = suc (countWhere predicate paths)
... | false = countWhere predicate paths

readCount : ∀ {before after} → Observation.Observation before after → List Observation.Path → ℕ
readCount observation = countWhere (Observation.needsRead observation)

-- When metadata contributes no additional hints, the exact number of reads
-- among selected paths is the number reported by the complete observer.
-- The observer's coverage remains an external correctness obligation.
readsMatchReported : ∀ {before after} changed (coverage : Observation.Covers before after changed)
  paths → All (λ path → Observation.metadataHint (before path) (after path) ≡ false) paths →
  readCount (Observation.complete changed coverage) paths ≡ countWhere changed paths
readsMatchReported changed coverage [] [] = refl
readsMatchReported changed coverage (path ∷ paths) (hint ∷ hints)
  rewrite hint with changed path
... | true = cong suc (readsMatchReported changed coverage paths hints)
... | false = readsMatchReported changed coverage paths hints

-- Two symbol lists are equivalent for one retained call if all symbols that
-- match its target name have the same membership. Unrelated symbols may have
-- been added or removed; this does not require retaining an entire graph.
record SameTargets (candidate : Structure.Candidate)
  (before after : List Structure.Symbol) : Set where
  field
    forward : ∀ target → Structure.Match candidate target → target ∈ before → target ∈ after
    backward : ∀ target → Structure.Match candidate target → target ∈ after → target ∈ before

unaffectedResolution : ∀ {candidate before after target} →
  SameTargets candidate before after → Structure.Resolves candidate before target →
  Structure.Resolves candidate after target
unaffectedResolution same (Structure.local present matching localPath) =
  Structure.local (SameTargets.forward same _ matching present) matching localPath
unaffectedResolution same (Structure.external present matching outside noLocal) =
  Structure.external (SameTargets.forward same _ matching present) matching outside
    (λ target presentAfter targetMatch localPath →
      noLocal target (SameTargets.backward same target targetMatch presentAfter) targetMatch localPath)

-- A symbol delta identifies names whose membership may have changed. The
-- adapter must produce an accurate delta; unchanged names retain membership.
record NameDelta (before after : List Structure.Symbol) (changed : ℕ → Bool) : Set where
  field
    retained : ∀ target → changed (Structure.Symbol.name target) ≡ false → target ∈ before → target ∈ after
    notAdded : ∀ target → changed (Structure.Symbol.name target) ≡ false → target ∈ after → target ∈ before

-- A retained call whose target name is outside the symbol delta has the same
-- resolution. This justifies updating callers for affected names only.
unaffectedNamePreservesResolution : ∀ {candidate before after target} changed →
  NameDelta before after changed → changed (Structure.Candidate.targetName candidate) ≡ false →
  Structure.Resolves candidate before target → Structure.Resolves candidate after target
unaffectedNamePreservesResolution {candidate} {before} {after} changed delta unchanged =
  unaffectedResolution (record { forward = forward ; backward = backward })
  where
  nameUnchanged : ∀ target → Structure.Match candidate target → changed (Structure.Symbol.name target) ≡ false
  nameUnchanged target matching rewrite Structure.Match.sameName matching = unchanged
  forward : ∀ target → Structure.Match candidate target → target ∈ before → target ∈ after
  forward target matching present =
    NameDelta.retained delta target (nameUnchanged target matching) present
  backward : ∀ target → Structure.Match candidate target → target ∈ after → target ∈ before
  backward target matching present =
    NameDelta.notAdded delta target (nameUnchanged target matching) present

differentSelfFalse : ∀ value → Observation.different value value ≡ false
differentSelfFalse value with value ≟ value
... | yes _ = refl
... | no unequal = ⊥-elim (unequal refl)

timestampSelfFalse : ∀ value → Observation.timestampChanged value value ≡ false
timestampSelfFalse zero = refl
timestampSelfFalse (suc value) = differentSelfFalse value

sameMetadataNoHint : ∀ metadata → Observation.metadataChanged metadata metadata ≡ false
sameMetadataNoHint (Observation.meta device inode size timestamp)
  rewrite differentSelfFalse device | differentSelfFalse inode | differentSelfFalse size |
          timestampSelfFalse timestamp = refl

-- Equal metadata can coincide with different bytes. In that case a provider
-- cannot soundly certify that no paths changed, regardless of the timestamp.
equalMetadataCannotCertifyUnchanged : ∀ {before after} path first second →
  before path ≡ Observation.present first → after path ≡ Observation.present second →
  Observation.File.metadata first ≡ Observation.File.metadata second →
  ¬ (Observation.File.bytes first ≡ Observation.File.bytes second) →
  Observation.metadataHint (Observation.present first) (Observation.present second) ≡ false ×
  ¬ Observation.Covers before after (λ _ → false)
equalMetadataCannotCertifyUnchanged path first second was now refl differentBytes =
  sameMetadataNoHint (Observation.File.metadata first) ,
  λ coverage → Observation.trueNotFalse
    (sym (Observation.changedBytesMustBeReported (λ _ → false) coverage path first second was now differentBytes))
