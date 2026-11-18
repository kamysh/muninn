{-# OPTIONS --safe #-}
-- A hash selects candidates; exact semantic input determines reuse.
module Muninn.IncrementalIdentity where

import Muninn.ReusePolicy as Reuse
import Muninn.Worktree as Worktree
open import Data.Nat using (ℕ; _≟_)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)

data Decision (saved current : Reuse.AnalysisInput) : Set where
  reuse : saved ≡ current → Decision saved current
  calculate : Decision saved current

-- The digest is deliberately arbitrary: the proof does not assume collision
-- resistance or use timestamps, device IDs, inode numbers, or file size as
-- semantic identity. Parser and grammar settings belong to AnalysisInput.
choose : (Reuse.AnalysisInput → ℕ) → (saved current : Reuse.AnalysisInput) → Decision saved current
choose digest saved current with digest saved ≟ digest current
... | no _ = calculate
... | yes _ with Reuse.analysisInput? saved current
...   | yes same = reuse same
...   | no _ = calculate

sameInputReused : ∀ digest input → choose digest input input ≡ reuse refl
sameInputReused digest input with digest input ≟ digest input
... | no different = ⊥-elim (different refl)
... | yes _ with Reuse.analysisInput? input input
...   | no different = ⊥-elim (different refl)
...   | yes refl = refl

-- Even when a digest collides, a different family, bytes, or analysis setting
-- cannot yield a reuse decision.
differentInputCalculated : ∀ digest saved current → saved ≢ current →
  choose digest saved current ≡ calculate
differentInputCalculated digest saved current distinct with digest saved ≟ digest current
... | no _ = refl
... | yes _ with Reuse.analysisInput? saved current
...   | yes same = ⊥-elim (distinct same)
...   | no _ = refl

reusedBytesEqual : ∀ {saved current} → saved ≡ current →
  Worktree.AnalysisMeaning.bytes (Reuse.AnalysisInput.meaning saved) ≡
  Worktree.AnalysisMeaning.bytes (Reuse.AnalysisInput.meaning current)
reusedBytesEqual same = cong (λ input → Worktree.AnalysisMeaning.bytes (Reuse.AnalysisInput.meaning input)) same
