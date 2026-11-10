{-# OPTIONS --safe #-}
-- Nonnegative ranking scores permit zero without treating it as exclusion.
module Muninn.HybridNumbers where
import Muninn.CatalogInputs as I
open import Muninn.Float using (Float; fromℕF; _+F_; _*F_; _/F_)
open import Agda.Builtin.Float using (primFloatIsNaN; primFloatIsInfinite; primFloatLess; primFloatToRatio)
open import Data.Nat using (ℕ; _<_; _≤_; _⊓_; _*_; _+_)
open import Data.Integer using (+_)
open import Data.Bool using (false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

record Score : Set where
  field value : Float
        numerator denominator : ℕ
        notNaN : primFloatIsNaN value ≡ false
        notInfinite : primFloatIsInfinite value ≡ false
        nonnegative : primFloatLess value (fromℕF 0) ≡ false
        denominatorPositive : 0 < denominator
        exactRatio : primFloatToRatio value ≡ (+ numerator , + denominator)
record Weight : Set where
  field score : Score
        atMostOne : primFloatLess (fromℕF 1) (Score.value score) ≡ false

defaultMultiplier : Float
defaultMultiplier = fromℕF 3 /F fromℕF 10
requestedWeight : I.RankingOverrides → Float
requestedWeight overrides with I.RankingOverrides.vendorWeight overrides
... | nothing = defaultMultiplier
... | just value = value

-- Admission must supply these proofs for the *actual* requested/default values.
-- Invalid input stays in the existing corrective dialogue, not another score.
record Overrides (input : I.RankingOverrides) : Set where
  field multiplier : Weight
        actualMultiplier : Score.value (Weight.score multiplier) ≡ requestedWeight input

budget : ℕ → ℕ
budget pageSize = (10 * pageSize) ⊓ 1000
contribution : Maybe ℕ → Float
contribution nothing = fromℕF 0
contribution (just rank) = fromℕF 1 /F (fromℕF 60 +F fromℕF rank)
fused : Maybe ℕ → Maybe ℕ → Float
fused text semantic = contribution text +F contribution semantic
