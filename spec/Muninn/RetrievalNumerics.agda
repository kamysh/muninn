{-# OPTIONS --safe #-}
-- Stored binary32 values are widened exactly; scoring itself is binary64.
module Muninn.RetrievalNumerics where
import Muninn.VectorData as V
open import Muninn.Float using (Float; fromℕF; _+F_; _*F_; _/F_)
open import Agda.Builtin.Float using (primFloatNegate; primFloatMinus; primFloatSqrt; primFloatLess; primFloatIsNaN; primFloatIsInfinite; primFloatToRatio)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_; _<_; _≤_; _≤?_)
open import Data.Integer using (+_)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- Exponent 255 is deliberately absent: NaN/infinity are not stored vectors.
record Binary32 : Set where
  field negative : Bool
        exponent fraction : ℕ
        finiteExponent : exponent < 255
        fractionWidth : fraction < 8388608

magnitude : Binary32 → Float
magnitude word with Binary32.exponent word
... | zero = fromℕF (Binary32.fraction word) /F fromℕF (2 ^ 149)
... | suc e with suc e ≤? 150
...   | yes small = fromℕF (8388608 + Binary32.fraction word) /F fromℕF (2 ^ (150 ∸ suc e))
...   | no large = fromℕF (8388608 + Binary32.fraction word) *F fromℕF (2 ^ (suc e ∸ 150))
widen : Binary32 → Float
widen word with Binary32.negative word
... | false = magnitude word
... | true = primFloatNegate (magnitude word)

record Stored32 (values : List Float) : Set where
  field words : List Binary32
        exactWidening : map widen words ≡ values

dot64 : List Float → List Float → Float
dot64 [] ys = fromℕF 0
dot64 (x ∷ xs) [] = fromℕF 0
dot64 (x ∷ xs) (y ∷ ys) = (x *F y) +F dot64 xs ys
cosine64 : List Float → List Float → Float
cosine64 xs ys = dot64 xs ys /F (primFloatSqrt (dot64 xs xs) *F primFloatSqrt (dot64 ys ys))

-- Only final cosine roundoff is clamped. No arbitrary score may replace it.
clampCosine : Float → Float
clampCosine value with primFloatLess (fromℕF 1) value
... | true = fromℕF 1
... | false with primFloatLess value (primFloatNegate (fromℕF 1))
...   | true = primFloatNegate (fromℕF 1)
...   | false = value

-- The exact rational image of the *computed* binary64 score supplies ordering.
-- This avoids asserting algebraic laws that rounded Float operations lack.
record Rank : Set where
  field value : Float
        numerator denominator : ℕ
        notNaN : primFloatIsNaN value ≡ false
        notInfinite : primFloatIsInfinite value ≡ false
        positive : 0 < numerator
        denominatorPositive : 0 < denominator
        exactRatio : primFloatToRatio value ≡ (+ numerator , + denominator)

record Cosine (query stored : List Float) : Set where
  field rank : Rank
        calculated : Rank.value rank ≡ clampCosine (cosine64 query stored)
        bounded : Rank.numerator rank ≤ Rank.denominator rank
        rawFinite : V.finite (cosine64 query stored ∷ []) ≡ true

-- A nonpositive result is a legitimate non-match, not missing numerical work.
-- Exhaustive evaluation must classify every usable vector by this fixed rule.
data Evaluation (query stored : List Float) : Set where
  positive : Cosine query stored → Evaluation query stored
  nonpositive : primFloatLess (fromℕF 0) (clampCosine (cosine64 query stored)) ≡ false →
    primFloatIsNaN (cosine64 query stored) ≡ false →
    primFloatIsInfinite (cosine64 query stored) ≡ false → Evaluation query stored

before : Rank → Rank → Bool
before first second with (Rank.numerator second * Rank.denominator first) ≤? (Rank.numerator first * Rank.denominator second)
... | yes _ = true
... | no _ = false
