{-# OPTIONS --safe #-}
-- Muninn/Float.agda
-- Float support used throughout the specification.
-- Uses Agda's built-in IEEE 754 Float primitives directly so the module
-- is compatible with --safe mode.
--
-- Agda primitives here are IEEE 754 binary64. Stored vectors are binary32;
-- RetrievalNumerics.Stored32 requires exact widening of their encoded values.
-- Retrieval scores are calculated in binary64 against those stored values.
-- A wider Float alone is not evidence that a value is valid for storage.
module Muninn.Float where

open import Data.Nat using (ℕ)
open import Agda.Builtin.Float public using (Float)
open import Agda.Builtin.Float using (primFloatPlus; primFloatTimes; primFloatDiv; primNatToFloat)

_+F_ : Float → Float → Float
_+F_ = primFloatPlus

_*F_ : Float → Float → Float
_*F_ = primFloatTimes

_/F_ : Float → Float → Float
_/F_ = primFloatDiv

fromℕF : ℕ → Float
fromℕF = primNatToFloat

infixl 6 _+F_
infixl 7 _*F_ _/F_