{-# OPTIONS --safe #-}
-- Muninn/Float.agda
-- Float support used throughout the specification.
-- Uses Agda's built-in IEEE 754 Float primitives directly so the module
-- is compatible with --safe mode.
--
-- Implementation note: in the Rust implementation Float corresponds to
-- f32 (IEEE 754 single-precision, 32-bit), not the 64-bit double that
-- Agda's built-in Float provides.  The spec uses Float as an
-- over-approximation.  Precision loss is intentional: pgvector and the
-- embedding libraries (fastembed, Voyage, OpenAI) all operate on f32.
module Muninn.Float where

open import Data.Nat using (ℕ)
open import Agda.Builtin.Float public using (Float)
open import Agda.Builtin.Float using (primFloatPlus; primFloatDiv; primNatToFloat)

_+F_ : Float → Float → Float
_+F_ = primFloatPlus

_/F_ : Float → Float → Float
_/F_ = primFloatDiv

fromℕF : ℕ → Float
fromℕF = primNatToFloat

infixl 6 _+F_
infixl 7 _/F_