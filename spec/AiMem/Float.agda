-- AiMem/Float.agda
-- Postulated Float support used throughout the specification.
-- Agda's built-in Float does not expose ordered arithmetic conveniently,
-- so we postulate the operations we need.  These are realised by IEEE 754
-- doubles in every concrete backend.
module AiMem.Float where

open import Data.Nat using (ℕ)

postulate
  Float  : Set
  _+F_   : Float → Float → Float
  _/F_   : Float → Float → Float
  fromℕF : ℕ → Float

infixl 6 _+F_
infixl 7 _/F_