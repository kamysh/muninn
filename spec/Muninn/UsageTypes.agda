{-# OPTIONS --safe #-}
-- Logical fields of one recorded MCP tool call.
module Muninn.UsageTypes where

open import Data.String using (String)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ)
open import Data.Integer using (ℤ)

record Usage : Set where
  constructor usage
  field tool : String
        repositoryPath : Maybe String
        durationMilliseconds : Maybe ℤ
        resultCount : Maybe ℤ
        recordedAt : ℕ
