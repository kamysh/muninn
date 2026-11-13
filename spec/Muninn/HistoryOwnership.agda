{-# OPTIONS --safe #-}
-- Fixed semantic ownership of installation-wide history records.
module Muninn.HistoryOwnership where
import Muninn.OwnedState as O
import Muninn.RepositoryHistory as History
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; false)

owns : ℕ → O.Record → Bool
owns family (O.recordOf owner (O.usage item)) = History.mentions family (History.owners item)
owns family (O.recordOf owner (O.logFile item)) = History.mentions family (History.owners item)
owns family _ = false
