{-# OPTIONS --safe #-}
-- Foreground interruption pauses the current accepted work, rather than
-- creating a separate index-removal or resume command.
module Muninn.CLIInterrupt where

import Muninn.CatalogInputs as I
import Muninn.OwnedState as O
import Muninn.WorkControlStore as Control
import Muninn.WorkQueue as Queue
open import Data.Nat using (ℕ)
open import Data.Bool using (true)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_)

command : I.ControlInput I.interrupt → Control.Command
command id = Control.pauseCurrent id

module Family (family : ℕ) where
  module Work = Control.Family family

  retainsPausedWork : ∀ world key versions info target → O.Unique world →
    O.DB.lookup key world ≡ just (O.recordOf Work.owner (O.acceptedWork versions info)) → Work.selected target info ≡ true →
    O.DB.lookup key (Work.final (command target) world) ≡
      just (O.recordOf Work.owner (O.acceptedWork versions (Queue.move Queue.paused info)))
  retainsPausedWork = Work.pauseRetainsWork
