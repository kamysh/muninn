{-# OPTIONS --safe #-}
-- Foreground interruption pauses the current accepted work, rather than
-- creating a separate index-removal or resume command.
module Muninn.CLIInterrupt where

import Muninn.CatalogInputs as I
import Muninn.IndexWorkControl as Control
import Data.Maybe
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module Model (Progress Results Temporary : Set) where
  module Work = Control.Model Progress Results Temporary

  -- The interrupt control input selects the pause transition of the
  -- accepted-work state machine. Binding the operation id to the family
  -- holding that work remains the dispatcher's obligation.
  command : I.ControlInput I.interrupt → Work.State → Work.State
  command id = Work.interrupt

  isPause : ∀ id before → command id before ≡ Work.pause before
  isPause id before = refl

  preservesProgress : ∀ id authorized phase progress results temporary →
    Work.State.current (command id (Work.state authorized (Data.Maybe.just (Work.work phase progress)) results temporary)) ≡
      Data.Maybe.just (Work.work Work.paused progress)
  preservesProgress id authorized phase progress results temporary =
    Work.pausePreservesProgress authorized phase progress results temporary

  keepsAuthorization : ∀ id before → Work.State.authorized (command id before) ≡ Work.State.authorized before
  keepsAuthorization id = Work.pauseKeepsAuthorization
