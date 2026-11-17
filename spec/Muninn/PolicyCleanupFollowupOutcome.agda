{-# OPTIONS --safe #-}
-- A covering follow-up's checked outcome also finishes the parent's captured work.
module Muninn.PolicyCleanupFollowupOutcome where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.PolicyRuleAdmission as Admission
import Muninn.CleanupLoop as Loop
open import Data.Bool using (Bool)
open import Data.String using (String)
open import Data.List using (List)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)

module Model where
  module Outcome = E.Model
  module Family (selection : E.Rule) (parentAccepted : O.World)
    (parentIntent : Outcome.Intent selection parentAccepted)
    (childAccepted : O.World) (childIntent : Outcome.Intent selection childAccepted) where
    module Parent = Loop.Model.Run selection parentAccepted parentIntent
    module Child = Loop.Model.Run selection childAccepted childIntent

    parentComplete : ∀ world → Child.Covered world → Child.Final.NoPending world → Parent.Final.NoPending world
    parentComplete world covered complete key (value , found , captured , owned , indexed , remaining) =
      complete key (value , found , covered key value found owned , owned , indexed , remaining)

    parentQuiet : ∀ world → Child.Covered world → Child.Final.NoPending world → Parent.Pass.NoEdit world
    parentQuiet world covered complete key (inj₁ (value , found , captured , owned , indexed , unneeded , rest)) =
      parentComplete world covered complete key (value , found , captured , owned , indexed , inj₁ unneeded)
    parentQuiet world covered complete key (inj₂ (value , found , captured , owned , indexed , needed , unprotected , changed)) =
      parentComplete world covered complete key (value , found , captured , owned , indexed , inj₂ (needed , changed))
