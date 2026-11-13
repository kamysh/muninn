{-# OPTIONS --safe #-}
-- An accepted remove or forget request remains active until its cleanup ends.
module Muninn.PendingRemoval where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.ReceiptTypes as Receipt
import Muninn.RequestIdentity as Identity
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary using (yes; no)

isRemoval : Identity.Meaning → Bool
isRemoval (Identity.mutation Identity.kUnregister input) = true
isRemoval (Identity.mutation Identity.kForget input) = true
isRemoval _ = false

activeFor : O.Owner → O.Record → Bool
activeFor owner (O.recordOf receiptOwner (O.receipt (Receipt.entry id (Receipt.active meaning names work))))
  with E.ownerEqual owner receiptOwner
... | yes _ = isRemoval meaning
... | no _ = false
activeFor owner _ = false

pending : O.Owner → O.World → Bool
pending owner = E.anyRow (λ key value → activeFor owner value)
