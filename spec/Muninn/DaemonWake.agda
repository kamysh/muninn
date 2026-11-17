{-# OPTIONS --safe #-}
-- Daemon notifications prompt a scan; polling supplies the same scan when
-- no notification arrives. This is finite scheduling, not a service loop.
module Muninn.DaemonWake where

import Muninn.Catalog as Catalog
import Muninn.CatalogInputs as Input
open import Data.Nat using (ℕ; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

pollSeconds : ℕ
pollSeconds = 60

data Listener : Set where listening pollingOnly : Listener

data Event : Listener → Set where
  notification : Event listening
  listenerClosed : Event listening
  poll : ∀ {listener} (elapsed : ℕ) → pollSeconds ≤ elapsed → Event listener

data Next : Set where
  wait : Listener → Next
  scan : Listener → Catalog.Request → Next

-- The fleet input names the registered families the scan covers.
step : ∀ {listener} → Input.JobInput Input.fleetScan → Event listener → Next
step input notification = scan listening (Catalog.background Input.fleetScan input)
step input listenerClosed = wait pollingOnly
step {listener} input (poll elapsed due) = scan listener (Catalog.background Input.fleetScan input)

notificationScans : ∀ input → step input notification ≡ scan listening (Catalog.background Input.fleetScan input)
notificationScans input = refl

fallbackScans : ∀ listener input elapsed due →
  step {listener} input (poll elapsed due) ≡ scan listener (Catalog.background Input.fleetScan input)
fallbackScans listener input elapsed due = refl

closedWaitsForPoll : ∀ input → step input listenerClosed ≡ wait pollingOnly
closedWaitsForPoll input = refl
