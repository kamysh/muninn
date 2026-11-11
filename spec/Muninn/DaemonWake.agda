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

step : ∀ {listener} → Input.OperationId → Event listener → Next
step id notification = scan listening (Catalog.background Input.fleetScan id)
step id listenerClosed = wait pollingOnly
step {listener} id (poll elapsed due) = scan listener (Catalog.background Input.fleetScan id)

notificationScans : ∀ id → step id notification ≡ scan listening (Catalog.background Input.fleetScan id)
notificationScans id = refl

fallbackScans : ∀ listener id elapsed due →
  step {listener} id (poll elapsed due) ≡ scan listener (Catalog.background Input.fleetScan id)
fallbackScans listener id elapsed due = refl

closedWaitsForPoll : ∀ id → step id listenerClosed ≡ wait pollingOnly
closedWaitsForPoll id = refl
