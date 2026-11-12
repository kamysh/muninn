{-# OPTIONS --safe #-}
-- Indexing controls change accepted work while preserving committed results.
module Muninn.IndexWorkControl where

open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module Model (Progress Results Temporary : Set) where
  data Phase : Set where
    running paused : Phase

  record Work : Set where
    constructor work
    field phase : Phase
          progress : Progress

  record State : Set where
    constructor state
    field authorized : Bool
          current : Maybe Work
          committed : Results
          temporary : Maybe Temporary

  -- Registration has no authorization and creates no indexing work.
  register : Results → State
  register results = state false nothing results nothing

  -- An explicit start both authorizes the family and accepts this work.
  start : Progress → State → State
  start progress (state authorized nothing results temporary) =
    state true (just (work running progress)) results temporary
  start progress (state authorized (just existing) results temporary) =
    state true (just existing) results temporary

  pause : State → State
  pause (state authorized nothing results temporary) = state authorized nothing results temporary
  pause (state authorized (just (work phase progress)) results temporary) =
    state authorized (just (work paused progress)) results temporary

  -- Foreground Ctrl-C pauses this request; it does not discard progress.
  interrupt : State → State
  interrupt = pause

  resume : State → State
  resume (state authorized nothing results temporary) = state authorized nothing results temporary
  resume (state false (just existing) results temporary) =
    state false (just existing) results temporary
  resume (state true (just (work phase progress)) results temporary) =
    state true (just (work running progress)) results temporary

  -- Only a running, authorized job can commit new results and progress.
  advance : Progress → Results → State → State
  advance nextProgress nextResults (state true (just (work running progress)) results temporary) =
    state true (just (work running nextProgress)) nextResults temporary
  advance nextProgress nextResults before = before

  -- A cancellation removes the work; committed output is not rolled back.
  -- Temporary effects are cleaned by the same operation before it completes.
  cancel : State → State
  cancel (state authorized current results temporary) = state authorized nothing results nothing

  cancelAndReport : State → State × Results
  cancelAndReport before = cancel before , State.committed before

  -- A disconnected MCP caller cannot revoke an accepted job.
  disconnect : State → State
  disconnect current = current

  registeredNeedsStart : ∀ results → State.authorized (register results) ≡ false
  registeredNeedsStart results = refl

  startAuthorizes : ∀ progress before → State.authorized (start progress before) ≡ true
  startAuthorizes progress (state authorized nothing results temporary) = refl
  startAuthorizes progress (state authorized (just existing) results temporary) = refl

  pausePreservesProgress : ∀ authorized phase progress results temporary →
    State.current (pause (state authorized (just (work phase progress)) results temporary)) ≡ just (work paused progress)
  pausePreservesProgress authorized phase progress results temporary = refl

  resumePreservesProgress : ∀ phase progress results temporary →
    State.current (resume (state true (just (work phase progress)) results temporary)) ≡ just (work running progress)
  resumePreservesProgress phase progress results temporary = refl

  pauseKeepsAuthorization : ∀ before → State.authorized (pause before) ≡ State.authorized before
  pauseKeepsAuthorization (state authorized nothing results temporary) = refl
  pauseKeepsAuthorization (state authorized (just (work phase progress)) results temporary) = refl

  cancelRemovesWork : ∀ before → State.current (cancel before) ≡ nothing
  cancelRemovesWork (state authorized current results temporary) = refl

  cancellationKeepsCommitted : ∀ before → State.committed (cancel before) ≡ State.committed before
  cancellationKeepsCommitted (state authorized current results temporary) = refl

  interruptionPauses : ∀ before → interrupt before ≡ pause before
  interruptionPauses before = refl

  unauthorizedCannotAdvance : ∀ nextProgress nextResults current results temporary →
    advance nextProgress nextResults (state false current results temporary) ≡ state false current results temporary
  unauthorizedCannotAdvance nextProgress nextResults current results temporary = refl

  cancelledCannotAdvance : ∀ nextProgress nextResults before →
    advance nextProgress nextResults (cancel before) ≡ cancel before
  cancelledCannotAdvance nextProgress nextResults (state false current results temporary) = refl
  cancelledCannotAdvance nextProgress nextResults (state true current results temporary) = refl

  pausedCannotAdvance : ∀ nextProgress nextResults authorized progress results temporary →
    advance nextProgress nextResults (state authorized (just (work paused progress)) results temporary) ≡
      state authorized (just (work paused progress)) results temporary
  pausedCannotAdvance nextProgress nextResults false progress results temporary = refl
  pausedCannotAdvance nextProgress nextResults true progress results temporary = refl

  cancellationReportsCommitted : ∀ before → proj₂ (cancelAndReport before) ≡ State.committed before
  cancellationReportsCommitted before = refl

  cancellationCleansTemporary : ∀ before → State.temporary (cancel before) ≡ nothing
  cancellationCleansTemporary (state authorized current results temporary) = refl

  disconnectDoesNotPreventProgress : ∀ nextProgress nextResults before →
    advance nextProgress nextResults (disconnect before) ≡ advance nextProgress nextResults before
  disconnectDoesNotPreventProgress nextProgress nextResults before = refl

  disconnectKeepsAcceptedWork : ∀ before → State.current (disconnect before) ≡ State.current before
  disconnectKeepsAcceptedWork before = refl
