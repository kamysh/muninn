{-# OPTIONS --safe #-}
-- One interruption semantics for all operations. A crash can lose the local
-- program position or acknowledgement at ANY transaction boundary. Tentative
-- statement prefixes never publish: Database.execute is the only atomic effect.
module Muninn.Recovery where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec)
import Muninn.Database

module Protocol (Key Value : Set) (equal : (a b : Key) → Dec (a ≡ b)) where
  module DB = Muninn.Database.Store Key Value equal
  open DB using (Rows; Transaction; execute)

  data Script (Result : Set) : Set₁ where
    done : Result → Script Result
    atomic : ∀ {Reply : Set} → Transaction Reply →
      (Reply → Script Result) → Script Result

  data Prefix {Result : Set} : Script Result → Rows → Script Result → Rows → Set₁ where
    stop : ∀ {script world} → Prefix script world script world
    committed : ∀ {Reply} {transaction : Transaction Reply} {next : Reply → Script Result}
      {world residual final} →
      Prefix (next (proj₁ (execute transaction world)))
             (proj₂ (execute transaction world)) residual final →
      Prefix (atomic transaction next) world residual final

  Interrupted : ∀ {Result} → Script Result → Rows → Rows → Set₁
  Interrupted script before after = Σ _ (λ residual → Prefix script before residual after)

  Completed : ∀ {Result} → Script Result → Rows → Result → Rows → Set₁
  Completed script before result after = Prefix script before (done result) after

  -- Goal is an interface PARAMETER, fixed by the independently specified
  -- catalog entry. It is deliberately not an operation-supplied record field.
  record Recoverable (Input Result : Set)
    (Goal Frame : Input → Rows → Rows → Set) : Set₂ where
    field
      script : Input → Rows → Script Result
      preserves : ∀ input before after →
        Interrupted (script input before) before after → Frame input before after
      converges : ∀ input before interrupted final result →
        Interrupted (script input before) before interrupted →
        Completed (script input interrupted) interrupted result final →
        Goal input before final
      terminates : ∀ input before → Σ Result (λ result → Σ Rows (λ final →
        Completed (script input before) before result final))

  firstAtomicBoundary : ∀ {Result Reply : Set} (transaction : Transaction Reply)
    (next : Reply → Script Result) before after →
    Interrupted (atomic transaction next) before after →
    (after ≡ before) ⊎ Σ (Script Result) (λ residual →
      Prefix (next (proj₁ (execute transaction before)))
        (proj₂ (execute transaction before)) residual after)
  firstAtomicBoundary transaction next before after (residual , stop) = inj₁ refl
  firstAtomicBoundary transaction next before after (residual , committed rest) = inj₂ (residual , rest)

  completedReturnPreservesWorld : ∀ {Result : Set} (result : Result) before observed after →
    Completed (done result) before observed after → after ≡ before
  completedReturnPreservesWorld result before observed after stop = refl

  composePrefixes : ∀ {Result : Set} {start middle final : Script Result} {before between after} →
    Prefix start before middle between → Prefix middle between final after → Prefix start before final after
  composePrefixes stop second = second
  composePrefixes (committed first) second = committed (composePrefixes first second)

  completedIsInterruptionBoundary : ∀ {Result : Set} {script : Script Result} {before result after} →
    Completed script before result after → Interrupted script before after
  completedIsInterruptionBoundary {result = result} run = done result , run
