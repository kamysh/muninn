{-# OPTIONS --safe #-}
-- One interruption relation for operations over fixed effect semantics.
module Muninn.GeneralRecovery where

open import Agda.Primitive using (Level)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec)
import Muninn.Database

-- Atomic is supplied by the shared interpreter, not by an individual script.
-- Effects may include observations as well as committed storage transactions.
module Protocol {effectLevel : Level} (World : Set) (Effect : Set effectLevel)
  (Reply : Effect → Set)
  (Atomic : World → (effect : Effect) → Reply effect → World → Set) where

  data Script (Result : Set) : Set effectLevel where
    done : Result → Script Result
    call : (effect : Effect) → (Reply effect → Script Result) → Script Result

  data Prefix {Result : Set} : Script Result → World → Script Result → World → Set effectLevel where
    stop : ∀ {script world} → Prefix script world script world
    advanced : ∀ {effect next before reply after residual final} →
      Atomic before effect reply after → Prefix (next reply) after residual final →
      Prefix (call effect next) before residual final

  Interrupted : ∀ {Result} → Script Result → World → World → Set effectLevel
  Interrupted script before after = Σ (Script _) (λ residual → Prefix script before residual after)

  Completed : ∀ {Result} → Script Result → World → Result → World → Set effectLevel
  Completed script before result after = Prefix script before (done result) after

  -- Goal, frame and readiness are independently fixed by the operation catalog.
  record Recoverable (Input Result : Set)
    (Goal Frame : Input → World → World → Set) (Ready : Input → World → Set) : Set effectLevel where
    field
      script : Input → Script Result
      preserves : ∀ input before after →
        Interrupted (script input) before after → Frame input before after
      converges : ∀ input before interrupted final result →
        Interrupted (script input) before interrupted →
        Completed (script input) interrupted result final → Goal input before final
      progresses : ∀ input before → Ready input before →
        Σ Result (λ result → Σ World (λ final → Completed (script input) before result final))

  firstBoundary : ∀ {Result : Set} effect (next : Reply effect → Script Result) before after →
    Interrupted (call effect next) before after →
    (after ≡ before) ⊎ Σ (Reply effect) (λ reply → Σ World (λ middle →
      Atomic before effect reply middle × Interrupted (next reply) middle after))
  firstBoundary effect next before after (residual , stop) = inj₁ refl
  firstBoundary effect next before after (residual , advanced committed rest) =
    inj₂ (_ , _ , committed , residual , rest)

  -- A committed effect is a retry boundary even if its reply is not delivered.
  committedBoundary : ∀ {Result : Set} {effect} {next : Reply effect → Script Result}
    {before reply after} → Atomic before effect reply after → Interrupted (call effect next) before after
  committedBoundary {next = next} {reply = reply} committed = next reply , advanced committed stop

  composePrefixes : ∀ {Result : Set} {start middle final : Script Result} {before between after} →
    Prefix start before middle between → Prefix middle between final after → Prefix start before final after
  composePrefixes stop second = second
  composePrefixes (advanced committed first) second = advanced committed (composePrefixes first second)

  completedReturnKeepsWorld : ∀ {Result : Set} (result : Result) before observed after →
    Completed (done result) before observed after → after ≡ before
  completedReturnKeepsWorld result before observed after stop = refl

  completedIsBoundary : ∀ {Result : Set} {script : Script Result} {before result after} →
    Completed script before result after → Interrupted script before after
  completedIsBoundary {result = result} run = done result , run

-- The database instance fixes atomic commit and rollback to the shared database
-- semantics. The dispatcher must use this instance for database effects.
module DatabaseProtocol (Key Value : Set) (same : (a b : Key) → Dec (a ≡ b)) where
  module DB = Muninn.Database.Store Key Value same

  data Effect : Set₁ where
    transaction : ∀ {Answer : Set} → DB.Transaction Answer → Effect

  ReplyOf : Effect → Set
  ReplyOf (transaction {Answer} transactionBody) = Answer

  Atomic : DB.Rows → (effect : Effect) → ReplyOf effect → DB.Rows → Set
  Atomic before (transaction transactionBody) reply after = DB.execute transactionBody before ≡ (reply , after)

  module Shared = Protocol DB.Rows Effect ReplyOf Atomic
