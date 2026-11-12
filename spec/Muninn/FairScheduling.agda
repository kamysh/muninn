{-# OPTIONS --safe #-}
-- Interactive requests retain capacity; background jobs take fair turns.
module Muninn.FairScheduling where
import Muninn.IndexWorkControl as Control
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; _≤?_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Maybe using (Maybe; just; nothing)
import Relation.Nullary
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; sym)

-- A one-slot installation yields background work when interaction arrives.
-- For larger installations both the background limit and the reservation are
-- positive and configurable; zero extra reserved slots means the default one.
data Capacity : Set where
  single : Capacity
  shared : (additionalBackground additionalReserved : ℕ) → Capacity

total : Capacity → ℕ
total single = 1
total (shared background reserved) = suc background + suc reserved
backgroundLimit : Capacity → ℕ
backgroundLimit single = 1
backgroundLimit (shared background reserved) = suc background
reserved : Capacity → ℕ
reserved single = 1
reserved (shared background extra) = suc extra

defaultReservation : ∀ background → reserved (shared background 0) ≡ 1
defaultReservation background = refl
backgroundLeavesReserved : ∀ background extra → backgroundLimit (shared background extra) + reserved (shared background extra) ≡ total (shared background extra)
backgroundLeavesReserved background extra = refl

-- Running background work uses at most its share. In shared mode it can
-- advance even while interactive requests wait. In single-slot mode an
-- already-running background job first checkpoints and yields the slot.
record Occupancy (capacity : Capacity) : Set where
  constructor occupancy
  field interactive background waitingInteractive : ℕ
        withinTotal : interactive + background ≤ total capacity
        withinBackground : background ≤ backgroundLimit capacity

canStartBackground : ∀ {capacity} → Occupancy capacity → Bool
canStartBackground {single} (occupancy zero zero zero _ _) = true
canStartBackground {single} _ = false
canStartBackground {shared b r} (occupancy active background waiting bounded limit) with suc background ≤? suc b | suc (active + background) ≤? total (shared b r)
... | Relation.Nullary.yes _ | Relation.Nullary.yes _ = true
... | _ | _ = false

needsYield : Occupancy single → Bool
needsYield (occupancy active zero waiting bounded limit) = false
needsYield (occupancy active (suc background) zero bounded limit) = false
needsYield (occupancy active (suc background) (suc waiting) bounded limit) = true

-- Handoff of the single slot transfers it from background to an already
-- waiting interactive request, retaining the saved work unchanged.
data Holder : Set where
  freeHolder interactiveHolder backgroundHolder : Holder

record SingleSlot (Saved : Set) : Set where
  constructor slot
  field holder : Holder
        interactiveWaiting : Bool
        saved : Saved

handoff : ∀ {Saved} → SingleSlot Saved → SingleSlot Saved
handoff (slot backgroundHolder true saved) = slot interactiveHolder false saved
handoff before = before

handoffGrantsInteractive : ∀ {Saved} (saved : Saved) →
  SingleSlot.holder (handoff (slot backgroundHolder true saved)) ≡ interactiveHolder
handoffGrantsInteractive saved = refl

handoffKeepsSavedWork : ∀ {Saved} (before : SingleSlot Saved) →
  SingleSlot.saved (handoff before) ≡ SingleSlot.saved before
handoffKeepsSavedWork (slot freeHolder waiting saved) = refl
handoffKeepsSavedWork (slot interactiveHolder waiting saved) = refl
handoffKeepsSavedWork (slot backgroundHolder true saved) = refl
handoffKeepsSavedWork (slot backgroundHolder false saved) = refl

-- Yield releases execution capacity without discarding the accepted job or
-- committed results. Resumption does not require reauthorizing the family.
module Yield (Progress Results Temporary : Set) where
  module Work = Control.Model Progress Results Temporary

  yield : Work.State → Work.State
  yield before = before

  preservesWork : ∀ before → Work.State.current (yield before) ≡ Work.State.current before
  preservesWork before = refl

  preservesResults : ∀ before → Work.State.committed (yield before) ≡ Work.State.committed before
  preservesResults before = refl

  preservesAuthorization : ∀ before → Work.State.authorized (yield before) ≡ Work.State.authorized before
  preservesAuthorization before = refl

-- A round visits every job already waiting once. Jobs admitted during the
-- round are appended after that finite prefix, so they cannot overtake it.
module Round {Job : Set} (advance : Job → Maybe Job) where
  -- A finished job leaves the queue. A job with more work rejoins its tail.
  next : Job → List Job
  next job with advance job
  ... | nothing = []
  ... | just remaining = remaining ∷ []
  record Outcome : Set where
    constructor outcome
    field visited queued : List Job
  prepend : Job → Outcome → Outcome
  prepend job (outcome served queued) = outcome (job ∷ served) queued
  -- New work and remaining work join the tail after the original prefix.
  sweep : List Job → List Job → List (List Job) → Outcome
  sweep [] queued arrivals = outcome [] queued
  sweep (job ∷ rest) queued [] = prepend job (sweep rest (queued ++ next job) [])
  sweep (job ∷ rest) queued (new ∷ arrivals) = prepend job (sweep rest (queued ++ (next job ++ new)) arrivals)
  -- These are the permitted one-job transitions. Arrivals join only the back.
  data Turns : List Job → List Job → List (List Job) → Outcome → Set where
    stopped : ∀ queued arrivals → Turns [] queued arrivals (outcome [] queued)
    served : ∀ job rest queued result → Turns rest (queued ++ next job) [] result →
      Turns (job ∷ rest) queued [] (prepend job result)
    servedWithArrivals : ∀ job rest queued new arrivals result →
      Turns rest (queued ++ (next job ++ new)) arrivals result →
      Turns (job ∷ rest) queued (new ∷ arrivals) (prepend job result)
  implementsTurns : ∀ front queued arrivals → Turns front queued arrivals (sweep front queued arrivals)
  implementsTurns [] queued arrivals = stopped queued arrivals
  implementsTurns (job ∷ rest) queued [] = served job rest queued _ (implementsTurns rest (queued ++ next job) [])
  implementsTurns (job ∷ rest) queued (new ∷ arrivals) =
    servedWithArrivals job rest queued new arrivals _ (implementsTurns rest (queued ++ (next job ++ new)) arrivals)
  allWaitingVisited : ∀ front queued arrivals job → job ∈ front → job ∈ Outcome.visited (sweep front queued arrivals)
  allWaitingVisited (job ∷ rest) queued [] .job (here refl) = here refl
  allWaitingVisited (first ∷ rest) queued [] job (there member) = there (allWaitingVisited rest (queued ++ next first) [] job member)
  allWaitingVisited (job ∷ rest) queued (new ∷ arrivals) .job (here refl) = here refl
  allWaitingVisited (first ∷ rest) queued (new ∷ arrivals) job (there member) = there (allWaitingVisited rest (queued ++ (next first ++ new)) arrivals job member)
  queuedPreserved : ∀ front queued arrivals job → job ∈ queued → job ∈ Outcome.queued (sweep front queued arrivals)
  queuedPreserved [] queued arrivals job member = member
  queuedPreserved (first ∷ rest) queued [] job member =
    queuedPreserved rest (queued ++ next first) [] job (∈-++⁺ˡ member)
  queuedPreserved (first ∷ rest) queued (new ∷ arrivals) job member =
    queuedPreserved rest (queued ++ (next first ++ new)) arrivals job (∈-++⁺ˡ member)

  -- Productiveness is an environmental condition on the actual work.
  data Progress (remaining : Job → ℕ) (job : Job) : Set where
    finished : advance job ≡ nothing → Progress remaining job
    advanced : ∀ nextJob → advance job ≡ just nextJob → remaining nextJob < remaining job → Progress remaining job
  waitingProgresses : ∀ front queued arrivals job remaining → Progress remaining job → job ∈ front →
    (job ∈ Outcome.visited (sweep front queued arrivals)) × Progress remaining job
  waitingProgresses front queued arrivals job remaining productive member =
    allWaitingVisited front queued arrivals job member , productive


  nextPresent : ∀ job nextJob → advance job ≡ just nextJob → nextJob ∈ next job
  nextPresent job nextJob observed rewrite observed = here refl

  requeuedAfterTurn : ∀ front queued arrivals job nextJob → job ∈ front →
    advance job ≡ just nextJob → nextJob ∈ Outcome.queued (sweep front queued arrivals)
  requeuedAfterTurn (job ∷ rest) queued [] .job nextJob (here refl) observed =
    queuedPreserved rest (queued ++ next job) [] nextJob (∈-++⁺ʳ queued (nextPresent job nextJob observed))
  requeuedAfterTurn (first ∷ rest) queued [] job nextJob (there present) observed =
    requeuedAfterTurn rest (queued ++ next first) [] job nextJob present observed
  requeuedAfterTurn (job ∷ rest) queued (new ∷ arrivals) .job nextJob (here refl) observed =
    queuedPreserved rest (queued ++ (next job ++ new)) arrivals nextJob
      (∈-++⁺ʳ queued (∈-++⁺ˡ (nextPresent job nextJob observed)))
  requeuedAfterTurn (first ∷ rest) queued (new ∷ arrivals) job nextJob (there present) observed =
    requeuedAfterTurn rest (queued ++ (next first ++ new)) arrivals job nextJob present observed

  -- Once the finite round is executed, a productive waiting job has either
  -- finished or its strictly smaller remaining work is back in the queue.
  productiveTurn : ∀ front queued arrivals job remaining → Progress remaining job → job ∈ front →
    (job ∈ Outcome.visited (sweep front queued arrivals)) ×
    ((advance job ≡ nothing) ⊎ Σ Job (λ nextJob →
      (advance job ≡ just nextJob) × ((remaining nextJob < remaining job) ×
        (nextJob ∈ Outcome.queued (sweep front queued arrivals)))))
  productiveTurn front queued arrivals job remaining (finished observed) present =
    allWaitingVisited front queued arrivals job present , inj₁ observed
  productiveTurn front queued arrivals job remaining (advanced nextJob observed smaller) present =
    allWaitingVisited front queued arrivals job present , inj₂
      (nextJob , observed , smaller , requeuedAfterTurn front queued arrivals job nextJob present observed)
