{-# OPTIONS --safe #-}
-- Interactive requests retain capacity; background jobs take fair turns.
module Muninn.FairScheduling where
import Muninn.OwnedState as O
import Muninn.WorkQueue as Q
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; _≤?_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (Maybe; just; nothing)
import Relation.Nullary
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; sym)
module DB = O.DB

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

-- Yield changes only the durable work phase. Existing receipt/checkpoint and
-- already-published results are left in place; the worker can take it up later.
yielded : O.Owner → List ℕ → Q.Info → O.Record
yielded owner versions info = O.recordOf owner (O.acceptedWork versions (Q.move Q.queued info))
yield : O.World → ℕ → O.Owner → List ℕ → Q.Info → O.World
yield world slot owner versions info = DB.write slot (yielded owner versions info) world

-- Only a currently running, actually stored job can be yielded.
yieldAt : ℕ → DB.Transaction Bool
yieldAt slot = DB.read slot choose
  where
  choose : Maybe O.Record → DB.Transaction Bool
  choose (just (O.recordOf owner (O.acceptedWork versions info))) with Q.Info.phase info
  ... | Q.running = DB.put slot (yielded owner versions info) (DB.commit true)
  ... | _ = DB.commit false
  choose _ = DB.commit false

yieldAtRunning : ∀ world slot owner versions info →
  DB.lookup slot world ≡ just (O.recordOf owner (O.acceptedWork versions info)) → Q.Info.phase info ≡ Q.running →
  DB.execute (yieldAt slot) world ≡ (true , yield world slot owner versions info)
yieldAtRunning world slot owner versions info found running rewrite found | running = refl

yieldKeepsIdentity : ∀ info →
  (Q.Info.id (Q.move Q.queued info) ≡ Q.Info.id info) × (Q.Info.parent (Q.move Q.queued info) ≡ Q.Info.parent info)
yieldKeepsIdentity info = Q.sameRequest Q.queued info

yieldKeepsOtherRecord : ∀ world slot other owner versions info → slot ≢ other →
  DB.lookup other (yield world slot owner versions info) ≡ DB.lookup other world
yieldKeepsOtherRecord world slot other owner versions info different = DB.writePreservesOther slot other (yielded owner versions info) world different

-- A job row and its receipt are distinct records. Checkpoint state and all
-- other persisted rows therefore survive yielding the worker slot.
yieldKeepsReceipt : ∀ world slot receiptSlot owner receiptOwner versions info receipt →
  DB.lookup slot world ≡ just (O.recordOf owner (O.acceptedWork versions info)) →
  DB.lookup receiptSlot world ≡ just (O.recordOf receiptOwner (O.receipt receipt)) →
  DB.lookup receiptSlot (yield world slot owner versions info) ≡ just (O.recordOf receiptOwner (O.receipt receipt))
yieldKeepsReceipt world slot receiptSlot owner receiptOwner versions info receipt jobAt receiptAt =
  trans (yieldKeepsOtherRecord world slot receiptSlot owner versions info distinct) receiptAt
  where
  distinct : slot ≢ receiptSlot
  distinct refl with trans (sym jobAt) receiptAt
  ... | ()

yieldLeavesWorkQueued : ∀ world slot owner versions info →
  DB.lookup slot (yield world slot owner versions info) ≡ just (yielded owner versions info)
yieldLeavesWorkQueued world slot owner versions info = DB.writeVisible slot (yielded owner versions info) world

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
