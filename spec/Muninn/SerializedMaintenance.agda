{-# OPTIONS --safe #-}
-- Observable maintenance laws; no SQL, Git, lock or graph implementation.
-- Historical issue #203 admission model. CheckoutPublication governs 1.4.0.
module Muninn.SerializedMaintenance where

open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Muninn.Config as Config
import Muninn.AdmittedSelection as Rules
open import Data.String using (String)

-- One gate per family. Counts denote active database operations, not saved
-- cursors. A request stops admission before waiting for existing users.
data Gate : Set where
  serving draining : ℕ → Gate
  exclusive : Gate

data Admit : Gate → Gate → Set where
  admit : ∀ {n} → Admit (serving n) (serving (suc n))

noAdmissionWhileDraining : ∀ n next → ¬ Admit (draining n) next
noAdmissionWhileDraining n next ()

noAdmissionWhileExclusive : ∀ next → ¬ Admit exclusive next
noAdmissionWhileExclusive next ()

request : Gate → Gate
request (serving n) = draining n
request (draining n) = draining n
request exclusive = exclusive

data Leave : Gate → Gate → Set where
  leaveServing : ∀ {n} → Leave (serving (suc n)) (serving n)
  leaveDraining : ∀ {n} → Leave (draining (suc n)) (draining n)

data Acquire : Gate → Set where
  drained : Acquire (draining zero)

acquisitionRequiresNoReaders : ∀ n → Acquire (draining n) → n ≡ zero
acquisitionRequiresNoReaders zero drained = refl

-- Pending is durable; active users/lock ownership are not. Recovery must not
-- turn a pending operation into a serving family.
recover : Bool → Gate
recover true = draining zero
recover false = serving zero

pendingRecoveryRefusesAdmission : ∀ next → ¬ Admit (recover true) next
pendingRecoveryRefusesAdmission next ()

-- Abstract resolved views, independent of base/delta physical representation.
-- Natural numbers stand for checkout, path and immutable version identities.
View : Set
View = ℕ → Maybe ℕ

Views : Set
Views = ℕ → View

select : (ℕ → Bool) → View → View
select allowed candidates path with allowed path
... | true = candidates path
... | false = nothing

excludedAbsent : ∀ allowed candidates path → allowed path ≡ false →
  select allowed candidates path ≡ nothing
excludedAbsent allowed candidates path excluded rewrite excluded = refl

includedRetained : ∀ allowed candidates path → allowed path ≡ true →
  select allowed candidates path ≡ candidates path
includedRetained allowed candidates path included rewrite included = refl

included : Config.Decision → Bool
included Config.Drop = false
included Config.T1 = true
included Config.T2 = true

-- Bind the abstract selector to the existing admitted ordered family rules.
policySelection : (policy : Config.FamilyPolicy) → Rules.FamilyEntries policy →
  (ℕ → Bool) → (ℕ → String) → View → View
policySelection policy entries gitIgnored names =
  select (λ path → included (Rules.classify policy entries (gitIgnored path) (names path) false))

policyDropAbsent : ∀ policy entries gitIgnored names candidates path →
  Rules.classify policy entries (gitIgnored path) (names path) false ≡ Config.Drop →
  policySelection policy entries gitIgnored names candidates path ≡ nothing
policyDropAbsent policy entries gitIgnored names candidates path dropped rewrite dropped = refl

replace : ℕ → View → Views → Views
replace target desired old checkout with target ≟ checkout
... | yes _ = desired
... | no _ = old checkout

targetUpdated : ∀ target desired old path →
  replace target desired old target path ≡ desired path
targetUpdated target desired old path with target ≟ target
... | yes _ = refl
... | no different = ⊥-elim (different refl)

otherCheckoutPreserved : ∀ target desired old checkout path →
  ¬ (target ≡ checkout) → replace target desired old checkout path ≡ old checkout path
otherCheckoutPreserved target desired old checkout path different with target ≟ checkout
... | yes same = ⊥-elim (different same)
... | no _ = refl

Referenced : Views → ℕ → Set
Referenced views version = Σ ℕ (λ checkout → Σ ℕ (λ path → views checkout path ≡ just version))

-- Decidability is supplied by enumeration of the finite stored manifests.
-- It is not an arbitrary keeper predicate: its type requires actual references.
prune : ∀ {Payload : Set} (views : Views) →
  ((version : ℕ) → Dec (Referenced views version)) →
  (ℕ → Maybe Payload) → ℕ → Maybe Payload
prune views referenced stored version with referenced version
... | yes _ = stored version
... | no _ = nothing

sharedVersionPreserved : ∀ {Payload : Set} views referenced
  (stored : ℕ → Maybe Payload) version → Referenced views version →
  prune views referenced stored version ≡ stored version
sharedVersionPreserved views referenced stored version needed with referenced version
... | yes _ = refl
... | no absent = ⊥-elim (absent needed)

unusedVersionRemoved : ∀ {Payload : Set} views referenced
  (stored : ℕ → Maybe Payload) version → ¬ Referenced views version →
  prune views referenced stored version ≡ nothing
unusedVersionRemoved views referenced stored version unused with referenced version
... | yes needed = ⊥-elim (unused needed)
... | no _ = refl

-- A publication changes only derived data; notes are outside that payload.
module Publication (Index Notes : Set) where
  record State : Set where
    constructor state
    field index : Index
          notes : Notes
  open State public

  publish : Index → State → State
  publish next old = state next (notes old)

  notesPreserved : ∀ next old → notes (publish next old) ≡ notes old
  notesPreserved next old = refl

  data Transaction (before after : State) : State → Set where
    rollback : Transaction before after before
    commit : Transaction before after after

  data Outcome (before after actual : State) : Set where
    oldState : actual ≡ before → Outcome before after actual
    newState : actual ≡ after → Outcome before after actual

  noPartialPublication : ∀ before after actual → Transaction before after actual →
    Outcome before after actual
  noPartialPublication before after .before rollback = oldState refl
  noPartialPublication before after .after commit = newState refl

-- Completion is checked against the latest requested generation, including
-- events that arrived during maintenance. Generations are not timestamps.
record Completion (requested applied pending : ℕ) : Set where
  constructor complete
  field current : applied ≡ requested
        empty : pending ≡ zero

data Reopen (requested applied pending : ℕ) : Gate → Gate → Set where
  reopen : Completion requested applied pending →
    Reopen requested applied pending exclusive (serving zero)

cannotReopenWithPending : ∀ requested applied n →
  ¬ Reopen requested applied (suc n) exclusive (serving zero)
cannotReopenWithPending requested applied n (reopen (complete _ ()))

cannotReopenStale : ∀ requested applied pending → ¬ (applied ≡ requested) →
  ¬ Reopen requested applied pending exclusive (serving zero)
cannotReopenStale requested applied pending stale (reopen proof) =
  stale (Completion.current proof)
