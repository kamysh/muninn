{-# OPTIONS --safe #-}
-- Confirmed absence has one short grace; retirement adds no cache-retention TTL.
module Muninn.Retirement where

import Muninn.Dialogue as D
import Muninn.OwnedState as O
open import Data.String using (_++_)
open import Data.Nat using (ℕ; _+_; _≤_; _≤?_; _≟_)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)

data Phase : Set where active retired : Phase

record State : Set where
  constructor state
  field phase : Phase
        absentSince : Maybe ℕ

initial : State
initial = state active nothing

-- These are inspection outcomes, not path-string comparisons. verifiedSame
-- must be supplied by the identity protocol in #32; its evidence-source choice
-- remains separate from this timer. Inconclusive is never confirmed absence.
data Inspection : Set where
  verifiedSame confirmedAbsent : Inspection
  inconclusive : D.Text → Inspection

graceSeconds : ℕ
graceSeconds = 60

absence : ℕ → State → State
absence now (state retired since) = state retired nothing
absence now (state active nothing) = state active (just now)
absence now (state active (just since)) with since + graceSeconds ≤? now
... | yes elapsed = state retired nothing
... | no waiting = state active (just since)

inspect : ℕ → Inspection → State → State
inspect now verifiedSame before = state active nothing
inspect now confirmedAbsent before = absence now before
inspect now (inconclusive why) before = state (State.phase before) nothing

-- This state is scoped to an existing registered identity. Explicit removal
-- removes that registration under #34; it cannot be reactivated by inspect.

firstAbsenceWaits : ∀ now → inspect now confirmedAbsent (state active nothing) ≡ state active (just now)
firstAbsenceWaits now = refl

withinGrace : ∀ now since → ¬ (since + graceSeconds ≤ now) →
  inspect now confirmedAbsent (state active (just since)) ≡ state active (just since)
withinGrace now since early with since + graceSeconds ≤? now
... | yes elapsed = ⊥-elim (early elapsed)
... | no waiting = refl

elapsedRetires : ∀ now since → since + graceSeconds ≤ now →
  inspect now confirmedAbsent (state active (just since)) ≡ state retired nothing
elapsedRetires now since elapsed with since + graceSeconds ≤? now
... | yes enough = refl
... | no early = ⊥-elim (early elapsed)

newRetirementNeedsEvidence : ∀ now observation since →
  State.phase (inspect now observation (state active since)) ≡ retired →
  observation ≡ confirmedAbsent × Σ ℕ (λ start → since ≡ just start × start + graceSeconds ≤ now)
newRetirementNeedsEvidence now verifiedSame since ()
newRetirementNeedsEvidence now (inconclusive why) since ()
newRetirementNeedsEvidence now confirmedAbsent nothing ()
newRetirementNeedsEvidence now confirmedAbsent (just since) retiredNow with since + graceSeconds ≤? now
... | yes elapsed = refl , since , refl , elapsed
... | no early with retiredNow
...   | ()

uncertaintyCannotRetire : ∀ now why before → State.phase (inspect now (inconclusive why) before) ≡ State.phase before
uncertaintyCannotRetire now why before = refl

uncertaintyResetsGrace : ∀ now why before → State.absentSince (inspect now (inconclusive why) before) ≡ nothing
uncertaintyResetsGrace now why before = refl

verifiedReturnReactivates : ∀ now before → inspect now verifiedSame before ≡ state active nothing
verifiedReturnReactivates now before = refl

retirementStableWhileMissing : ∀ now since → inspect now confirmedAbsent (state retired since) ≡ state retired nothing
retirementStableWhileMissing now since = refl

data Cleanup : Set where keepRequired reclaimUnusedNow : Cleanup

cleanup : Phase → Cleanup
cleanup active = keepRequired
cleanup retired = reclaimUnusedNow

-- No time or cache-age parameter exists: after logical retirement, only real
-- readers, accepted work and shared references may postpone reclamation.
retiredHasNoRetentionDelay : ∀ current → State.phase current ≡ retired → cleanup (State.phase current) ≡ reclaimUnusedNow
retiredHasNoRetentionDelay current retiredNow rewrite retiredNow = refl

uncertainQuestion : D.Text → D.Question
uncertainQuestion why = D.prerequisite
  (D.text 'I' (" cannot confirm whether the registered repository is present: " ++ D.render why))
  (D.text 'C' "heck the path and access permissions, or tell me where the registered repository moved. I will keep its registration and will not treat this inspection as proof that it was removed.")


phaseFlag : Phase → Bool
phaseFlag active = false
phaseFlag retired = true

fromFlag : Bool → Phase
fromFlag false = active
fromFlag true = retired

flagRoundTrip : ∀ phase → fromFlag (phaseFlag phase) ≡ phase
flagRoundTrip active = refl
flagRoundTrip retired = refl

registrationState : O.RegistrationInfo → State
registrationState info = state (fromFlag (O.RegistrationInfo.retired info)) (O.RegistrationInfo.missingSince info)

checkoutState : O.CheckoutInfo → State
checkoutState info = state (fromFlag (O.CheckoutInfo.retired info)) (O.CheckoutInfo.missingSince info)

saveRegistration : State → O.RegistrationInfo → O.RegistrationInfo
saveRegistration current info = record info
  { retired = phaseFlag (State.phase current); missingSince = State.absentSince current }

saveCheckout : State → O.CheckoutInfo → O.CheckoutInfo
saveCheckout current info = record info
  { retired = phaseFlag (State.phase current); missingSince = State.absentSince current }

registrationCheckpoint : ∀ current info → registrationState (saveRegistration current info) ≡ current
registrationCheckpoint (state phase since) info rewrite flagRoundTrip phase = refl

checkoutCheckpoint : ∀ current info → checkoutState (saveCheckout current info) ≡ current
checkoutCheckpoint (state phase since) info rewrite flagRoundTrip phase = refl

registrationUpdate : ℕ → Inspection → O.RegistrationInfo → O.RegistrationInfo
registrationUpdate now observation info = saveRegistration (inspect now observation (registrationState info)) info

checkoutUpdate : ℕ → Inspection → O.CheckoutInfo → O.CheckoutInfo
checkoutUpdate now observation info = saveCheckout (inspect now observation (checkoutState info)) info

registrationUpdateMatches : ∀ now observation info → registrationState (registrationUpdate now observation info) ≡
  inspect now observation (registrationState info)
registrationUpdateMatches now observation info = registrationCheckpoint _ info

checkoutUpdateMatches : ∀ now observation info → checkoutState (checkoutUpdate now observation info) ≡
  inspect now observation (checkoutState info)
checkoutUpdateMatches now observation info = checkoutCheckpoint _ info

registrationMetadataPreserved : ∀ current info → O.RegistrationInfo.metadata (saveRegistration current info) ≡ O.RegistrationInfo.metadata info
registrationMetadataPreserved current info = refl

checkoutControlsPreserved : ∀ current info →
  O.CheckoutInfo.paused (saveCheckout current info) ≡ O.CheckoutInfo.paused info ×
  O.CheckoutInfo.gitSuspended (saveCheckout current info) ≡ O.CheckoutInfo.gitSuspended info ×
  O.CheckoutInfo.metadata (saveCheckout current info) ≡ O.CheckoutInfo.metadata info
checkoutControlsPreserved current info = refl , refl , refl
