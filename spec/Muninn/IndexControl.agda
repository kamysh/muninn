{-# OPTIONS --safe #-}
-- Worker admission checks the current durable state inside its transaction.
module Muninn.IndexControl where
import Muninn.OwnedState as O
import Muninn.WorkQueue as Q
import Muninn.CatalogInputs as I
import Muninn.ExclusionOutcomes as E
import Muninn.ReceiptTypes as R
import Muninn.ReceiptLedger as L
open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (Bool; true; false; not; _∧_)
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.String using (String)
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
module DB = O.DB

familyRunnable : O.RegistrationInfo → Bool
familyRunnable info = O.RegistrationInfo.indexingEnabled info ∧
  (O.RegistrationInfo.creationCompleted info ∧
    (not (O.RegistrationInfo.retired info) ∧ not (O.RegistrationInfo.paused info)))

-- Registration and configuration cannot themselves produce StartAuthority.
-- The request must identify the actual family and the inspected policy revision.
record StartAuthority (request : I.IntentInput I.start)
  (info : O.RegistrationInfo) (policy : O.PolicyVersionInfo) : Set where
  constructor authority
  field prepared : O.RegistrationInfo.creationCompleted info ≡ true
        unpaused : O.RegistrationInfo.paused info ≡ false
        active : O.RegistrationInfo.retired info ≡ false
        familyMatches : I.FamilyTarget.expectedFamily (I.PolicyTarget.target (I.Mutation.input request)) ≡ O.RegistrationInfo.id info
        policyFamily : O.PolicyVersionInfo.familyId policy ≡ O.RegistrationInfo.id info
        revisionMatches : I.PolicyTarget.expectedRevision (I.Mutation.input request) ≡ O.PolicyVersionInfo.revision policy

authorize : ∀ request info policy → StartAuthority request info policy → O.RegistrationInfo
authorize request info policy permission = record info { indexingEnabled = true }

explicitStartAuthorizes : ∀ request info policy permission → O.RegistrationInfo.indexingEnabled (authorize request info policy permission) ≡ true
explicitStartAuthorizes request info policy permission = refl

startKeepsPause : ∀ request info policy permission → O.RegistrationInfo.paused (authorize request info policy permission) ≡ O.RegistrationInfo.paused info
startKeepsPause request info policy permission = refl

module Worker (family familySlot workSlot : ℕ) (id : I.OperationId) (generation : ℕ) where
  owner = O.family family
  familyReady : Maybe O.Record → Bool
  familyReady (just (O.recordOf actualOwner (O.registration info))) = familyRunnable info ∧ E.sameOwner actualOwner owner
  familyReady _ = false

  workReady : Maybe O.Record → Bool
  workReady (just (O.recordOf actualOwner (O.acceptedWork versions info))) =
    Q.runnable (Q.Info.phase info) ∧ (E.sameOwner actualOwner owner ∧
      (does (L.sameId id (Q.Info.id info)) ∧ does (generation ≟ Q.Info.generation info)))
  workReady _ = false

  receiptReady : Maybe (L.Found id) → Bool
  receiptReady (just (L.found slot actualOwner (R.active input names progress))) = E.sameOwner actualOwner owner
  receiptReady _ = false

  allowed : O.World → Bool
  allowed world = workReady (DB.lookup workSlot world) ∧
    (familyReady (DB.lookup familySlot world) ∧
      (receiptReady (L.find id world) ∧ not (E.pendingRemovalFor owner world)))

  transaction : ∀ {A : Set} → DB.Transaction A → A → DB.Transaction A
  transaction body waiting = DB.scan (λ world → choose body waiting world)
    where
    choose : ∀ {A : Set} → DB.Transaction A → A → O.World → DB.Transaction A
    choose body waiting world with allowed world
    ... | true = body
    ... | false = DB.abort waiting

  committedRequiresPermission : ∀ {A : Set} (body : DB.Transaction A) waiting before result after →
    DB.evaluate (transaction body waiting) before ≡ DB.committed result after →
    allowed before ≡ true × DB.evaluate body before ≡ DB.committed result after
  committedRequiresPermission body waiting before result after committed with allowed before
  ... | true = refl , committed
  ... | false with committed
  ...   | ()

  ready : ∀ {A : Set} (body : DB.Transaction A) waiting world → allowed world ≡ true →
    DB.evaluate (transaction body waiting) world ≡ DB.evaluate body world
  ready body waiting world permitted with allowed world
  ... | true = refl
  ... | false with permitted
  ...   | ()

  effect : L.Effect → String → L.Effect
  effect body waiting = record
    { transaction = transaction (L.Effect.transaction body) waiting
    ; guidance = L.Effect.guidance body
    ; isolates = λ before result after committed → L.Effect.isolates body before result after
        (proj₂ (committedRequiresPermission (L.Effect.transaction body) waiting before result after committed)) }

  missingWorkStops : ∀ world → DB.lookup workSlot world ≡ nothing → allowed world ≡ false
  missingWorkStops world absent rewrite absent = refl

  pausedWorkStops : ∀ world actualOwner versions info →
    DB.lookup workSlot world ≡ just (O.recordOf actualOwner (O.acceptedWork versions info)) →
    Q.Info.phase info ≡ Q.paused → allowed world ≡ false
  pausedWorkStops world actualOwner versions info found paused rewrite found | paused = refl
