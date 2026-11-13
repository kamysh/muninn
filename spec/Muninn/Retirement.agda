{-# OPTIONS --safe #-}
-- Confirmed absence has one short grace; retirement adds no cache-retention TTL.
module Muninn.Retirement where

import Muninn.Dialogue as D
import Muninn.RepositoryIdentity as Identity
import Muninn.PendingRemoval as Pending
import Muninn.OwnedState as Owned
open import Data.String using (_++_)
open import Data.Nat using (ℕ; _+_; _≤_; _≤?_; _≟_)
open import Data.Bool using (Bool; true; false; _∧_; not)
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
-- carries verified identity evidence from #32. Inconclusive is never confirmed absence.
data Inspection : Set where
  verifiedSame : (saved : Identity.FamilyBinding) → (observed : Identity.Observation) →
    Identity.FamilyAssociation saved observed → Inspection
  confirmedAbsent : Inspection
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
inspect now (verifiedSame saved observed evidence) before = state active nothing
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
newRetirementNeedsEvidence now (verifiedSame saved observed evidence) since ()
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

verifiedReturnReactivates : ∀ now before saved observed evidence →
  inspect now (verifiedSame saved observed evidence) before ≡ state active nothing
verifiedReturnReactivates now before saved observed evidence = refl

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



-- The grace checkpoint and retirement flag are part of the saved records.
phaseFlag : Phase → Bool
phaseFlag active = false
phaseFlag retired = true

fromFlag : Bool → Phase
fromFlag false = active
fromFlag true = retired

registrationState : Owned.RegistrationInfo → State
registrationState info = state (fromFlag (Owned.RegistrationInfo.retired info)) (Owned.RegistrationInfo.missingSince info)

checkoutState : Owned.CheckoutInfo → State
checkoutState info = state (fromFlag (Owned.CheckoutInfo.retired info)) (Owned.CheckoutInfo.missingSince info)

saveRegistration : State → Owned.RegistrationInfo → Owned.RegistrationInfo
saveRegistration current info = record info
  { retired = phaseFlag (State.phase current); missingSince = State.absentSince current }

saveCheckout : State → Owned.CheckoutInfo → Owned.CheckoutInfo
saveCheckout current info = record info
  { retired = phaseFlag (State.phase current); missingSince = State.absentSince current }

registrationPreservesMetadata : ∀ current info →
  Owned.RegistrationInfo.metadata (saveRegistration current info) ≡ Owned.RegistrationInfo.metadata info
registrationPreservesMetadata current info = refl

registrationPreservesLegacyReadability : ∀ current info →
  Owned.RegistrationInfo.legacyReadable (saveRegistration current info) ≡ Owned.RegistrationInfo.legacyReadable info
registrationPreservesLegacyReadability current info = refl

-- A retired family's reclaiming work uses the same complete-world cleanup
-- transaction and its current need/protection checks as exclusion cleanup.
import Muninn.CleanupEffects as Effects
import Muninn.CleanupLoop as Loop
import Muninn.CleanupProgress as Progress
import Muninn.CleanupReleased as Released
import Muninn.ExclusionOutcomes as Outcomes
open import Data.List using (List; [])
open import Data.String using (String)
import Data.String as String
import Muninn.Worktree as Worktree
import Muninn.Types as Types

module Reclamation
  (selection : Outcomes.Rule) (accepted : Owned.World)
  (intent : Outcomes.Model.Intent selection accepted) where
  module Model = Outcomes.Model
  module Core = Effects.Model.Core selection accepted intent
  module DB = Owned.DB

  -- Observe the actual registration in the same transaction as the cleanup.
  retiredAt : ℕ → Owned.World → Bool
  retiredAt slot world with DB.lookup slot world
  ... | just (Owned.recordOf owner (Owned.registration info))
    with Outcomes.ownerEqual owner (Outcomes.targetOwner selection)
  ...   | yes same = Owned.RegistrationInfo.retired info
  ...   | no different = false
  retiredAt slot world | _ = false

  reclaim : ℕ → ℕ → DB.Transaction Effects.Reply
  reclaim slot key = DB.scan λ world → choose (retiredAt slot world)
    where
    choose : Bool → DB.Transaction Effects.Reply
    choose false = DB.commit Effects.unchanged
    choose true = Core.transaction key

  notRetiredKeepsWorld : ∀ slot key world → retiredAt slot world ≡ false →
    proj₂ (DB.execute (reclaim slot key) world) ≡ world
  notRetiredKeepsWorld slot key world notRetired rewrite notRetired = refl

  -- Every eligible record is removed in this batch; there is no retention clock.
  eligibleReclaimed : ∀ slot key world → retiredAt slot world ≡ true → Core.Removal key world →
    DB.execute (reclaim slot key) world ≡ (Effects.removed , DB.delete key world)
  eligibleReclaimed slot key world isRetired ready rewrite isRetired with Core.removal? key world
  ... | yes actual = refl
  ... | no impossible = ⊥-elim (impossible ready)

  -- The shared proof protects metadata, readers, needed data and other families.
  safety : ∀ slot key world →
    Model.Safety selection world (proj₂ (DB.execute (reclaim slot key) world))
  safety slot key world with retiredAt slot world
  ... | false = Model.safetyReflexive selection world
  ... | true = Core.transactionSafety key world

  retiredExecutesCore : ∀ slot key world → retiredAt slot world ≡ true →
    DB.execute (reclaim slot key) world ≡ DB.execute (Core.transaction key) world
  retiredExecutesCore slot key world isRetired rewrite isRetired = refl

  -- After existing users release their records, the finite pass reaches the
  -- independent cleanup outcome; no extra age or retention condition applies.
  module Pass = Progress.Model.Pass selection accepted intent
  module Use = Released.Model.Loop selection accepted intent
  module Worker = Loop.Model.Run selection accepted intent

  retiredCleanupFinishes : Owned.Admissible accepted → Use.Released accepted →
    Model.Complete selection accepted intent accepted (Pass.Result.after (Pass.run accepted))
  retiredCleanupFinishes = Worker.finishes

-- Observation and scheduling its newly retired family cleanup commit together.
import Muninn.RecordAllocation as Allocation
import Muninn.CleanupScheduling as Scheduling
import Muninn.ReceiptLedger as Ledger
import Muninn.ReceiptTypes as Receipt
import Muninn.RequestIdentity as Requests
import Muninn.CatalogInputs as Input
open import Muninn.CatalogInputs using (OperationId)
open import Data.Unit using (tt)
open import Data.Nat using (zero)

module FamilyControl
  (selection : Outcomes.Rule) where
  module M = Outcomes.Model
  module DB = Owned.DB
  module Schedule = Scheduling.Model.Family selection

  data Reply : Set where
    inspected cleanupScheduled : Reply
    clarify : D.Question → Reply

  identityQuestion : D.Question
  identityQuestion = D.prerequisite
    (D.text 'I' " cannot confirm this is the registered repository.")
    (D.text 'T' "ell me whether the repository moved or was replaced, and where it is now.")

  registrationQuestion : D.Question
  registrationQuestion = D.prerequisite
    (D.text 'I' " cannot find this registered repository.")
    (D.text 'T' "ell me where the repository is, so I can continue.")

  jobQuestion : D.Question
  jobQuestion = D.prerequisite
    (D.text 'I' " found an existing request with different details.")
    (D.text 'S' "tart a new request so I can continue the cleanup.")

  inspectionReply : Inspection → Reply
  inspectionReply (inconclusive why) = clarify (uncertainQuestion why)
  inspectionReply _ = inspected

  -- A successful identity observation must name this stored family.
  identityFits : Inspection → Owned.RegistrationInfo → Bool
  identityFits confirmedAbsent info = true
  identityFits (inconclusive why) info = true
  identityFits (verifiedSame saved observed evidence) info with Owned.RegistrationInfo.identity info
  ... | nothing = false
  ... | just id with Types.UUID.value (Worktree.FamilyId.value id) String.≟
                    Types.UUID.value (Worktree.FamilyId.value (Identity.FamilyBinding.id saved))
  ...   | yes same = true
  ...   | no different = false

  -- A live removal keeps its fence even when the repository is rediscovered.
  observationFits : Inspection → Owned.RegistrationInfo → Owned.World → Bool
  observationFits (verifiedSame saved observed evidence) info world =
    identityFits (verifiedSame saved observed evidence) info ∧ not (Pending.pending (Outcomes.targetOwner selection) world)
  observationFits observation info world = identityFits observation info

  inspectionDenied : Owned.World → Reply
  inspectionDenied world with Pending.pending (Outcomes.targetOwner selection) world
  ... | true = inspected
  ... | false = clarify identityQuestion

  -- A cleanup task must belong to an already accepted job for this family.
  jobReady : OperationId → Owned.RegistrationInfo → Owned.World → Bool
  jobReady id info world with Ledger.find id world | Owned.RegistrationInfo.identity info
  ... | just (Ledger.found slot owner (Receipt.active (Requests.durableJob Input.reclaimRetired input) names progress)) | just family
    with Outcomes.ownerEqual owner (Outcomes.targetOwner selection) | Ledger.sameId (Input.FamilyJob.operationId input) id |
      Types.UUID.value (Worktree.FamilyId.value (Input.FamilyJob.family input)) String.≟ Types.UUID.value (Worktree.FamilyId.value family)
  ...   | yes sameOwner | yes sameId | yes sameFamily = true
  ...   | _ | _ | _ = false
  jobReady id info world | _ | _ = false

  -- The daemon can accept a new job and its work in this same commit.
  freshReceipt : OperationId → Worktree.FamilyId → Owned.Owner → Owned.Record
  freshReceipt id family owner = Owned.recordOf owner (Owned.receipt (Receipt.entry id
    (Receipt.active (Requests.durableJob Input.reclaimRetired (record { operationId = id; family = family })) tt
      (Receipt.progressOf zero [] ""))))

  startsCleanup : Phase → Phase → Bool
  startsCleanup active retired = true
  startsCleanup _ _ = false

  update : ℕ → Inspection → OperationId → ℕ → DB.Transaction Reply
  update now observation job slot = DB.scan λ world → examine (DB.lookup slot world) world
    where
    examine : Maybe Owned.Record → Owned.World → DB.Transaction Reply
    examine (just (Owned.recordOf owner (Owned.registration info))) world
      with Outcomes.ownerEqual owner (Outcomes.targetOwner selection)
    ... | no different = DB.commit (clarify registrationQuestion)
    ... | yes same with observationFits observation info world
    ...   | false = DB.commit (inspectionDenied world)
    ...   | true with startsCleanup (State.phase (registrationState info)) (State.phase (inspect now observation (registrationState info)))
    ...     | false =
      DB.put slot (Owned.recordOf owner (Owned.registration (saveRegistration (inspect now observation (registrationState info)) info)))
        (DB.commit (inspectionReply observation))
    ...     | true with jobReady job info world
    ...       | true =
      DB.put (Allocation.freshId world) (Schedule.task job (Allocation.freshId world) "" world)
        (DB.put slot (Owned.recordOf owner (Owned.registration (saveRegistration (inspect now observation (registrationState info)) info)))
          (DB.commit cleanupScheduled))
    ...       | false with Ledger.find job world | Owned.RegistrationInfo.identity info
    ...         | nothing | just family =
      DB.put (Allocation.freshId world) (freshReceipt job family owner)
        (DB.put (Allocation.freshId (DB.write (Allocation.freshId world) (freshReceipt job family owner) world))
          (Schedule.task job (Allocation.freshId (DB.write (Allocation.freshId world) (freshReceipt job family owner) world)) "" (DB.write (Allocation.freshId world) (freshReceipt job family owner) world))
          (DB.put slot (Owned.recordOf owner (Owned.registration (saveRegistration (inspect now observation (registrationState info)) info))) (DB.commit cleanupScheduled)))
    ...         | nothing | nothing = DB.commit (clarify identityQuestion)
    ...         | just existing | _ = DB.commit (clarify jobQuestion)
    examine _ world = DB.commit (clarify registrationQuestion)

  cleanupStarts : ∀ first second → first ≡ active → second ≡ retired → startsCleanup first second ≡ true
  cleanupStarts .active .retired refl refl = refl

  -- On the first transition to retirement, both writes publish together.
  retirementSchedules : ∀ now observation job slot world owner info →
    DB.lookup slot world ≡ just (Owned.recordOf owner (Owned.registration info)) →
    owner ≡ Outcomes.targetOwner selection →
    observationFits observation info world ≡ true →
    jobReady job info world ≡ true →
    State.phase (registrationState info) ≡ active →
    State.phase (inspect now observation (registrationState info)) ≡ retired →
    DB.execute (update now observation job slot) world ≡
      (cleanupScheduled , DB.write slot (Owned.recordOf owner (Owned.registration (saveRegistration (inspect now observation (registrationState info)) info)))
        (DB.write (Allocation.freshId world) (Schedule.task job (Allocation.freshId world) "" world) world))
  retirementSchedules now observation job slot world owner info found same fits ready wasActive nowRetired
    rewrite found | same with Outcomes.ownerEqual (Outcomes.targetOwner selection) (Outcomes.targetOwner selection)
  ... | no impossible = ⊥-elim (impossible refl)
  ... | yes identical rewrite fits | cleanupStarts (State.phase (registrationState info)) (State.phase (inspect now observation (registrationState info))) wasActive nowRetired | ready = refl

  absentJobNotReady : ∀ job info world family → Ledger.find job world ≡ nothing →
    Owned.RegistrationInfo.identity info ≡ just family → jobReady job info world ≡ false
  absentJobNotReady job info world family noJob identity rewrite noJob = refl

  -- A new job is accepted with the retirement and cleanup task atomically.
  freshRetirementSchedules : ∀ now observation job slot world owner info family →
    DB.lookup slot world ≡ just (Owned.recordOf owner (Owned.registration info)) →
    owner ≡ Outcomes.targetOwner selection →
    observationFits observation info world ≡ true →
    Ledger.find job world ≡ nothing → Owned.RegistrationInfo.identity info ≡ just family →
    State.phase (registrationState info) ≡ active →
    State.phase (inspect now observation (registrationState info)) ≡ retired →
    DB.execute (update now observation job slot) world ≡
      (cleanupScheduled , DB.write slot (Owned.recordOf owner (Owned.registration (saveRegistration (inspect now observation (registrationState info)) info)))
        (DB.write (Allocation.freshId (DB.write (Allocation.freshId world) (freshReceipt job family owner) world))
          (Schedule.task job (Allocation.freshId (DB.write (Allocation.freshId world) (freshReceipt job family owner) world)) "" (DB.write (Allocation.freshId world) (freshReceipt job family owner) world))
          (DB.write (Allocation.freshId world) (freshReceipt job family owner) world)))
  freshRetirementSchedules now observation job slot world owner info family found same fits noJob identity wasActive nowRetired
    rewrite found | same with Outcomes.ownerEqual (Outcomes.targetOwner selection) (Outcomes.targetOwner selection)
  ... | no impossible = ⊥-elim (impossible refl)
  ... | yes identical rewrite fits | cleanupStarts (State.phase (registrationState info)) (State.phase (inspect now observation (registrationState info))) wasActive nowRetired | absentJobNotReady job info world family noJob identity | noJob | identity with Outcomes.ownerEqual (Outcomes.targetOwner selection) (Outcomes.targetOwner selection)
  ...   | yes sameOwner = refl
  ...   | no impossible = ⊥-elim (impossible refl)

  -- An identity mismatch cannot reactivate or change the saved registration.
  mismatchedIdentityKeepsWorld : ∀ now observation job slot world owner info →
    DB.lookup slot world ≡ just (Owned.recordOf owner (Owned.registration info)) →
    owner ≡ Outcomes.targetOwner selection → observationFits observation info world ≡ false →
    DB.execute (update now observation job slot) world ≡ (inspectionDenied world , world)
  mismatchedIdentityKeepsWorld now observation job slot world owner info found same mismatch
    rewrite found | same with Outcomes.ownerEqual (Outcomes.targetOwner selection) (Outcomes.targetOwner selection)
  ... | no impossible = ⊥-elim (impossible refl)
  ... | yes identical rewrite mismatch = refl

  -- Atomic retirement cannot alter a row belonging to another family.
  freshRetirementPreservesOther : ∀ now observation job slot world owner info family key value →
    DB.lookup slot world ≡ just (Owned.recordOf owner (Owned.registration info)) →
    owner ≡ Outcomes.targetOwner selection →
    observationFits observation info world ≡ true →
    Ledger.find job world ≡ nothing → Owned.RegistrationInfo.identity info ≡ just family →
    State.phase (registrationState info) ≡ active →
    State.phase (inspect now observation (registrationState info)) ≡ retired →
    DB.lookup key world ≡ just value → Owned.owner value ≢ Outcomes.targetOwner selection →
    DB.lookup key (proj₂ (DB.execute (update now observation job slot) world)) ≡ just value
  freshRetirementPreservesOther now observation job slot world owner info family key value found same fits noJob identity wasActive nowRetired otherFound otherOwner =
    trans (cong (DB.lookup key) (cong proj₂ (freshRetirementSchedules now observation job slot world owner info family found same fits noJob identity wasActive nowRetired)))
      (trans (DB.writePreservesOther slot key updated afterTask slotDifferent)
        (trans (DB.writePreservesOther taskSlot key task receiptWorld taskDifferent)
          (trans (DB.writePreservesOther receiptSlot key receipt world receiptDifferent) otherFound)))
    where
    open import Data.Maybe.Properties using (just-injective)
    import Muninn.CleanupAdmissionStorage as Insert
    import Data.List.Relation.Unary.All as All
    receipt = freshReceipt job family owner
    receiptSlot = Allocation.freshId world
    receiptWorld = DB.write receiptSlot receipt world
    taskSlot = Allocation.freshId receiptWorld
    task = Schedule.task job taskSlot "" receiptWorld
    updated = Owned.recordOf owner (Owned.registration (saveRegistration (inspect now observation (registrationState info)) info))
    afterTask = DB.write taskSlot task receiptWorld

    slotDifferent : slot ≢ key
    slotDifferent refl = otherOwner (trans (sym (cong Owned.owner (just-injective (trans (sym found) otherFound)))) same)

    receiptDifferent : receiptSlot ≢ key
    receiptDifferent refl = Allocation.fresh world (Insert.storedReserved world key value otherFound)

    receiptWorldFound : DB.lookup key receiptWorld ≡ just value
    receiptWorldFound = Insert.oldLookup world receiptSlot receipt (Allocation.fresh world) key value otherFound

    taskDifferent : taskSlot ≢ key
    taskDifferent refl = Allocation.fresh receiptWorld (Insert.storedReserved receiptWorld key value receiptWorldFound)

  existingRetirementPreservesOther : ∀ now observation job slot world owner info key value →
    DB.lookup slot world ≡ just (Owned.recordOf owner (Owned.registration info)) →
    owner ≡ Outcomes.targetOwner selection →
    observationFits observation info world ≡ true → jobReady job info world ≡ true →
    State.phase (registrationState info) ≡ active →
    State.phase (inspect now observation (registrationState info)) ≡ retired →
    DB.lookup key world ≡ just value → Owned.owner value ≢ Outcomes.targetOwner selection →
    DB.lookup key (proj₂ (DB.execute (update now observation job slot) world)) ≡ just value
  existingRetirementPreservesOther now observation job slot world owner info key value found same fits ready wasActive nowRetired otherFound otherOwner =
    trans (cong (DB.lookup key) (cong proj₂ (retirementSchedules now observation job slot world owner info found same fits ready wasActive nowRetired)))
      (trans (DB.writePreservesOther slot key updated afterTask slotDifferent)
        (trans (DB.writePreservesOther taskSlot key task world taskDifferent) otherFound))
    where
    open import Data.Maybe.Properties using (just-injective)
    import Muninn.CleanupAdmissionStorage as Insert
    taskSlot = Allocation.freshId world
    task = Schedule.task job taskSlot "" world
    updated = Owned.recordOf owner (Owned.registration (saveRegistration (inspect now observation (registrationState info)) info))
    afterTask = DB.write taskSlot task world

    slotDifferent : slot ≢ key
    slotDifferent refl = otherOwner (trans (sym (cong Owned.owner (just-injective (trans (sym found) otherFound)))) same)

    taskDifferent : taskSlot ≢ key
    taskDifferent refl = Allocation.fresh world (Insert.storedReserved world key value otherFound)

  -- The scheduled workset covers the actual state after its atomic writes.
  module SavedCapture (before : Owned.World) (slot : ℕ) (job : OperationId)
    (owner : Owned.Owner) (info : Owned.RegistrationInfo) (current : State)
    (oldAt : DB.lookup slot before ≡ just (Owned.recordOf owner (Owned.registration info)))
    (oldOwner : owner ≡ Outcomes.targetOwner selection) (valid : Owned.Admissible before) where
    open import Data.Nat using (_≟_)
    open import Data.List.Membership.Propositional using (_∈_)
    open import Data.List.Relation.Unary.Any using (here; there)
    import Muninn.CleanupObservations as Observations
    import Muninn.CleanupOrder as Order
    import Muninn.CleanupAdmissionStorage as Insert
    import Muninn.CleanupStorage as Storage
    import Data.List.Relation.Unary.All as All

    taskSlot = Allocation.freshId before
    task = Schedule.task job taskSlot "" before
    old = Owned.recordOf owner (Owned.registration info)
    updated = Owned.recordOf owner (Owned.registration (saveRegistration current info))
    inserted = DB.write taskSlot task before
    after = DB.write slot updated inserted
    keys = Schedule.ids taskSlot before

    insertedValid : Owned.Admissible inserted
    insertedValid = Insert.insertAdmissible before taskSlot task valid (Allocation.fresh before) Owned.local All.[] All.[]

    oldInInserted : DB.lookup slot inserted ≡ just old
    oldInInserted = Insert.oldLookup before taskSlot task (Allocation.fresh before) slot old oldAt

    updatedPlaced : Owned.Placed updated
    updatedPlaced rewrite oldOwner = Owned.local

    afterValid : Owned.Admissible after
    afterValid = Storage.writeAdmissible inserted slot old updated insertedValid oldInInserted refl refl updatedPlaced (λ ref ())

    covered : ∀ key value → DB.lookup key after ≡ just value →
      Owned.owner value ≡ Outcomes.targetOwner selection → key ∈ keys
    covered key value found owned with slot ≟ key
    ... | yes refl = there (M.captureComplete selection before slot old (Observations.lookupMember before slot old oldAt) oldOwner)
    ... | no otherSlot with taskSlot ≟ key
    ...   | yes refl = here refl
    ...   | no otherTask = there (M.captureComplete selection before key value (Observations.lookupMember before key value original) owned)
      where
      afterTask : DB.lookup key inserted ≡ just value
      afterTask = trans (sym (DB.writePreservesOther slot key updated inserted otherSlot)) found
      original : DB.lookup key before ≡ just value
      original = trans (sym (DB.writePreservesOther taskSlot key task before otherTask)) afterTask

    intent : M.Intent selection after
    intent = record
      { keys = keys
      ; uniqueBefore = Owned.Admissible.unique afterValid
      ; covers = λ key value present owned → covered key value (Order.memberLookup after key value (Owned.Admissible.unique afterValid) present) owned }

    module Worker = Loop.Model.Run selection after intent
    finishes : Worker.Use.Released after →
      M.Complete selection after intent after (Worker.Pass.Result.after (Worker.Pass.run after))
    finishes = Worker.finishes afterValid

  -- Both scheduling paths instantiate the same completion proof at the exact
  -- world produced by their atomic transaction.
  module ExistingCompletion (now : ℕ) (observation : Inspection) (job : OperationId)
    (slot : ℕ) (world : Owned.World) (owner : Owned.Owner) (info : Owned.RegistrationInfo)
    (found : DB.lookup slot world ≡ just (Owned.recordOf owner (Owned.registration info)))
    (same : owner ≡ Outcomes.targetOwner selection) (fits : observationFits observation info world ≡ true)
    (ready : jobReady job info world ≡ true) (wasActive : State.phase (registrationState info) ≡ active)
    (nowRetired : State.phase (inspect now observation (registrationState info)) ≡ retired)
    (valid : Owned.Admissible world) where
    module Saved = SavedCapture world slot job owner info (inspect now observation (registrationState info)) found same valid
    committedWorld : proj₂ (DB.execute (update now observation job slot) world) ≡ Saved.after
    committedWorld = cong proj₂ (retirementSchedules now observation job slot world owner info found same fits ready wasActive nowRetired)
    finishes : Saved.Worker.Use.Released Saved.after →
      M.Complete selection Saved.after Saved.intent Saved.after (Saved.Worker.Pass.Result.after (Saved.Worker.Pass.run Saved.after))
    finishes = Saved.finishes

  module FreshCompletion (now : ℕ) (observation : Inspection) (job : OperationId)
    (slot : ℕ) (world : Owned.World) (owner : Owned.Owner) (info : Owned.RegistrationInfo)
    (family : Worktree.FamilyId)
    (found : DB.lookup slot world ≡ just (Owned.recordOf owner (Owned.registration info)))
    (same : owner ≡ Outcomes.targetOwner selection) (fits : observationFits observation info world ≡ true)
    (noJob : Ledger.find job world ≡ nothing) (identity : Owned.RegistrationInfo.identity info ≡ just family)
    (wasActive : State.phase (registrationState info) ≡ active)
    (nowRetired : State.phase (inspect now observation (registrationState info)) ≡ retired)
    (valid : Owned.Admissible world) where
    import Muninn.CleanupAdmissionStorage as Insert
    import Data.List.Relation.Unary.All as All
    receipt = freshReceipt job family owner
    receiptWorld = DB.write (Allocation.freshId world) receipt world
    old = Owned.recordOf owner (Owned.registration info)
    receiptWorldValid : Owned.Admissible receiptWorld
    receiptWorldValid = Insert.insertAdmissible world (Allocation.freshId world) receipt valid (Allocation.fresh world) tt All.[] All.[]
    oldInReceiptWorld : DB.lookup slot receiptWorld ≡ just old
    oldInReceiptWorld = Insert.oldLookup world (Allocation.freshId world) receipt (Allocation.fresh world) slot old found
    module Saved = SavedCapture receiptWorld slot job owner info (inspect now observation (registrationState info)) oldInReceiptWorld same receiptWorldValid
    committedWorld : proj₂ (DB.execute (update now observation job slot) world) ≡ Saved.after
    committedWorld = cong proj₂ (freshRetirementSchedules now observation job slot world owner info family found same fits noJob identity wasActive nowRetired)
    finishes : Saved.Worker.Use.Released Saved.after →
      M.Complete selection Saved.after Saved.intent Saved.after (Saved.Worker.Pass.Result.after (Saved.Worker.Pass.run Saved.after))
    finishes = Saved.finishes

  -- Rediscovery cannot undo the fence while a removal is active.
  removalFenceHeld : ∀ saved observed evidence info world →
    Pending.pending (Outcomes.targetOwner selection) world ≡ true →
    observationFits (verifiedSame saved observed evidence) info world ≡ false
  removalFenceHeld saved observed evidence info world activeRemoval rewrite activeRemoval
    with identityFits (verifiedSame saved observed evidence) info
  ... | true = refl
  ... | false = refl

  noReactivationDuringRemoval : ∀ now saved observed evidence job slot world owner info →
    DB.lookup slot world ≡ just (Owned.recordOf owner (Owned.registration info)) →
    owner ≡ Outcomes.targetOwner selection →
    Pending.pending (Outcomes.targetOwner selection) world ≡ true →
    DB.execute (update now (verifiedSame saved observed evidence) job slot) world ≡ (inspected , world)
  noReactivationDuringRemoval now saved observed evidence job slot world owner info found same activeRemoval
    rewrite found | same with Outcomes.ownerEqual (Outcomes.targetOwner selection) (Outcomes.targetOwner selection)
  ... | no impossible = ⊥-elim (impossible refl)
  ... | yes identical rewrite removalFenceHeld saved observed evidence info world activeRemoval | activeRemoval = refl
