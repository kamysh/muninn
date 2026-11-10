{-# OPTIONS --safe #-}
-- Explicit first-start authorization, durable queue and checkpoint commit together.
module Muninn.FirstStart where
import Muninn.OwnedState as O
import Muninn.WorkQueue as Q
import Muninn.IndexControl as Control
import Muninn.StoredPolicy as Policy
import Muninn.CatalogInputs as I
import Muninn.RequestIdentity as N
import Muninn.ReceiptTypes as R
import Muninn.ReceiptLedger as L
import Muninn.RecordAllocation as Allocation
import Muninn.CleanupAdmissionStorage as Insert
import Muninn.CleanupStorage as Storage
import Muninn.IdentityCheckpoint as Checkpoint
import Muninn.RegistryCreation as Creation
import Muninn.RetirementControl as Frames
import Muninn.ViewPublication as Compose
import Muninn.ArtifactIdentity as Equal
import Muninn.ExclusionOutcomes as E
import Muninn.Dialogue as D
open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (true; false)
import Data.Bool as Bool
open import Data.List using ([])
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)
module DB = O.DB

module Family (family registrationSlot policyPointer : ℕ) (request : I.IntentInput I.start)
  (checkpoint continuation : String) (guidance : String → D.Prompt) where
  module Stored = Policy.Family family policyPointer
  owner = O.family family
  id = I.Mutation.operationId request
  input = N.mutation N.kStart request
  target = I.PolicyTarget.target (I.Mutation.input request)

  belongs : O.Record → Bool.Bool
  belongs (O.recordOf actualOwner (O.acceptedWork versions queuedWork)) =
    E.sameOwner actualOwner owner Bool.∧ does (L.sameId id (Q.Info.parent queuedWork))
  belongs (O.recordOf actualOwner (O.cleanupWork parent keys payload)) =
    E.sameOwner actualOwner owner Bool.∧ does (L.sameId id parent)
  belongs value = false

  alreadySaved : O.World → Bool.Bool
  alreadySaved world = E.anyRow (λ key value → belongs value) world

  record Ready (world : O.World) : Set where
    constructor ready
    field info : O.RegistrationInfo
          current : Stored.Saved world
          located : DB.lookup registrationSlot world ≡ just (O.recordOf owner (O.registration info))
          permission : Control.StartAuthority request info (Stored.Saved.info current)
          notRemoving : E.pendingRemovalFor owner world ≡ false
          noDuplicate : alreadySaved world ≡ false

  examine : ∀ world info current →
    DB.lookup registrationSlot world ≡ just (O.recordOf owner (O.registration info)) → Maybe (Ready world)
  examine world info current located with
    O.RegistrationInfo.creationCompleted info Bool.≟ true |
    O.RegistrationInfo.paused info Bool.≟ false |
    O.RegistrationInfo.retired info Bool.≟ false |
    Equal.FamilyId? (I.FamilyTarget.expectedFamily target) (O.RegistrationInfo.id info) |
    Equal.FamilyId? (O.PolicyVersionInfo.familyId (Stored.Saved.info current)) (O.RegistrationInfo.id info) |
    I.PolicyTarget.expectedRevision (I.Mutation.input request) ≟ O.PolicyVersionInfo.revision (Stored.Saved.info current) |
    E.pendingRemovalFor owner world Bool.≟ false |
    alreadySaved world Bool.≟ false
  ... | yes prepared | yes unpaused | yes active | yes matched | yes sameFamily | yes revision | yes notRemoving | yes noDuplicate =
    just (ready info current located (Control.authority prepared unpaused active matched sameFamily revision) notRemoving noDuplicate)
  ... | _ | _ | _ | _ | _ | _ | _ | _ = nothing

  fromRecord : ∀ world → Maybe (Stored.Saved world) →
    (value : Maybe O.Record) → DB.lookup registrationSlot world ≡ value → Maybe (Ready world)
  fromRecord world (just current) (just (O.recordOf actualOwner (O.registration info))) located with E.ownerEqual actualOwner owner
  ... | yes refl = examine world info current located
  ... | no other = nothing
  fromRecord world current value located = nothing

  observe : (world : O.World) → Maybe (Ready world)
  observe world = fromRecord world (Stored.observe world) (DB.lookup registrationSlot world) refl

  updated : ∀ {world} → Ready world → O.Record
  updated seen = O.recordOf owner (O.registration
    (Control.authorize request (Ready.info seen) (Stored.Saved.info (Ready.current seen)) (Ready.permission seen)))

  queue : O.Record
  queue = O.recordOf owner (O.acceptedWork [] (record
    { id = id; parent = id; job = I.reconcileFamily
    ; input = record { operationId = id; family = I.FamilyTarget.expectedFamily target }
    ; phase = Q.queued; generation = 0 }))

  middle : ∀ world → Ready world → O.World
  middle world seen = DB.write registrationSlot (updated seen) world

  changed : ∀ world → Ready world → O.World
  changed world seen = DB.write (Allocation.freshId (middle world seen)) queue (middle world seen)

  snapshot : ∀ world → Maybe (Ready world) → DB.Transaction String
  snapshot world nothing = DB.abort continuation
  snapshot world (just seen) = DB.put registrationSlot (updated seen)
    (DB.put (Allocation.freshId (middle world seen)) queue (DB.commit checkpoint))

  transaction : DB.Transaction String
  transaction = DB.scan (λ world → snapshot world (observe world))

  isolates : ∀ before result after → DB.evaluate transaction before ≡ DB.committed result after → L.ReceiptFrame before after
  isolates before result after committed with observe before
  ... | nothing with committed
  ...   | ()
  isolates before result after committed | just seen with committed
  ... | refl = Compose.composeFrames before (middle before seen) (changed before seen)
      (Frames.writeFrame before registrationSlot (O.recordOf owner (O.registration (Ready.info seen))) (updated seen)
        (Ready.located seen) (λ ()) (λ ()))
      (Creation.freshFrame (middle before seen) (Allocation.freshId (middle before seen)) queue
        (Allocation.fresh (middle before seen)) (λ ()))

  effect : L.Effect
  effect = record { transaction = transaction; guidance = guidance; isolates = isolates }

  module Current (before : O.World) (valid : O.Admissible before) (seen : Ready before)
    (observed : observe before ≡ just seen) where
    middleValid : O.Admissible (middle before seen)
    middleValid = Storage.writeAdmissible before registrationSlot (O.recordOf owner (O.registration (Ready.info seen)))
      (updated seen) valid (Ready.located seen) refl refl O.local (λ ref ())

    changedValid : O.Admissible (changed before seen)
    changedValid = Insert.insertAdmissible (middle before seen) (Allocation.freshId (middle before seen)) queue
      middleValid (Allocation.fresh (middle before seen)) O.local All.[] All.[]

    performs : DB.evaluate transaction before ≡ DB.committed checkpoint (changed before seen)
    performs rewrite observed = refl

    module Run (receiptSlot : ℕ) (progress : R.Work)
      (accepted : L.find id before ≡ just (L.found receiptSlot owner (R.active input refl progress)))
      (located : DB.lookup receiptSlot before ≡ just (L.recordAt {id = id} owner (R.active input refl progress))) where
      module Saved = Checkpoint.Run id input refl owner receiptSlot progress checkpoint effect before (changed before seen)
        changedValid accepted located performs
      open Saved public

      queueSaved : DB.lookup (Allocation.freshId (middle before seen)) after ≡ just queue
      queueSaved = preservesData (Allocation.freshId (middle before seen)) queue
        (DB.writeVisible (Allocation.freshId (middle before seen)) queue (middle before seen)) (λ ())

      authorizationSaved : DB.lookup registrationSlot after ≡ just (updated seen)
      authorizationSaved = preservesData registrationSlot (updated seen)
        (Insert.oldLookup (middle before seen) (Allocation.freshId (middle before seen)) queue
          (Allocation.fresh (middle before seen)) registrationSlot (updated seen)
          (DB.writeVisible registrationSlot (updated seen) before)) (λ ())
