{-# OPTIONS --safe #-}
-- Fresh registration reserves typed identity and immutable creation policy.
-- Schema preparation and first indexing remain distinct accepted operations.
module Muninn.RegistryCreation where

import Muninn.OwnedState as O
import Muninn.RepositoryIdentity as Identity
import Muninn.RepositoryDiscovery as Discovery
import Muninn.IdentityCheckpoint as Checkpoint
import Muninn.Config as Config
import Muninn.Worktree as W
import Muninn.Types as T
import Muninn.ArtifactIdentity as Equal
import Muninn.ExclusionOutcomes as E
import Muninn.RecordAllocation as Allocation
import Muninn.CleanupAdmissionStorage as Insert
import Muninn.CleanupStorage as Storage
import Muninn.ReceiptLedger as Ledger
import Muninn.ReceiptTypes as R
import Muninn.CatalogInputs as I
import Muninn.RequestIdentity as Meaning
import Muninn.Dialogue as D
import Muninn.ViewPublication as Frames
open import Data.Nat using (ℕ; suc; _≟_)
open import Data.Nat.Properties using (<-irrefl)
open import Data.Bool using (Bool; true; false; not; _∨_)
open import Data.String using (String)
import Data.String as String
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
module DB = O.DB
module Exec = O.Execution

owners : O.World → List ℕ
owners [] = []
owners ((key , O.recordOf O.installation value) ∷ rest) = owners rest
owners ((key , O.recordOf (O.family family) value) ∷ rest) = family ∷ owners rest

reserved : O.World → List ℕ
reserved world = Insert.reserved world ++ owners world

ownerId : O.World → ℕ
ownerId world = suc (Allocation.largest (reserved world))

fresh : ∀ world → Insert.Fresh world (ownerId world)
fresh world present = <-irrefl refl (Allocation.memberBound (reserved world) (ownerId world) (∈-++⁺ˡ present))

ownerMember : ∀ world key value family → (key , value) ∈ world → O.owner value ≡ O.family family → family ∈ owners world
ownerMember ((key , O.recordOf O.installation value) ∷ rest) .key .(O.recordOf O.installation value) family (here refl) ()
ownerMember ((key , O.recordOf (O.family family) value) ∷ rest) .key .(O.recordOf (O.family family) value) .family (here refl) refl = here refl
ownerMember ((first , O.recordOf O.installation value) ∷ rest) key stored family (there present) owned = ownerMember rest key stored family present owned
ownerMember ((first , O.recordOf (O.family previous) value) ∷ rest) key stored family (there present) owned = there (ownerMember rest key stored family present owned)

freshOwner : ∀ world key value → (key , value) ∈ world → O.owner value ≢ O.family (ownerId world)
freshOwner world key value present same = <-irrefl refl
  (Allocation.memberBound (reserved world) (ownerId world) (∈-++⁺ʳ (Insert.reserved world) (ownerMember world key value _ present same)))

freshFrame : ∀ world slot value → Insert.Fresh world slot → O.kind (O.body value) ≢ O.receiptK → Ledger.ReceiptFrame world (DB.write slot value world)
freshFrame world slot value unused nonReceipt key owner receiptData =
  Insert.oldLookup world slot value unused key _ , backward
  where
  backward : DB.lookup key (DB.write slot value world) ≡ just (O.recordOf owner (O.receipt receiptData)) →
    DB.lookup key world ≡ just (O.recordOf owner (O.receipt receiptData))
  backward found with slot ≟ key
  ... | yes refl = ⊥-elim (nonReceipt (cong (λ row → O.kind (O.body row)) (just-injective (trans (sym (DB.writeVisible slot value world)) found))))
  ... | no different = trans (sym (DB.writePreservesOther slot key value world different)) found

record Candidate : Set where
  constructor candidate
  field family : Identity.FamilyBinding
        checkout : Identity.CheckoutBinding
        policy : Config.FamilyPolicy
        sameFamily : Config.FamilyPolicy.family policy ≡ Identity.FamilyBinding.id family
        gitSuspended : Bool

familyInfo : Candidate → O.RegistrationInfo
familyInfo proposed = record
  { id = Identity.FamilyBinding.id (Candidate.family proposed); identity = just (Candidate.family proposed); retired = false; legacyReadable = false
  ; indexingEnabled = false; creationCompleted = false; missingSince = nothing; metadata = "" }

checkoutInfo : Candidate → O.CheckoutInfo
checkoutInfo proposed = record
  { id = Identity.CheckoutBinding.id (Candidate.checkout proposed); incarnation = Identity.CheckoutBinding.incarnation (Candidate.checkout proposed)
  ; identity = just (Candidate.checkout proposed); retired = false; paused = false
  ; gitSuspended = Candidate.gitSuspended proposed; missingSince = nothing; metadata = "" }

-- Reservation cannot authorize first indexing, alter its chosen family ID, or
-- forget the frozen policy that preparation must complete.
reservationNeverStarts : ∀ proposed → O.RegistrationInfo.indexingEnabled (familyInfo proposed) ≡ false
reservationNeverStarts proposed = refl

reservationPending : ∀ proposed → O.RegistrationInfo.creationCompleted (familyInfo proposed) ≡ false
reservationPending proposed = refl

module Reserve (proposed : Candidate) (source : Identity.Observation) (ctx : D.Context)
  (confirmed : Discovery.NewFamilyConfirmation ctx source)
  (familySource : Candidate.family proposed ≡ Identity.newFamily (Identity.FamilyBinding.id (Candidate.family proposed)) source)
  (checkoutSource : Candidate.checkout proposed ≡ Identity.newCheckout (Identity.CheckoutBinding.id (Candidate.checkout proposed)) (Identity.CheckoutBinding.incarnation (Candidate.checkout proposed)) source)
  (checkpoint continuation : String) (guidance : String → D.Prompt) where
  familyBinding = Candidate.family proposed
  checkoutBinding = Candidate.checkout proposed

  associated : O.RegistrationInfo → Bool
  associated info with O.RegistrationInfo.identity info
  ... | nothing = false
  ... | just saved = does (Identity.familyAssociation? saved source)

  conflict : O.Record → Bool
  conflict (O.recordOf owner (O.registration info)) =
    does (Equal.FamilyId? (O.RegistrationInfo.id info) (Identity.FamilyBinding.id familyBinding)) ∨ associated info
  conflict (O.recordOf owner (O.checkout info)) =
    does (T.UUID.value (W.CheckoutId.value (O.CheckoutInfo.id info)) String.≟ T.UUID.value (W.CheckoutId.value (Identity.CheckoutBinding.id checkoutBinding))) ∨
    does (T.UUID.value (O.CheckoutInfo.incarnation info) String.≟ T.UUID.value (Identity.CheckoutBinding.incarnation checkoutBinding))
  conflict value = false

  allowed : O.World → Bool
  allowed world = not (E.anyRow (λ key value → conflict value) world)

  owner : O.World → O.Owner
  owner world = O.family (ownerId world)

  registration : O.World → O.Record
  registration world = O.recordOf (owner world) (O.registration (familyInfo proposed))
  registered : O.World → O.World
  registered world = DB.write (ownerId world) (registration world) world

  intentSlot : O.World → ℕ
  intentSlot world = Allocation.freshId (registered world)
  intentRow : O.World → O.Record
  intentRow world = O.recordOf (owner world) (O.creationIntent (Candidate.policy proposed))
  withIntent : O.World → O.World
  withIntent world = DB.write (intentSlot world) (intentRow world) (registered world)

  checkoutSlot : O.World → ℕ
  checkoutSlot world = Allocation.freshId (withIntent world)
  checkoutRow : O.World → O.Record
  checkoutRow world = O.recordOf (owner world) (O.checkout (checkoutInfo proposed))
  created : O.World → O.World
  created world = DB.write (checkoutSlot world) (checkoutRow world) (withIntent world)

  snapshot : O.World → DB.Transaction String
  snapshot world with allowed world
  ... | false = DB.abort continuation
  ... | true = DB.put (ownerId world) (registration world)
      (DB.put (intentSlot world) (intentRow world) (DB.put (checkoutSlot world) (checkoutRow world) (DB.commit checkpoint)))

  transaction : DB.Transaction String
  transaction = DB.scan snapshot

  frames : ∀ world → Ledger.ReceiptFrame world (created world)
  frames world = Frames.composeFrames world (registered world) (created world)
    (freshFrame world (ownerId world) (registration world) (fresh world) (λ ()))
    (Frames.composeFrames (registered world) (withIntent world) (created world)
      (freshFrame (registered world) (intentSlot world) (intentRow world) (Allocation.fresh (registered world)) (λ ()))
      (freshFrame (withIntent world) (checkoutSlot world) (checkoutRow world) (Allocation.fresh (withIntent world)) (λ ())))

  isolates : ∀ before result after → DB.evaluate transaction before ≡ DB.committed result after → Ledger.ReceiptFrame before after
  isolates before result after committed with allowed before
  ... | false with committed
  ...   | ()
  isolates before result after committed | true with committed
  ... | refl = frames before

  effect : Ledger.Effect
  effect = record { transaction = transaction; guidance = guidance; isolates = isolates }

  module Current (before : O.World) (valid : O.Admissible before) (free : allowed before ≡ true) where
    afterRegistration = registered before
    afterIntent = withIntent before
    afterCreation = created before

    performs : DB.evaluate transaction before ≡ DB.committed checkpoint afterCreation
    performs rewrite free = refl

    registrationValid : O.Admissible afterRegistration
    registrationValid = Insert.insertAdmissible before (ownerId before) (registration before) valid (fresh before) O.local All.[] All.[]
    intentValid : O.Admissible afterIntent
    intentValid = Insert.insertAdmissible afterRegistration (intentSlot before) (intentRow before) registrationValid (Allocation.fresh afterRegistration) O.local All.[] All.[]
    creationValid : O.Admissible afterCreation
    creationValid = Insert.insertAdmissible afterIntent (checkoutSlot before) (checkoutRow before) intentValid (Allocation.fresh afterIntent) O.local All.[] All.[]

    registrationVisible : DB.lookup (ownerId before) afterCreation ≡ just (registration before)
    registrationVisible = Insert.oldLookup afterIntent (checkoutSlot before) (checkoutRow before) (Allocation.fresh afterIntent) (ownerId before) _
      (Insert.oldLookup afterRegistration (intentSlot before) (intentRow before) (Allocation.fresh afterRegistration) (ownerId before) _
        (DB.writeVisible (ownerId before) (registration before) before))

    intentVisible : DB.lookup (intentSlot before) afterCreation ≡ just (intentRow before)
    intentVisible = Insert.oldLookup afterIntent (checkoutSlot before) (checkoutRow before) (Allocation.fresh afterIntent) (intentSlot before) _
      (DB.writeVisible (intentSlot before) (intentRow before) afterRegistration)

    checkoutVisible : DB.lookup (checkoutSlot before) afterCreation ≡ just (checkoutRow before)
    checkoutVisible = DB.writeVisible (checkoutSlot before) (checkoutRow before) afterIntent

    oldRecord : ∀ key value → DB.lookup key before ≡ just value → DB.lookup key afterCreation ≡ just value
    oldRecord key value found = Insert.oldLookup afterIntent (checkoutSlot before) (checkoutRow before) (Allocation.fresh afterIntent) key value
      (Insert.oldLookup afterRegistration (intentSlot before) (intentRow before) (Allocation.fresh afterRegistration) key value
        (Insert.oldLookup before (ownerId before) (registration before) (fresh before) key value found))

    module Run (requestInput : I.IntentInput I.register)
      (sourceMatches : proj₁ (I.Mutation.input requestInput) ≡ Identity.Observation.requested source)
      (requestedPolicy : proj₂ (I.Mutation.input requestInput) ≡ record
        { name = Config.FamilyPolicy.name (Candidate.policy proposed)
        ; index = Config.FamilyPolicy.index (Candidate.policy proposed)
        ; watcher = Config.FamilyPolicy.watcher (Candidate.policy proposed)
        ; embeddings = Config.FamilyPolicy.embeddings (Candidate.policy proposed) })
      (receiptSlot : ℕ) (progress : R.Work)
      (ctxMatches : D.Context.id ctx ≡ I.Mutation.operationId requestInput)
      (located : DB.lookup receiptSlot before ≡ just (Ledger.recordAt O.installation
        (R.active (Meaning.mutation Meaning.kRegister requestInput) refl progress)))
      (foundHere : Ledger.find (I.Mutation.operationId requestInput) before ≡ just (Ledger.found receiptSlot O.installation
        (R.active (Meaning.mutation Meaning.kRegister requestInput) refl progress))) where
      id = I.Mutation.operationId requestInput
      input = Meaning.mutation Meaning.kRegister requestInput
      change = Ledger.checkpoint []
      next = R.nextWork progress [] checkpoint
      oldReceipt = Ledger.recordAt {id = id} O.installation (R.active input refl progress)
      newReceipt = Ledger.recordAt {id = id} O.installation (R.active input refl next)
      after = DB.write receiptSlot newReceipt afterCreation
      request = Ledger.update id input (R.generation progress) change effect

      commits : DB.execute request before ≡ (Ledger.resume receiptSlot next , after)
      commits = Ledger.committedUpdate id input refl change effect receiptSlot O.installation progress before checkpoint afterCreation foundHere performs

      receiptInCreated : DB.lookup receiptSlot afterCreation ≡ just oldReceipt
      receiptInCreated = oldRecord receiptSlot oldReceipt located

      afterValid : O.Admissible after
      afterValid = Storage.writeAdmissible afterCreation receiptSlot oldReceipt newReceipt creationValid receiptInCreated refl refl tt (λ ref ())

      keepNew : ∀ key value → DB.lookup key afterCreation ≡ just value → O.kind (O.body value) ≢ O.receiptK → DB.lookup key after ≡ just value
      keepNew key value found nonReceipt = trans
        (DB.writePreservesOther receiptSlot key newReceipt afterCreation
          (Frames.lookupDistinct afterCreation receiptSlot oldReceipt key value receiptInCreated found (λ same → nonReceipt (sym same)))) found

      savedRegistration : DB.lookup (ownerId before) after ≡ just (registration before)
      savedRegistration = keepNew (ownerId before) _ registrationVisible (λ ())
      savedCreationIntent : DB.lookup (intentSlot before) after ≡ just (intentRow before)
      savedCreationIntent = keepNew (intentSlot before) _ intentVisible (λ ())
      savedCheckout : DB.lookup (checkoutSlot before) after ≡ just (checkoutRow before)
      savedCheckout = keepNew (checkoutSlot before) _ checkoutVisible (λ ())

      preservesExisting : ∀ key value → DB.lookup key before ≡ just value → O.kind (O.body value) ≢ O.receiptK → DB.lookup key after ≡ just value
      preservesExisting key value found nonReceipt = keepNew key value (oldRecord key value found) nonReceipt

      receiptWritten : Ledger.find id after ≡ just (Ledger.found receiptSlot O.installation (R.active input refl next))
      receiptWritten = Ledger.writtenReceiptVisible id receiptSlot O.installation (R.active input refl next) afterCreation

      retry : DB.execute request after ≡ (Ledger.resume receiptSlot next , after)
      retry = Ledger.staleStepSkipsEffect id input refl (R.generation progress) change effect receiptSlot O.installation next after receiptWritten
        (Ledger.nextGenerationDifferent (R.generation progress))

      boundary : ∀ observed → Exec.Interrupted (Exec.atomic request Exec.done) before observed → (observed ≡ before) ⊎ (observed ≡ after)
      boundary observed interrupted with Ledger.atomicBoundary request before observed interrupted
      ... | inj₁ same = inj₁ same
      ... | inj₂ same = inj₂ (trans same (cong proj₂ commits))

      completedAtomic : ∀ observed reply final → Exec.Completed (Exec.atomic request Exec.done) observed reply final → DB.execute request observed ≡ (reply , final)
      completedAtomic observed reply final (Exec.committed Exec.stop) = refl

      converges : ∀ observed reply final → Exec.Interrupted (Exec.atomic request Exec.done) before observed →
        Exec.Completed (Exec.atomic request Exec.done) observed reply final → final ≡ after
      converges observed reply final interrupted completed with boundary observed interrupted
      ... | inj₁ same = trans (sym (cong proj₂ (completedAtomic observed reply final completed)))
        (trans (cong (λ world → proj₂ (DB.execute request world)) same) (cong proj₂ commits))
      ... | inj₂ same = trans (sym (cong proj₂ (completedAtomic observed reply final completed)))
        (trans (cong (λ world → proj₂ (DB.execute request world)) same) (cong proj₂ retry))

      completes : ∀ world → Σ Ledger.Reply (λ reply → Σ O.World (λ final → Exec.Completed (Exec.atomic request Exec.done) world reply final))
      completes world = proj₁ (DB.execute request world) , proj₂ (DB.execute request world) , Exec.committed Exec.stop

      preservesFamilies : ∀ key family value → DB.lookup key before ≡ just value → O.owner value ≡ O.family family → DB.lookup key after ≡ just value
      preservesFamilies key family (O.recordOf .(O.family family) body) found refl = trans
        (DB.writePreservesOther receiptSlot key newReceipt afterCreation
          (Checkpoint.ownerDistinct before receiptSlot oldReceipt key (O.recordOf (O.family family) body) located found (λ ())))
        (oldRecord key (O.recordOf (O.family family) body) found)
