{-# OPTIONS --safe #-}
-- Identity reconciliation reads the actual rows inside one DB transaction.
module Muninn.RepositoryRegistry where

import Muninn.OwnedState as O
import Muninn.RepositoryIdentity as Identity
import Muninn.RepositoryDiscovery as Discovery
import Muninn.RegistryCreation as Creation
import Muninn.IdentityCheckpoint as Checkpoint
import Muninn.ArtifactIdentity as Equal
import Muninn.ExclusionOutcomes as E
import Muninn.CleanupStorage as Storage
import Muninn.CleanupAdmissionStorage as Insert
import Muninn.RecordAllocation as Allocation
import Muninn.RetirementControl as Control
import Muninn.Retirement as Life
import Muninn.ViewPublication as Frames
import Muninn.ReceiptLedger as Ledger
import Muninn.ReceiptTypes as R
import Muninn.RequestIdentity as Meaning
import Muninn.CatalogInputs as I
import Muninn.Dialogue as D
import Muninn.Worktree as W
import Muninn.Types as T
open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (Bool; true; false; not; _∨_; _∧_)
open import Data.String using (String)
import Data.String as String
open import Data.List using ([])
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no; does)
open import Relation.Nullary.Decidable using (map′)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
module DB = O.DB

uuidEqual : ∀ (first second : T.UUID) → Dec (first ≡ second)
uuidEqual first second = map′ (λ { refl → refl }) (λ { refl → refl })
  (T.UUID.value first String.≟ T.UUID.value second)
checkoutEqual : ∀ (first second : W.CheckoutId) → Dec (first ≡ second)
checkoutEqual first second = map′ (λ { refl → refl }) (λ { refl → refl })
  (uuidEqual (W.CheckoutId.value first) (W.CheckoutId.value second))

module Family (ownerId familySlot : ℕ) (familyId : W.FamilyId)
  (source : Identity.Observation) (ctx : D.Context) where
  owner = O.family ownerId

  record Seen (world : O.World) : Set where
    constructor seen
    field info : O.RegistrationInfo
          binding : Identity.FamilyBinding
          located : DB.lookup familySlot world ≡ just (O.recordOf owner (O.registration info))
          named : O.RegistrationInfo.id info ≡ familyId
          bound : O.RegistrationInfo.identity info ≡ just binding
          bindingNamed : Identity.FamilyBinding.id binding ≡ familyId
          reuse : Discovery.FamilyReuse ctx binding source

  valueAt : ∀ world → (value : Maybe O.Record) → DB.lookup familySlot world ≡ value → Maybe (Seen world)
  valueAt world (just (O.recordOf actualOwner (O.registration info))) found with E.ownerEqual actualOwner owner
  ... | no other = nothing
  ... | yes refl with Equal.FamilyId? (O.RegistrationInfo.id info) familyId
  ...   | no other = nothing
  ...   | yes named with O.RegistrationInfo.identity info in bound
  ...     | nothing = nothing
  ...     | just binding with Equal.FamilyId? (Identity.FamilyBinding.id binding) familyId
  ...       | no other = nothing
  ...       | yes bindingNamed with Discovery.familyReuse ctx binding source
  ...         | nothing = nothing
  ...         | just reuse = just (seen info binding found named bound bindingNamed reuse)
  valueAt world value found = nothing

  observe : ∀ world → Maybe (Seen world)
  observe world = valueAt world (DB.lookup familySlot world) refl

  movedInfo : ∀ {world} → Seen world → O.RegistrationInfo
  movedInfo current = record (Life.registrationUpdate 0 Life.verifiedSame (Seen.info current))
    { identity = just (Discovery.familyAfter (Seen.reuse current)) }

  moved : ∀ {world} → Seen world → O.Record
  moved current = O.recordOf owner (O.registration (movedInfo current))

  keepsId : ∀ {world} (current : Seen world) → O.RegistrationInfo.id (movedInfo current) ≡ familyId
  keepsId current = Seen.named current
  keepsAuthorization : ∀ {world} (current : Seen world) →
    O.RegistrationInfo.indexingEnabled (movedInfo current) ≡ O.RegistrationInfo.indexingEnabled (Seen.info current)
  keepsAuthorization current = refl
  keepsKind : ∀ {world} (current : Seen world) →
    Identity.FamilyBinding.kind (Discovery.familyAfter (Seen.reuse current)) ≡ Identity.FamilyBinding.kind (Seen.binding current)
  keepsKind current = Discovery.familyAfterKind (Seen.reuse current)

  -- Positive association with another registered family wins over a proposed
  -- reassociation. Ask for corrected context rather than merging identities.
  otherFamily : ℕ → O.Record → Bool
  otherFamily key (O.recordOf actualOwner (O.registration info)) =
    not (does (key ≟ familySlot)) ∧
      (does (Equal.FamilyId? (O.RegistrationInfo.id info) familyId) ∨ associated (O.RegistrationInfo.identity info))
    where
    associated : Maybe Identity.FamilyBinding → Bool
    associated nothing = false
    associated (just binding) = does (Identity.familyAssociation? binding source)
  otherFamily key value = false

  noOtherFamily : O.World → Bool
  noOtherFamily world = not (E.anyRow otherFamily world)

  module Move (checkoutSlot : ℕ) (checkoutId : W.CheckoutId) (incarnation : T.UUID)
    (checkpoint continuation : String) (guidance : String → D.Prompt) where
    record Current (world : O.World) : Set where
      constructor current
      field family : Seen world
            info : O.CheckoutInfo
            binding : Identity.CheckoutBinding
            located : DB.lookup checkoutSlot world ≡ just (O.recordOf owner (O.checkout info))
            named : O.CheckoutInfo.id info ≡ checkoutId
            incarnationMatches : O.CheckoutInfo.incarnation info ≡ incarnation
            bound : O.CheckoutInfo.identity info ≡ just binding
            bindingNamed : Identity.CheckoutBinding.id binding ≡ checkoutId
            bindingIncarnation : Identity.CheckoutBinding.incarnation binding ≡ incarnation
            reuse : Discovery.CheckoutReuse ctx (Identity.FamilyBinding.kind (Seen.binding family)) binding source

    checkoutAt : ∀ world → Seen world → (value : Maybe O.Record) → DB.lookup checkoutSlot world ≡ value → Maybe (Current world)
    checkoutAt world family (just (O.recordOf actualOwner (O.checkout info))) found with E.ownerEqual actualOwner owner
    ... | no other = nothing
    ... | yes refl with checkoutEqual (O.CheckoutInfo.id info) checkoutId | uuidEqual (O.CheckoutInfo.incarnation info) incarnation
    ...   | no other | _ = nothing
    ...   | _ | no other = nothing
    ...   | yes named | yes incarnationMatches with O.CheckoutInfo.identity info in bound
    ...     | nothing = nothing
    ...     | just binding with checkoutEqual (Identity.CheckoutBinding.id binding) checkoutId | uuidEqual (Identity.CheckoutBinding.incarnation binding) incarnation
    ...       | no other | _ = nothing
    ...       | _ | no other = nothing
    ...       | yes bindingNamed | yes bindingIncarnation with Discovery.checkoutReuse ctx (Identity.FamilyBinding.kind (Seen.binding family)) binding source
    ...         | nothing = nothing
    ...         | just reuse = just (current family info binding found named incarnationMatches bound bindingNamed bindingIncarnation reuse)
    checkoutAt world family value found = nothing

    observeCheckout : ∀ world → Maybe (Current world)
    observeCheckout world with observe world
    ... | nothing = nothing
    ... | just family = checkoutAt world family (DB.lookup checkoutSlot world) refl

    otherCheckout : ℕ → Identity.Kind → O.Record → Bool
    otherCheckout key kind (O.recordOf actualOwner (O.checkout info)) =
      not (does (key ≟ checkoutSlot)) ∧
        (does (checkoutEqual (O.CheckoutInfo.id info) checkoutId) ∨
         does (uuidEqual (O.CheckoutInfo.incarnation info) incarnation) ∨ associated (O.CheckoutInfo.identity info))
      where
      associated : Maybe Identity.CheckoutBinding → Bool
      associated nothing = false
      associated (just binding) = does (Identity.checkoutAssociation? kind binding source)
    otherCheckout key kind value = false

    allowed : ∀ world → Current world → Bool
    allowed world selected = noOtherFamily world ∧ not (E.anyRow (λ key value → otherCheckout key (Identity.FamilyBinding.kind (Seen.binding (Current.family selected))) value) world)

    checkoutInfo : ∀ {world} → Current world → O.CheckoutInfo
    checkoutInfo selected = record (Life.checkoutUpdate 0 Life.verifiedSame (Current.info selected))
      { identity = just (Discovery.checkoutAfter (Current.reuse selected)) }
    checkoutRow : ∀ {world} → Current world → O.Record
    checkoutRow selected = O.recordOf owner (O.checkout (checkoutInfo selected))
    middle : ∀ world → Current world → O.World
    middle world selected = DB.write familySlot (moved (Current.family selected)) world
    changed : ∀ world → Current world → O.World
    changed world selected = DB.write checkoutSlot (checkoutRow selected) (middle world selected)

    snapshot : ∀ world → Maybe (Current world) → DB.Transaction String
    snapshot world nothing = DB.abort continuation
    snapshot world (just selected) with allowed world selected
    ... | false = DB.abort continuation
    ... | true = DB.put familySlot (moved (Current.family selected)) (DB.put checkoutSlot (checkoutRow selected) (DB.commit checkpoint))
    transaction : DB.Transaction String
    transaction = DB.scan (λ world → snapshot world (observeCheckout world))

    frame : ∀ world selected → Ledger.ReceiptFrame world (changed world selected)
    frame world selected = Frames.composeFrames world (middle world selected) (changed world selected)
      (Control.writeFrame world familySlot _ _ (Seen.located (Current.family selected)) (λ ()) (λ ()))
      (Control.writeFrame (middle world selected) checkoutSlot _ _
        (trans (DB.writePreservesOther familySlot checkoutSlot (moved (Current.family selected)) world
          (Frames.lookupDistinct world familySlot _ checkoutSlot _ (Seen.located (Current.family selected)) (Current.located selected) (λ ()))) (Current.located selected))
        (λ ()) (λ ()))

    isolates : ∀ world result after → DB.evaluate transaction world ≡ DB.committed result after → Ledger.ReceiptFrame world after
    isolates world result after committed with observeCheckout world
    ... | nothing with committed
    ...   | ()
    isolates world result after committed | just selected with allowed world selected
    ... | false with committed
    ...   | ()
    isolates world result after committed | just selected | true with committed
    ... | refl = frame world selected
    effect : Ledger.Effect
    effect = record { transaction = transaction; guidance = guidance; isolates = isolates }

    module Ready (before : O.World) (valid : O.Admissible before) (selected : Current before)
      (seenNow : observeCheckout before ≡ just selected) (free : allowed before selected ≡ true) where
      familyOld = O.recordOf owner (O.registration (Seen.info (Current.family selected)))
      checkoutOld = O.recordOf owner (O.checkout (Current.info selected))
      middleWorld = middle before selected
      changedWorld = changed before selected
      distinct : familySlot ≢ checkoutSlot
      distinct = Frames.lookupDistinct before familySlot familyOld checkoutSlot checkoutOld (Seen.located (Current.family selected)) (Current.located selected) (λ ())
      checkoutInMiddle : DB.lookup checkoutSlot middleWorld ≡ just checkoutOld
      checkoutInMiddle = trans (DB.writePreservesOther familySlot checkoutSlot (moved (Current.family selected)) before distinct) (Current.located selected)
      middleValid : O.Admissible middleWorld
      middleValid = Storage.writeAdmissible before familySlot familyOld (moved (Current.family selected)) valid (Seen.located (Current.family selected)) refl refl O.local (λ ref ())
      changedValid : O.Admissible changedWorld
      changedValid = Storage.writeAdmissible middleWorld checkoutSlot checkoutOld (checkoutRow selected) middleValid checkoutInMiddle refl refl O.local (λ ref ())
      performs : DB.evaluate transaction before ≡ DB.committed checkpoint changedWorld
      performs rewrite seenNow | free = refl
      registrationVisible : DB.lookup familySlot changedWorld ≡ just (moved (Current.family selected))
      registrationVisible = trans (DB.writePreservesOther checkoutSlot familySlot (checkoutRow selected) middleWorld (λ same → distinct (sym same))) (DB.writeVisible familySlot (moved (Current.family selected)) before)
      checkoutVisible : DB.lookup checkoutSlot changedWorld ≡ just (checkoutRow selected)
      checkoutVisible = DB.writeVisible checkoutSlot (checkoutRow selected) middleWorld
      preserves : ∀ key → key ≢ familySlot → key ≢ checkoutSlot → DB.lookup key changedWorld ≡ DB.lookup key before
      preserves key familyDifferent checkoutDifferent = trans
        (DB.writePreservesOther checkoutSlot key (checkoutRow selected) middleWorld (λ same → checkoutDifferent (sym same)))
        (DB.writePreservesOther familySlot key (moved (Current.family selected)) before (λ same → familyDifferent (sym same)))

      module Run (id : I.OperationId) (input : Meaning.Meaning) (names : R.Names id input)
        (receiptSlot : ℕ) (progress : R.Work)
        (found : Ledger.find id before ≡ just (Ledger.found receiptSlot owner (R.active input names progress)))
        (located : DB.lookup receiptSlot before ≡ just (Ledger.recordAt owner (R.active input names progress))) where
        keepBefore = preserves
        module Seal = Checkpoint.Run id input names owner receiptSlot progress checkpoint effect before changedWorld changedValid found located performs
        open Seal public
        savedRegistration : DB.lookup familySlot after ≡ just (moved (Current.family selected))
        savedRegistration = preservesData familySlot _ registrationVisible (λ ())
        savedCheckout : DB.lookup checkoutSlot after ≡ just (checkoutRow selected)
        savedCheckout = preservesData checkoutSlot _ checkoutVisible (λ ())

        otherFamilies : ∀ key value → O.owner value ≢ owner → DB.lookup key before ≡ just value → DB.lookup key after ≡ just value
        otherFamilies key value foreign found = Seal.preserves key value
          (trans (keepBefore key
            (λ same → Checkpoint.ownerDistinct before familySlot familyOld key value (Seen.located (Current.family selected)) found (λ owned → foreign (sym owned)) (sym same))
            (λ same → Checkpoint.ownerDistinct before checkoutSlot checkoutOld key value (Current.located selected) found (λ owned → foreign (sym owned)) (sym same))) found)
          (λ same → Checkpoint.ownerDistinct before receiptSlot _ key value located found (λ owned → foreign (sym owned)) (sym same))

  module Add (binding : Identity.CheckoutBinding)
    (fromSource : binding ≡ Identity.newCheckout (Identity.CheckoutBinding.id binding) (Identity.CheckoutBinding.incarnation binding) source)
    (gitSuspended : Bool) (checkpoint continuation : String) (guidance : String → D.Prompt) where
    info : O.CheckoutInfo
    info = record { id = Identity.CheckoutBinding.id binding; incarnation = Identity.CheckoutBinding.incarnation binding
      ; identity = just binding; retired = false; paused = false; gitSuspended = gitSuspended; missingSince = nothing; metadata = "" }
    row = O.recordOf owner (O.checkout info)

    conflict : Identity.Kind → O.Record → Bool
    conflict kind (O.recordOf actualOwner (O.checkout info)) =
      does (checkoutEqual (O.CheckoutInfo.id info) (Identity.CheckoutBinding.id binding)) ∨
      does (uuidEqual (O.CheckoutInfo.incarnation info) (Identity.CheckoutBinding.incarnation binding)) ∨ associated (O.CheckoutInfo.identity info)
      where
      associated : Maybe Identity.CheckoutBinding → Bool
      associated nothing = false
      associated (just previous) = does (Identity.checkoutAssociation? kind previous source)
    conflict kind value = false

    allowed : ∀ world → Seen world → Bool
    allowed world selected = noOtherFamily world ∧ not (E.anyRow (λ key value → conflict (Identity.FamilyBinding.kind (Seen.binding selected)) value) world)
    middle : ∀ world → Seen world → O.World
    middle world selected = DB.write familySlot (moved selected) world
    slot : ∀ world → Seen world → ℕ
    slot world selected = Allocation.freshId (middle world selected)
    changed : ∀ world → Seen world → O.World
    changed world selected = DB.write (slot world selected) row (middle world selected)

    snapshot : ∀ world → Maybe (Seen world) → DB.Transaction String
    snapshot world nothing = DB.abort continuation
    snapshot world (just selected) with allowed world selected
    ... | false = DB.abort continuation
    ... | true = DB.put familySlot (moved selected) (DB.put (slot world selected) row (DB.commit checkpoint))
    transaction : DB.Transaction String
    transaction = DB.scan (λ world → snapshot world (observe world))
    frame : ∀ world selected → Ledger.ReceiptFrame world (changed world selected)
    frame world selected = Frames.composeFrames world (middle world selected) (changed world selected)
      (Control.writeFrame world familySlot _ _ (Seen.located selected) (λ ()) (λ ()))
      (Creation.freshFrame (middle world selected) (slot world selected) row (Allocation.fresh (middle world selected)) (λ ()))
    isolates : ∀ world result after → DB.evaluate transaction world ≡ DB.committed result after → Ledger.ReceiptFrame world after
    isolates world result after committed with observe world
    ... | nothing with committed
    ...   | ()
    isolates world result after committed | just selected with allowed world selected
    ... | false with committed
    ...   | ()
    isolates world result after committed | just selected | true with committed
    ... | refl = frame world selected
    effect : Ledger.Effect
    effect = record { transaction = transaction; guidance = guidance; isolates = isolates }

    module Ready (before : O.World) (valid : O.Admissible before) (selected : Seen before)
      (seenNow : observe before ≡ just selected) (free : allowed before selected ≡ true) where
      middleWorld = middle before selected
      changedWorld = changed before selected
      old = O.recordOf owner (O.registration (Seen.info selected))
      middleValid : O.Admissible middleWorld
      middleValid = Storage.writeAdmissible before familySlot old (moved selected) valid (Seen.located selected) refl refl O.local (λ ref ())
      changedValid : O.Admissible changedWorld
      changedValid = Insert.insertAdmissible middleWorld (slot before selected) row middleValid (Allocation.fresh middleWorld) O.local All.[] All.[]
      performs : DB.evaluate transaction before ≡ DB.committed checkpoint changedWorld
      performs rewrite seenNow | free = refl
      checkoutVisible : DB.lookup (slot before selected) changedWorld ≡ just row
      checkoutVisible = DB.writeVisible (slot before selected) row middleWorld
      registrationVisible : DB.lookup familySlot changedWorld ≡ just (moved selected)
      registrationVisible = Insert.oldLookup middleWorld (slot before selected) row (Allocation.fresh middleWorld) familySlot _ (DB.writeVisible familySlot (moved selected) before)
      preserves : ∀ key value → key ≢ familySlot → DB.lookup key before ≡ just value → DB.lookup key changedWorld ≡ just value
      preserves key value different found = Insert.oldLookup middleWorld (slot before selected) row (Allocation.fresh middleWorld) key value
        (trans (DB.writePreservesOther familySlot key (moved selected) before (λ same → different (sym same))) found)

      module Run (id : I.OperationId) (input : Meaning.Meaning) (names : R.Names id input)
        (receiptSlot : ℕ) (progress : R.Work)
        (found : Ledger.find id before ≡ just (Ledger.found receiptSlot owner (R.active input names progress)))
        (located : DB.lookup receiptSlot before ≡ just (Ledger.recordAt owner (R.active input names progress))) where
        keepBefore = preserves
        module Seal = Checkpoint.Run id input names owner receiptSlot progress checkpoint effect before changedWorld changedValid found located performs
        open Seal public
        savedRegistration : DB.lookup familySlot after ≡ just (moved selected)
        savedRegistration = preservesData familySlot _ registrationVisible (λ ())
        savedCheckout : DB.lookup (slot before selected) after ≡ just row
        savedCheckout = preservesData (slot before selected) row checkoutVisible (λ ())

        otherFamilies : ∀ key value → O.owner value ≢ owner → DB.lookup key before ≡ just value → DB.lookup key after ≡ just value
        otherFamilies key value foreign found = Seal.preserves key value
          (keepBefore key value
            (λ same → Checkpoint.ownerDistinct before familySlot old key value (Seen.located selected) found (λ owned → foreign (sym owned)) (sym same)) found)
          (λ same → Checkpoint.ownerDistinct before receiptSlot _ key value located found (λ owned → foreign (sym owned)) (sym same))
