{-# OPTIONS --safe #-}
-- Independent removal outcomes over the whole logical application world.
module Muninn.RemovalOutcome where

import Muninn.ApplicationWorld as A
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)

module Model (Family Key Value RequestId Request Result : Set)
  (sameFamily : (a b : Family) → Dec (a ≡ b))
  (installationOwns : Value → Family → Set)
  (requestOwns : Request → Family → Set)
  (resultOwns : Result → Family → Set)
  (installationKind : Value → A.Kind)
  (installationOwns? : (value : Value) (family : Family) → Dec (installationOwns value family))
  (requestOwns? : (request : Request) (family : Family) → Dec (requestOwns request family))
  (resultOwns? : (result : Result) (family : Family) → Dec (resultOwns result family)) where

  World = A.World Family Key Value RequestId Request Result
  Receipt = A.Receipt Family Request Result

  clearInstallation : Family → Maybe Value → Maybe Value
  clearInstallation family nothing = nothing
  clearInstallation family (just value) with installationOwns? value family
  ... | yes _ = nothing
  ... | no _ = just value

  -- A used-ID marker survives without retaining any request or result content.
  clearReceipt : Family → Maybe Receipt → Maybe Receipt
  clearReceipt family nothing = nothing
  clearReceipt family (just A.used) = just A.used
  clearReceipt family (just (A.active owners request)) = just (A.active owners request)
  clearReceipt family (just (A.completed owners request result)) with requestOwns? request family | resultOwns? result family
  ... | yes _ | _ = just A.used
  ... | no _ | yes _ = just A.used
  ... | no _ | no _ = just (A.completed owners request result)

  -- The policy is fixed here, independently of the operation script.
  preservedKind : A.Kind → Bool
  preservedKind A.policyHistory = true
  preservedKind A.policyCurrent = true
  preservedKind A.note = true
  preservedKind A.notePosting = true
  preservedKind A.noteVector = true
  preservedKind A.registration = false
  preservedKind A.checkout = false
  preservedKind A.fileVersion = false
  preservedKind A.fileBinding = false
  preservedKind A.chunk = false
  preservedKind A.posting = false
  preservedKind A.vector = false
  preservedKind A.symbol = false
  preservedKind A.edge = false
  preservedKind A.graphSnapshot = false
  preservedKind A.legacy = false
  preservedKind A.staging = false
  preservedKind A.pendingWork = false
  preservedKind A.reader = false
  preservedKind A.continuation = false
  preservedKind A.schemaResource = false
  preservedKind A.graphResource = false
  preservedKind A.usage = true

  clearCodeEntry : Maybe (A.Entry Key Value) → Maybe (A.Entry Key Value)
  clearCodeEntry nothing = nothing
  clearCodeEntry (just entry) with preservedKind (A.Entry.kind entry)
  ... | true = just entry
  ... | false = nothing

  clearCodeInstallation : Family → Maybe Value → Maybe Value
  clearCodeInstallation family nothing = nothing
  clearCodeInstallation family (just value) with installationOwns? value family
  ... | no _ = just value
  ... | yes _ with preservedKind (installationKind value)
  ...   | true = just value
  ...   | false = nothing

  unregister : Family → World → World
  unregister family world = record
    { familyData = λ other key → selectFamily family other (A.World.familyData world other key)
    ; installationData = λ key → clearCodeInstallation family (A.World.installationData world key)
    ; receipts = λ id → clearReceipt family (A.World.receipts world id) }
    where
    selectFamily : Family → Family → Maybe (A.Entry Key Value) → Maybe (A.Entry Key Value)
    selectFamily target other previous with sameFamily target other
    ... | yes _ = clearCodeEntry previous
    ... | no _ = previous

  unregisterKeepsNotesAndSettings : ∀ family world key entry →
    A.World.familyData world family key ≡ just entry → preservedKind (A.Entry.kind entry) ≡ true →
    A.World.familyData (unregister family world) family key ≡ just entry
  unregisterKeepsNotesAndSettings family world key entry found kept with sameFamily family family
  ... | no different = ⊥-elim (different refl)
  ... | yes _ rewrite found | kept = refl

  unregisterRemovesCode : ∀ family world key entry →
    A.World.familyData world family key ≡ just entry → preservedKind (A.Entry.kind entry) ≡ false →
    A.World.familyData (unregister family world) family key ≡ nothing
  unregisterRemovesCode family world key entry found removed with sameFamily family family
  ... | no different = ⊥-elim (different refl)
  ... | yes _ rewrite found | removed = refl

  unregisterPreservesOtherFamily : ∀ family other world key → other ≢ family →
    A.World.familyData (unregister family world) other key ≡ A.World.familyData world other key
  unregisterPreservesOtherFamily family other world key different with sameFamily family other
  ... | yes same = ⊥-elim (different (sym same))
  ... | no _ = refl

  forget : Family → World → World
  forget family world = record
    { familyData = λ other key → clearFamily family other (A.World.familyData world other key)
    ; installationData = λ key → clearInstallation family (A.World.installationData world key)
    ; receipts = λ id → clearReceipt family (A.World.receipts world id) }
    where
    clearFamily : Family → Family → Maybe (A.Entry Key Value) → Maybe (A.Entry Key Value)
    clearFamily target other previous with sameFamily target other
    ... | yes _ = nothing
    ... | no _ = previous

  familyGone : ∀ family world key → A.World.familyData (forget family world) family key ≡ nothing
  familyGone family world key with sameFamily family family
  ... | yes _ = refl
  ... | no different = ⊥-elim (different refl)

  otherFamilyPreserved : ∀ family other world key → other ≢ family →
    A.World.familyData (forget family world) other key ≡ A.World.familyData world other key
  otherFamilyPreserved family other world key different with sameFamily family other
  ... | yes same = ⊥-elim (different (sym same))
  ... | no _ = refl

  installationGone : ∀ family world key value →
    A.World.installationData (forget family world) key ≡ just value → ¬ installationOwns value family
  installationGone family world key value found with A.World.installationData world key
  ... | nothing with found
  ...   | ()
  installationGone family world key value found | just stored with installationOwns? stored family
  ... | yes _ with found
  ...   | ()
  installationGone family world key value found | just stored | no notOwned with found
  ...   | refl = notOwned

  -- Cleanup waits for active requests; it never discards unfinished work.
  NoActiveTarget : Family → World → Set
  NoActiveTarget family world = ∀ id owners request →
    A.World.receipts world id ≡ just (A.active owners request) → ¬ requestOwns request family

  activeGone : ∀ family world → NoActiveTarget family world → ∀ id owners request →
    A.World.receipts (forget family world) id ≡ just (A.active owners request) → ¬ requestOwns request family
  activeGone family world noActive id owners request found with A.World.receipts world id in original
  ... | nothing with found
  ...   | ()
  activeGone family world noActive id owners request found | just A.used with found
  ...   | ()
  activeGone family world noActive id owners request found | just (A.active storedOwners storedRequest) with found
  ...   | refl = noActive id owners request original
  activeGone family world noActive id owners request found | just (A.completed storedOwners storedRequest result) with requestOwns? storedRequest family | resultOwns? result family
  ... | yes _ | _ with found
  ...   | ()
  activeGone family world noActive id owners request found | just (A.completed storedOwners storedRequest result) | no _ | yes _ with found
  ...   | ()
  activeGone family world noActive id owners request found | just (A.completed storedOwners storedRequest result) | no _ | no _ with found
  ...   | ()

  completedGone : ∀ family world id owners request result →
    A.World.receipts (forget family world) id ≡ just (A.completed owners request result) →
    ¬ (requestOwns request family ⊎ resultOwns result family)
  completedGone family world id owners request result found with A.World.receipts world id
  ... | nothing with found
  ...   | ()
  completedGone family world id owners request result found | just A.used with found
  ...   | ()
  completedGone family world id owners request result found | just (A.active storedOwners storedRequest) with found
  ... | ()
  completedGone family world id owners request result found | just (A.completed storedOwners storedRequest storedResult) with requestOwns? storedRequest family | resultOwns? storedResult family
  ... | yes _ | _ with found
  ...   | ()
  completedGone family world id owners request result found | just (A.completed storedOwners storedRequest storedResult) | no _ | yes _ with found
  ...   | ()
  completedGone family world id owners request result found | just (A.completed storedOwners storedRequest storedResult) | no noRequest | no noResult with found
  ...   | refl = λ { (inj₁ owned) → noRequest owned; (inj₂ owned) → noResult owned }

  complete : ∀ family world → NoActiveTarget family world → A.NoFamilyData installationOwns requestOwns resultOwns family (forget family world)
  complete family world noActive = familyGone family world , installationGone family world , activeGone family world noActive , completedGone family world

  markerPreserved : ∀ family world id → A.World.receipts world id ≡ just A.used →
    A.World.receipts (forget family world) id ≡ just A.used
  markerPreserved family world id found rewrite found = refl

  -- If any part of a saved result belongs to the forgotten family, discard the
  -- entire result; do not keep the parts associated with other families.
  sharedResultCleared : ∀ family world id owners request result →
    A.World.receipts world id ≡ just (A.completed owners request result) → resultOwns result family →
    A.World.receipts (forget family world) id ≡ just A.used
  sharedResultCleared family world id owners request result found owned rewrite found
    with requestOwns? request family | resultOwns? result family
  ... | yes _ | _ = refl
  ... | no _ | yes _ = refl
  ... | no _ | no different = ⊥-elim (different owned)

  unrelatedInstallationPreserved : ∀ family world key →
    (∀ value → A.World.installationData world key ≡ just value → ¬ installationOwns value family) →
    A.World.installationData (forget family world) key ≡ A.World.installationData world key
  unrelatedInstallationPreserved family world key unrelated with A.World.installationData world key in found
  ... | nothing = refl
  ... | just value with installationOwns? value family
  ...   | yes owned = ⊥-elim (unrelated value refl owned)
  ...   | no _ = refl

  unrelatedReceiptsPreserved : ∀ family world id →
    (∀ owners request → A.World.receipts world id ≡ just (A.active owners request) → ¬ requestOwns request family) →
    (∀ owners request result → A.World.receipts world id ≡ just (A.completed owners request result) →
      ¬ (requestOwns request family ⊎ resultOwns result family)) →
    A.World.receipts (forget family world) id ≡ A.World.receipts world id
  unrelatedReceiptsPreserved family world id activeUnrelated completedUnrelated with A.World.receipts world id in found
  ... | nothing = refl
  ... | just A.used = refl
  ... | just (A.active owners request) = refl
  unrelatedReceiptsPreserved family world id activeUnrelated completedUnrelated | just (A.completed owners request result) with requestOwns? request family | resultOwns? result family
  ... | yes owned | _ = ⊥-elim (completedUnrelated owners request result refl (inj₁ owned))
  ... | no _ | yes owned = ⊥-elim (completedUnrelated owners request result refl (inj₂ owned))
  ... | no _ | no _ = refl

  -- Final cleanup is idempotent: a lost acknowledgement does not repeat data.
  installationRetry : ∀ family previous → clearInstallation family (clearInstallation family previous) ≡ clearInstallation family previous
  installationRetry family nothing = refl
  installationRetry family (just value) with installationOwns? value family
  ... | yes _ = refl
  ... | no notOwned with installationOwns? value family
  ...   | yes owned = ⊥-elim (notOwned owned)
  ...   | no _ = refl

  receiptRetry : ∀ family previous → clearReceipt family (clearReceipt family previous) ≡ clearReceipt family previous
  receiptRetry family nothing = refl
  receiptRetry family (just A.used) = refl
  receiptRetry family (just (A.active owners request)) = refl
  receiptRetry family (just (A.completed owners request result)) with requestOwns? request family | resultOwns? result family
  ... | yes _ | _ = refl
  ... | no _ | yes _ = refl
  ... | no notRequest | no notResult with requestOwns? request family | resultOwns? result family
  ...   | yes owned | _ = ⊥-elim (notRequest owned)
  ...   | no _ | yes owned = ⊥-elim (notResult owned)
  ...   | no _ | no _ = refl

  familyRetry : ∀ family other world key →
    A.World.familyData (forget family (forget family world)) other key ≡
      A.World.familyData (forget family world) other key
  familyRetry family other world key with sameFamily family other
  ... | yes _ = refl
  ... | no _ = refl

  installationWorldRetry : ∀ family world key →
    A.World.installationData (forget family (forget family world)) key ≡
      A.World.installationData (forget family world) key
  installationWorldRetry family world key = installationRetry family (A.World.installationData world key)

  receiptWorldRetry : ∀ family world id →
    A.World.receipts (forget family (forget family world)) id ≡
      A.World.receipts (forget family world) id
  receiptWorldRetry family world id = receiptRetry family (A.World.receipts world id)

-- The executable state-machine goal is fixed over the resulting world, not
-- over the statements used to reach it.
import Muninn.OwnedState as O
import Muninn.RepositoryHistory as History
import Muninn.HistoryOwnership as Ownership
open import Data.Nat using (ℕ)
open import Data.List.Relation.Unary.All using (All)

ForgetGoal : ℕ → O.World → History.History → Set
ForgetGoal family world records =
  (∀ slot value → O.DB.lookup slot world ≡ just value → O.owner value ≢ O.family family) ×
  ((∀ slot value → O.DB.lookup slot world ≡ just value → Ownership.owns family value ≡ false) ×
  (All (λ item → History.mentions family (History.Entry.owners item) ≡ false) (History.usage records) ×
  (All (λ item → History.mentions family (History.Entry.owners item) ≡ false) (History.logs records) ×
   All (λ item → History.mentions family (History.Entry.owners item) ≡ false) (History.buffered records))))
