{-# OPTIONS --safe #-}
-- Search scope is established by the existing identity/clarification protocol.
module Muninn.SearchTarget where
import Muninn.OwnedState as O
import Muninn.WorkQueue as Q
import Muninn.RepositoryIdentity as Identity
import Muninn.RepositoryDiscovery as Discovery
import Muninn.Dialogue as D
import Muninn.CatalogInputs as I
import Muninn.RequestCodecs as Codecs
import Muninn.Canonical as Canonical
import Muninn.ExclusionOutcomes as E
open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
module DB = O.DB

familyReuse : ∀ ctx binding observed → Discovery.FamilyDecision ctx binding observed →
  Maybe (Identity.FamilyAssociation binding observed ⊎ Discovery.FamilyConfirmation ctx binding observed)
familyReuse ctx binding observed (Discovery.reuseFamily same) = just (inj₁ same)
familyReuse ctx binding observed (Discovery.reuseClarifiedFamily same) = just (inj₂ same)
familyReuse ctx binding observed _ = nothing

checkoutReuse : ∀ ctx kind binding observed → Discovery.CheckoutDecision ctx kind binding observed →
  Maybe (Identity.CheckoutAssociation kind binding observed ⊎ Discovery.CheckoutConfirmation ctx kind binding observed)
checkoutReuse ctx kind binding observed (Discovery.reuseCheckout same) = just (inj₁ same)
checkoutReuse ctx kind binding observed (Discovery.reuseClarifiedCheckout same) = just (inj₂ same)
checkoutReuse ctx kind binding observed _ = nothing

module Family (family registrationSlot checkoutSlot : ℕ) (requiredLocation : I.Locator)
  (ctx : D.Context) (observed : Identity.Observation) where
  owner = O.family family

  record Target (world : O.World) : Set where
    constructor target
    field registration : O.RegistrationInfo
          checkout : O.CheckoutInfo
          familySource : Identity.FamilyBinding
          checkoutSource : Identity.CheckoutBinding
          familyAt : DB.lookup registrationSlot world ≡ just (O.recordOf owner (O.registration registration))
          checkoutAt : DB.lookup checkoutSlot world ≡ just (O.recordOf owner (O.checkout checkout))
          savedFamily : O.RegistrationInfo.identity registration ≡ just familySource
          savedCheckout : O.CheckoutInfo.identity checkout ≡ just checkoutSource
          familyId : Identity.FamilyBinding.id familySource ≡ O.RegistrationInfo.id registration
          checkoutId : Identity.CheckoutBinding.id checkoutSource ≡ O.CheckoutInfo.id checkout
          incarnation : Identity.CheckoutBinding.incarnation checkoutSource ≡ O.CheckoutInfo.incarnation checkout
          requested : requiredLocation ≡ Identity.Observation.requested observed
          currentRoot : Identity.CheckoutBinding.root checkoutSource ≡ Identity.Observation.root observed
          familyEvidence : Identity.FamilyAssociation familySource observed ⊎ Discovery.FamilyConfirmation ctx familySource observed
          checkoutEvidence : Identity.CheckoutAssociation (Identity.FamilyBinding.kind familySource) checkoutSource observed ⊎
            Discovery.CheckoutConfirmation ctx (Identity.FamilyBinding.kind familySource) checkoutSource observed

  examine : ∀ world registration checkout familySource checkoutSource →
    DB.lookup registrationSlot world ≡ just (O.recordOf owner (O.registration registration)) →
    DB.lookup checkoutSlot world ≡ just (O.recordOf owner (O.checkout checkout)) →
    O.RegistrationInfo.identity registration ≡ just familySource →
    O.CheckoutInfo.identity checkout ≡ just checkoutSource → Maybe (Target world)
  examine world registration checkout familySource checkoutSource familyAt checkoutAt savedFamily savedCheckout with
    Canonical.compare Codecs.familyId (Identity.FamilyBinding.id familySource) (O.RegistrationInfo.id registration) |
    Canonical.compare Codecs.checkoutId (Identity.CheckoutBinding.id checkoutSource) (O.CheckoutInfo.id checkout) |
    Canonical.compare Codecs.uuid (Identity.CheckoutBinding.incarnation checkoutSource) (O.CheckoutInfo.incarnation checkout) |
    Canonical.compare Codecs.locator requiredLocation (Identity.Observation.requested observed) |
    Canonical.compare Codecs.path (Identity.CheckoutBinding.root checkoutSource) (Identity.Observation.root observed) |
    familyReuse ctx familySource observed (Discovery.assessFamily ctx familySource observed) |
    checkoutReuse ctx (Identity.FamilyBinding.kind familySource) checkoutSource observed
      (Discovery.assessCheckout ctx (Identity.FamilyBinding.kind familySource) checkoutSource observed)
  ... | yes familyId | yes checkoutId | yes incarnation | yes requested | yes currentRoot | just familyEvidence | just checkoutEvidence =
    just (target registration checkout familySource checkoutSource familyAt checkoutAt savedFamily savedCheckout
      familyId checkoutId incarnation requested currentRoot familyEvidence checkoutEvidence)
  ... | _ | _ | _ | _ | _ | _ | _ = nothing

  bindings : ∀ world registration checkout →
    DB.lookup registrationSlot world ≡ just (O.recordOf owner (O.registration registration)) →
    DB.lookup checkoutSlot world ≡ just (O.recordOf owner (O.checkout checkout)) → Maybe (Target world)
  bindings world registration checkout familyAt checkoutAt with O.RegistrationInfo.identity registration in savedFamily | O.CheckoutInfo.identity checkout in savedCheckout
  ... | just familySource | just checkoutSource = examine world registration checkout familySource checkoutSource familyAt checkoutAt savedFamily savedCheckout
  ... | _ | _ = nothing

  checkoutValue : ∀ world registration → DB.lookup registrationSlot world ≡ just (O.recordOf owner (O.registration registration)) →
    (value : Maybe O.Record) → DB.lookup checkoutSlot world ≡ value → Maybe (Target world)
  checkoutValue world registration familyAt (just (O.recordOf actualOwner (O.checkout checkout))) checkoutAt with E.ownerEqual actualOwner owner
  ... | yes refl = bindings world registration checkout familyAt checkoutAt
  ... | no different = nothing
  checkoutValue world registration familyAt value checkoutAt = nothing

  familyValue : ∀ world → (value : Maybe O.Record) → DB.lookup registrationSlot world ≡ value → Maybe (Target world)
  familyValue world (just (O.recordOf actualOwner (O.registration registration))) familyAt with E.ownerEqual actualOwner owner
  ... | yes refl = checkoutValue world registration familyAt (DB.lookup checkoutSlot world) refl
  ... | no different = nothing
  familyValue world value found = nothing

  observe : (world : O.World) → Maybe (Target world)
  observe world = familyValue world (DB.lookup registrationSlot world) refl

  capture : ∀ {world} → (query : Q.Search) → Q.location query ≡ requiredLocation → Target world → Q.SavedSearch
  capture query sameLocation selected = Q.savedSearch query (O.RegistrationInfo.id (Target.registration selected))
    (O.CheckoutInfo.id (Target.checkout selected)) (O.CheckoutInfo.incarnation (Target.checkout selected))

  queryRetained : ∀ world query sameLocation (selected : Target world) → Q.SavedSearch.request (capture query sameLocation selected) ≡ query
  queryRetained world query sameLocation selected = refl
  capturedCheckout : ∀ world query sameLocation (selected : Target world) → Q.SavedSearch.checkout (capture query sameLocation selected) ≡ O.CheckoutInfo.id (Target.checkout selected)
  capturedCheckout world query sameLocation selected = refl

  -- Resume may follow a verified move. It must match saved IDs/incarnation,
  -- rather than looking up the old query's directory string as a fresh clone.
  sameScope : ∀ {world} → Q.SavedSearch → Target world → Set
  sameScope saved selected = Q.SavedSearch.family saved ≡ O.RegistrationInfo.id (Target.registration selected) ×
    (Q.SavedSearch.checkout saved ≡ O.CheckoutInfo.id (Target.checkout selected) ×
      Q.SavedSearch.incarnation saved ≡ O.CheckoutInfo.incarnation (Target.checkout selected))
