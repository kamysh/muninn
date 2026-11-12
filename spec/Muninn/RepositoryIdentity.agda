{-# OPTIONS --safe #-}
-- Database IDs, external incarnation evidence, and path locations are distinct.
module Muninn.RepositoryIdentity where

import Muninn.Worktree as W
import Muninn.CatalogInputs as Input
open import Muninn.Types using (FilePath; UUID)
open import Data.String using (String; _≟_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

-- This is provider-issued object-incarnation evidence, NOT a path, a content
-- hash, branch or remote URL. Supply nothing if a platform cannot establish a
-- reliable key. No private ID is written into Git metadata by this contract.
record ObjectId : Set where
  constructor objectId
  field issuer token : String

objectEqual : (first second : ObjectId) → Dec (first ≡ second)
objectEqual (objectId issuer token) (objectId other otherToken) with issuer ≟ other | token ≟ otherToken
... | yes refl | yes refl = yes refl
... | no different | _ = no (λ same → different (cong ObjectId.issuer same))
... | _ | no different = no (λ same → different (cong ObjectId.token same))

data Kind : Set where directory git : Kind

record FamilyBinding : Set where
  constructor familyBinding
  field id : W.FamilyId
        kind : Kind
        location : FilePath
        anchor : Maybe ObjectId

record CheckoutBinding : Set where
  constructor checkoutBinding
  field id : W.CheckoutId
        incarnation : UUID
        root : FilePath
        rootObject : Maybe ObjectId
        gitAdmin : Maybe ObjectId

record GitObservation : Set where
  constructor gitObservation
  field commonPath adminPath : FilePath
        commonObject adminObject : Maybe ObjectId

record Observation : Set where
  constructor observation
  field stamp : UUID
        requested : Input.Locator
        root : FilePath
        rootObject : Maybe ObjectId
        gitInfo : Maybe GitObservation

Agrees : Maybe ObjectId → Maybe ObjectId → Set
Agrees (just first) (just second) = first ≡ second
Agrees _ _ = ⊥

agrees? : ∀ first second → Dec (Agrees first second)
agrees? (just first) (just second) = objectEqual first second
agrees? nothing second = no (λ ())
agrees? (just first) nothing = no (λ ())

FamilyAssociation : FamilyBinding → Observation → Set
FamilyAssociation (familyBinding id directory location anchor) observed = Agrees anchor (Observation.rootObject observed)
FamilyAssociation (familyBinding id git location anchor) observed with Observation.gitInfo observed
... | nothing = ⊥
... | just gitView = Agrees anchor (GitObservation.commonObject gitView)

familyAssociation? : ∀ binding observed → Dec (FamilyAssociation binding observed)
familyAssociation? (familyBinding id directory location anchor) observed = agrees? anchor (Observation.rootObject observed)
familyAssociation? (familyBinding id git location anchor) observed with Observation.gitInfo observed
... | nothing = no (λ ())
... | just gitView = agrees? anchor (GitObservation.commonObject gitView)

CheckoutAssociation : Kind → CheckoutBinding → Observation → Set
CheckoutAssociation directory binding observed = Agrees (CheckoutBinding.rootObject binding) (Observation.rootObject observed)
CheckoutAssociation git binding observed with Observation.gitInfo observed
... | nothing = ⊥
... | just gitView = Agrees (CheckoutBinding.gitAdmin binding) (GitObservation.adminObject gitView)

checkoutAssociation? : ∀ kind binding observed → Dec (CheckoutAssociation kind binding observed)
checkoutAssociation? directory binding observed = agrees? (CheckoutBinding.rootObject binding) (Observation.rootObject observed)
checkoutAssociation? git binding observed with Observation.gitInfo observed
... | nothing = no (λ ())
... | just gitView = agrees? (CheckoutBinding.gitAdmin binding) (GitObservation.adminObject gitView)

familyLocation : (binding : FamilyBinding) → (observed : Observation) → FamilyAssociation binding observed → FilePath
familyLocation (familyBinding id directory location anchor) observed same = Observation.root observed
familyLocation (familyBinding id git location anchor) observed same with Observation.gitInfo observed
... | nothing = ⊥-elim same
... | just gitView = GitObservation.commonPath gitView

moveFamily : (binding : FamilyBinding) → (observed : Observation) → FamilyAssociation binding observed → FamilyBinding
moveFamily binding observed same = record binding { location = familyLocation binding observed same }

moveCheckout : ∀ kind → (binding : CheckoutBinding) → (observed : Observation) → CheckoutAssociation kind binding observed → CheckoutBinding
moveCheckout kind binding observed same = record binding
  { root = Observation.root observed; rootObject = Observation.rootObject observed }

familyMoveKeepsId : ∀ binding observed same → FamilyBinding.id (moveFamily binding observed same) ≡ FamilyBinding.id binding
familyMoveKeepsId binding observed same = refl

familyMoveKeepsKind : ∀ binding observed same → FamilyBinding.kind (moveFamily binding observed same) ≡ FamilyBinding.kind binding
familyMoveKeepsKind binding observed same = refl

checkoutMoveKeepsIdentity : ∀ kind binding observed same →
  CheckoutBinding.id (moveCheckout kind binding observed same) ≡ CheckoutBinding.id binding ×
  CheckoutBinding.incarnation (moveCheckout kind binding observed same) ≡ CheckoutBinding.incarnation binding
checkoutMoveKeepsIdentity kind binding observed same = refl , refl

checkoutMoveUsesNewRoot : ∀ kind binding observed same →
  CheckoutBinding.root (moveCheckout kind binding observed same) ≡ Observation.root observed
checkoutMoveUsesNewRoot kind binding observed same = refl

-- Pure intended metadata for an explicitly requested conversion. Ordinary
-- discovery uses moveFamily, whose kind-preservation law forbids conversion.
convertBinding : FamilyBinding → GitObservation → FamilyBinding
convertBinding binding observed = record binding
  { kind = git; location = GitObservation.commonPath observed; anchor = GitObservation.commonObject observed }

conversionKeepsId : ∀ binding observed → FamilyBinding.id (convertBinding binding observed) ≡ FamilyBinding.id binding
conversionKeepsId binding observed = refl

conversionIsGit : ∀ binding observed → FamilyBinding.kind (convertBinding binding observed) ≡ git
conversionIsGit binding observed = refl

CompatibleKind : Kind → Observation → Set
CompatibleKind directory observed = ⊤
CompatibleKind git observed with Observation.gitInfo observed
... | nothing = ⊥
... | just gitView = ⊤

compatibleKind? : ∀ kind observed → Dec (CompatibleKind kind observed)
compatibleKind? directory observed = yes tt
compatibleKind? git observed with Observation.gitInfo observed
... | nothing = no (λ ())
... | just gitView = yes tt

-- Explicitly clarified moves may cross filesystems and therefore change the
-- observed object key. They retain the DB identity; ordinary moves still need
-- the positive association above. No path-only automatic adoption exists.
reassociateFamily : (saved : FamilyBinding) → (observed : Observation) → CompatibleKind (FamilyBinding.kind saved) observed → FamilyBinding
reassociateFamily (familyBinding id directory location anchor) observed suitable =
  familyBinding id directory (Observation.root observed) (Observation.rootObject observed)
reassociateFamily (familyBinding id git location anchor) observed suitable with Observation.gitInfo observed
... | nothing = ⊥-elim suitable
... | just gitView = familyBinding id git (GitObservation.commonPath gitView) (GitObservation.commonObject gitView)

reassociateCheckout : ∀ kind → (saved : CheckoutBinding) → (observed : Observation) → CompatibleKind kind observed → CheckoutBinding
reassociateCheckout directory saved observed suitable = record saved
  { root = Observation.root observed; rootObject = Observation.rootObject observed }
reassociateCheckout git saved observed suitable with Observation.gitInfo observed
... | nothing = ⊥-elim suitable
... | just gitView = record saved { root = Observation.root observed; rootObject = Observation.rootObject observed; gitAdmin = GitObservation.adminObject gitView }

reassociationKeepsFamilyId : ∀ saved observed suitable → FamilyBinding.id (reassociateFamily saved observed suitable) ≡ FamilyBinding.id saved
reassociationKeepsFamilyId (familyBinding id directory location anchor) observed suitable = refl
reassociationKeepsFamilyId (familyBinding id git location anchor) observed suitable with Observation.gitInfo observed
... | nothing = ⊥-elim suitable
... | just gitView = refl

reassociationKeepsCheckoutId : ∀ kind saved observed suitable →
  CheckoutBinding.id (reassociateCheckout kind saved observed suitable) ≡ CheckoutBinding.id saved ×
  CheckoutBinding.incarnation (reassociateCheckout kind saved observed suitable) ≡ CheckoutBinding.incarnation saved
reassociationKeepsCheckoutId directory saved observed suitable = refl , refl
reassociationKeepsCheckoutId git saved observed suitable with Observation.gitInfo observed
... | nothing = ⊥-elim suitable
... | just gitView = refl , refl

newFamily : W.FamilyId → Observation → FamilyBinding
newFamily id observed with Observation.gitInfo observed
... | nothing = familyBinding id directory (Observation.root observed) (Observation.rootObject observed)
... | just gitView = familyBinding id git (GitObservation.commonPath gitView) (GitObservation.commonObject gitView)

newCheckout : W.CheckoutId → UUID → Observation → CheckoutBinding
newCheckout id incarnation observed with Observation.gitInfo observed
... | nothing = checkoutBinding id incarnation (Observation.root observed) (Observation.rootObject observed) nothing
... | just gitView = checkoutBinding id incarnation (Observation.root observed) (Observation.rootObject observed) (GitObservation.adminObject gitView)
