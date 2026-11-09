{-# OPTIONS --safe #-}
-- Reuse proven associations; otherwise correct the context through dialogue.
module Muninn.RepositoryDiscovery where

import Muninn.RepositoryIdentity as Identity
import Muninn.Dialogue as D
import Muninn.OwnedState as O
import Muninn.Worktree as W
import Muninn.Types as T
import Muninn.CatalogInputs as I
import Muninn.ArtifactIdentity as Equal
open import Muninn.Types using (FilePath; UUID)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_)
open import Data.String using (String; _++_)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe.Properties
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
import Data.String as String
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)

observationText : Identity.Observation → String
observationText observed = T.UUID.value (Identity.Observation.stamp observed)

familyIdText : Identity.FamilyBinding → String
familyIdText saved = T.UUID.value (W.FamilyId.value (Identity.FamilyBinding.id saved))

checkoutIdText : Identity.CheckoutBinding → String
checkoutIdText saved = T.UUID.value (W.CheckoutId.value (Identity.CheckoutBinding.id saved))

familySame : Identity.FamilyBinding → Identity.Observation → D.Option
familySame saved observed = D.option (D.text 'S' "ame repository, moved or restored")
  (D.text 'K' "eep the existing registration, notes and compatible indexed work; update its location only after confirming this current inspection.")
  (("repository.id" , familyIdText saved) ∷
   ("repository.familyRoot" , FilePath.value (Identity.Observation.root observed)) ∷
   ("repository.familyObservation" , observationText observed) ∷
   ("repository.familyChoice" , "same") ∷ [])

familyNew : Identity.Observation → D.Option
familyNew observed = D.option (D.text 'N' "ew or replacement repository")
  (D.text 'U' "se a new registration and identity. Preserve the old repository separately; do not adopt its saved view because this path was reused.")
  (("repository.familyRoot" , FilePath.value (Identity.Observation.root observed)) ∷
   ("repository.familyObservation" , observationText observed) ∷
   ("repository.familyChoice" , "new") ∷ [])

familyQuestion : Identity.FamilyBinding → Identity.Observation → D.Question
familyQuestion saved observed = D.alternatives
  (D.text 'I' (" cannot establish whether " ++ FilePath.value (Identity.Observation.root observed) ++
    " is the saved repository " ++ familyIdText saved ++ ". A matching path or Git history is not enough."))
  (familySame saved observed) (familyNew observed ∷ [])

checkoutSame : Identity.CheckoutBinding → Identity.Observation → D.Option
checkoutSame saved observed = D.option (D.text 'S' "ame worktree, moved")
  (D.text 'K' "eep its worktree identity and completed view; update the observed location.")
  (("repository.checkout" , checkoutIdText saved) ∷
   ("repository.checkoutRoot" , FilePath.value (Identity.Observation.root observed)) ∷
   ("repository.checkoutObservation" , observationText observed) ∷
   ("repository.checkoutChoice" , "same") ∷ [])

checkoutNew : Identity.Observation → D.Option
checkoutNew observed = D.option (D.text 'N' "ew replacement worktree")
  (D.text 'G' "ive it a fresh worktree identity and incarnation; keep the old saved view separate.")
  (("repository.checkoutRoot" , FilePath.value (Identity.Observation.root observed)) ∷
   ("repository.checkoutObservation" , observationText observed) ∷
   ("repository.checkoutChoice" , "new") ∷ [])

checkoutQuestion : Identity.CheckoutBinding → Identity.Observation → D.Question
checkoutQuestion saved observed = D.alternatives
  (D.text 'I' (" cannot establish whether " ++ FilePath.value (Identity.Observation.root observed) ++
    " is the saved worktree " ++ checkoutIdText saved ++ ". It may have moved or been replaced."))
  (checkoutSame saved observed) (checkoutNew observed ∷ [])

storedEquals? : (value : Maybe String) → (expected : String) → Dec (value ≡ just expected)
storedEquals? nothing expected = no (λ ())
storedEquals? (just value) expected with value String.≟ expected
... | yes refl = yes refl
... | no different = no (λ { refl → different refl })

record FamilyConfirmation (ctx : D.Context) (saved : Identity.FamilyBinding) (observed : Identity.Observation) : Set where
  field namedId : D.Facts.lookup "repository.id" (D.Context.facts ctx) ≡ just (familyIdText saved)
        namedRoot : D.Facts.lookup "repository.familyRoot" (D.Context.facts ctx) ≡ just (FilePath.value (Identity.Observation.root observed))
        currentObservation : D.Facts.lookup "repository.familyObservation" (D.Context.facts ctx) ≡ just (observationText observed)
        choseSame : D.Facts.lookup "repository.familyChoice" (D.Context.facts ctx) ≡ just "same"
        suitable : Identity.CompatibleKind (Identity.FamilyBinding.kind saved) observed

familyConfirmation? : ∀ ctx saved observed → Dec (FamilyConfirmation ctx saved observed)
familyConfirmation? ctx saved observed with storedEquals? (D.Facts.lookup "repository.id" (D.Context.facts ctx)) (familyIdText saved)
  | storedEquals? (D.Facts.lookup "repository.familyRoot" (D.Context.facts ctx)) (FilePath.value (Identity.Observation.root observed))
  | storedEquals? (D.Facts.lookup "repository.familyObservation" (D.Context.facts ctx)) (observationText observed)
  | storedEquals? (D.Facts.lookup "repository.familyChoice" (D.Context.facts ctx)) "same"
  | Identity.compatibleKind? (Identity.FamilyBinding.kind saved) observed
... | yes idSame | yes rootSame | yes stampSame | yes choice | yes suitable = yes (record
  { namedId = idSame; namedRoot = rootSame; currentObservation = stampSame; choseSame = choice; suitable = suitable })
... | no different | _ | _ | _ | _ = no (λ proof → different (FamilyConfirmation.namedId proof))
... | _ | no different | _ | _ | _ = no (λ proof → different (FamilyConfirmation.namedRoot proof))
... | _ | _ | no different | _ | _ = no (λ proof → different (FamilyConfirmation.currentObservation proof))
... | _ | _ | _ | no different | _ = no (λ proof → different (FamilyConfirmation.choseSame proof))
... | _ | _ | _ | _ | no different = no (λ proof → different (FamilyConfirmation.suitable proof))

familyAnswerAdmitted : ∀ ctx saved observed → Identity.CompatibleKind (Identity.FamilyBinding.kind saved) observed →
  FamilyConfirmation (D.repairMany (D.Option.updates (familySame saved observed)) ctx) saved observed
familyAnswerAdmitted ctx saved observed suitable = record
  { namedId = refl; namedRoot = refl; currentObservation = refl; choseSame = refl; suitable = suitable }

record NewFamilyConfirmation (ctx : D.Context) (observed : Identity.Observation) : Set where
  field namedRoot : D.Facts.lookup "repository.familyRoot" (D.Context.facts ctx) ≡ just (FilePath.value (Identity.Observation.root observed))
        currentObservation : D.Facts.lookup "repository.familyObservation" (D.Context.facts ctx) ≡ just (observationText observed)
        choseNew : D.Facts.lookup "repository.familyChoice" (D.Context.facts ctx) ≡ just "new"

newFamilyAnswerAdmitted : ∀ ctx observed → NewFamilyConfirmation (D.repairMany (D.Option.updates (familyNew observed)) ctx) observed
newFamilyAnswerAdmitted ctx observed = record { namedRoot = refl; currentObservation = refl; choseNew = refl }
newFamilyConfirmation? : ∀ ctx observed → Dec (NewFamilyConfirmation ctx observed)
newFamilyConfirmation? ctx observed with storedEquals? (D.Facts.lookup "repository.familyRoot" (D.Context.facts ctx)) (FilePath.value (Identity.Observation.root observed))
  | storedEquals? (D.Facts.lookup "repository.familyObservation" (D.Context.facts ctx)) (observationText observed)
  | storedEquals? (D.Facts.lookup "repository.familyChoice" (D.Context.facts ctx)) "new"
... | yes root | yes stamp | yes choice = yes (record { namedRoot = root; currentObservation = stamp; choseNew = choice })
... | no different | _ | _ = no (λ proof → different (NewFamilyConfirmation.namedRoot proof))
... | _ | no different | _ = no (λ proof → different (NewFamilyConfirmation.currentObservation proof))
... | _ | _ | no different = no (λ proof → different (NewFamilyConfirmation.choseNew proof))

data FamilyDecision (ctx : D.Context) (saved : Identity.FamilyBinding) (observed : Identity.Observation) : Set where
  reuseFamily : Identity.FamilyAssociation saved observed → FamilyDecision ctx saved observed
  reuseClarifiedFamily : FamilyConfirmation ctx saved observed → FamilyDecision ctx saved observed
  useNewRegistration : NewFamilyConfirmation ctx observed → FamilyDecision ctx saved observed
  clarifyFamily : ¬ Identity.FamilyAssociation saved observed → ¬ FamilyConfirmation ctx saved observed → ¬ NewFamilyConfirmation ctx observed → D.Question → FamilyDecision ctx saved observed

assessFamily : ∀ ctx saved observed → FamilyDecision ctx saved observed
assessFamily ctx saved observed with Identity.familyAssociation? saved observed
... | yes same = reuseFamily same
... | no unknown with familyConfirmation? ctx saved observed
...   | yes clarified = reuseClarifiedFamily clarified
...   | no missing with newFamilyConfirmation? ctx observed
...     | yes fresh = useNewRegistration fresh
...     | no absent = clarifyFamily unknown missing absent (familyQuestion saved observed)

knownFamilyReused : ∀ ctx saved observed → Identity.FamilyAssociation saved observed →
  Σ (Identity.FamilyAssociation saved observed) (λ same → assessFamily ctx saved observed ≡ reuseFamily same)
knownFamilyReused ctx saved observed proof with Identity.familyAssociation? saved observed
... | yes same = same , refl
... | no unknown = ⊥-elim (unknown proof)

clarifiedFamilyReused : ∀ ctx saved observed → ¬ Identity.FamilyAssociation saved observed → FamilyConfirmation ctx saved observed →
  Σ (FamilyConfirmation ctx saved observed) (λ clarified → assessFamily ctx saved observed ≡ reuseClarifiedFamily clarified)
clarifiedFamilyReused ctx saved observed unknown proof with Identity.familyAssociation? saved observed
... | yes same = ⊥-elim (unknown same)
... | no different with familyConfirmation? ctx saved observed
...   | yes clarified = clarified , refl
...   | no missing = ⊥-elim (missing proof)

record CheckoutConfirmation (ctx : D.Context) (kind : Identity.Kind) (saved : Identity.CheckoutBinding) (observed : Identity.Observation) : Set where
  field namedId : D.Facts.lookup "repository.checkout" (D.Context.facts ctx) ≡ just (checkoutIdText saved)
        namedRoot : D.Facts.lookup "repository.checkoutRoot" (D.Context.facts ctx) ≡ just (FilePath.value (Identity.Observation.root observed))
        currentObservation : D.Facts.lookup "repository.checkoutObservation" (D.Context.facts ctx) ≡ just (observationText observed)
        choseSame : D.Facts.lookup "repository.checkoutChoice" (D.Context.facts ctx) ≡ just "same"
        suitable : Identity.CompatibleKind kind observed

checkoutConfirmation? : ∀ ctx kind saved observed → Dec (CheckoutConfirmation ctx kind saved observed)
checkoutConfirmation? ctx kind saved observed with storedEquals? (D.Facts.lookup "repository.checkout" (D.Context.facts ctx)) (checkoutIdText saved)
  | storedEquals? (D.Facts.lookup "repository.checkoutRoot" (D.Context.facts ctx)) (FilePath.value (Identity.Observation.root observed))
  | storedEquals? (D.Facts.lookup "repository.checkoutObservation" (D.Context.facts ctx)) (observationText observed)
  | storedEquals? (D.Facts.lookup "repository.checkoutChoice" (D.Context.facts ctx)) "same"
  | Identity.compatibleKind? kind observed
... | yes idSame | yes rootSame | yes stampSame | yes choice | yes suitable = yes (record
  { namedId = idSame; namedRoot = rootSame; currentObservation = stampSame; choseSame = choice; suitable = suitable })
... | no different | _ | _ | _ | _ = no (λ proof → different (CheckoutConfirmation.namedId proof))
... | _ | no different | _ | _ | _ = no (λ proof → different (CheckoutConfirmation.namedRoot proof))
... | _ | _ | no different | _ | _ = no (λ proof → different (CheckoutConfirmation.currentObservation proof))
... | _ | _ | _ | no different | _ = no (λ proof → different (CheckoutConfirmation.choseSame proof))
... | _ | _ | _ | _ | no different = no (λ proof → different (CheckoutConfirmation.suitable proof))

checkoutAnswerAdmitted : ∀ ctx kind saved observed → Identity.CompatibleKind kind observed →
  CheckoutConfirmation (D.repairMany (D.Option.updates (checkoutSame saved observed)) ctx) kind saved observed
checkoutAnswerAdmitted ctx kind saved observed suitable = record
  { namedId = refl; namedRoot = refl; currentObservation = refl; choseSame = refl; suitable = suitable }

record NewCheckoutConfirmation (ctx : D.Context) (observed : Identity.Observation) : Set where
  field namedRoot : D.Facts.lookup "repository.checkoutRoot" (D.Context.facts ctx) ≡ just (FilePath.value (Identity.Observation.root observed))
        currentObservation : D.Facts.lookup "repository.checkoutObservation" (D.Context.facts ctx) ≡ just (observationText observed)
        choseNew : D.Facts.lookup "repository.checkoutChoice" (D.Context.facts ctx) ≡ just "new"

newCheckoutAnswerAdmitted : ∀ ctx observed → NewCheckoutConfirmation (D.repairMany (D.Option.updates (checkoutNew observed)) ctx) observed
newCheckoutAnswerAdmitted ctx observed = record { namedRoot = refl; currentObservation = refl; choseNew = refl }

newCheckoutConfirmation? : ∀ ctx observed → Dec (NewCheckoutConfirmation ctx observed)
newCheckoutConfirmation? ctx observed with storedEquals? (D.Facts.lookup "repository.checkoutRoot" (D.Context.facts ctx)) (FilePath.value (Identity.Observation.root observed))
  | storedEquals? (D.Facts.lookup "repository.checkoutObservation" (D.Context.facts ctx)) (observationText observed)
  | storedEquals? (D.Facts.lookup "repository.checkoutChoice" (D.Context.facts ctx)) "new"
... | yes root | yes stamp | yes choice = yes (record { namedRoot = root; currentObservation = stamp; choseNew = choice })
... | no different | _ | _ = no (λ proof → different (NewCheckoutConfirmation.namedRoot proof))
... | _ | no different | _ = no (λ proof → different (NewCheckoutConfirmation.currentObservation proof))
... | _ | _ | no different = no (λ proof → different (NewCheckoutConfirmation.choseNew proof))

data CheckoutDecision (ctx : D.Context) (kind : Identity.Kind) (saved : Identity.CheckoutBinding) (observed : Identity.Observation) : Set where
  reuseCheckout : Identity.CheckoutAssociation kind saved observed → CheckoutDecision ctx kind saved observed
  reuseClarifiedCheckout : CheckoutConfirmation ctx kind saved observed → CheckoutDecision ctx kind saved observed
  useNewCheckout : NewCheckoutConfirmation ctx observed → CheckoutDecision ctx kind saved observed
  clarifyCheckout : ¬ Identity.CheckoutAssociation kind saved observed → ¬ CheckoutConfirmation ctx kind saved observed → ¬ NewCheckoutConfirmation ctx observed → D.Question → CheckoutDecision ctx kind saved observed

assessCheckout : ∀ ctx kind saved observed → CheckoutDecision ctx kind saved observed
assessCheckout ctx kind saved observed with Identity.checkoutAssociation? kind saved observed
... | yes same = reuseCheckout same
... | no unknown with checkoutConfirmation? ctx kind saved observed
...   | yes clarified = reuseClarifiedCheckout clarified
...   | no missing with newCheckoutConfirmation? ctx observed
...     | yes fresh = useNewCheckout fresh
...     | no absent = clarifyCheckout unknown missing absent (checkoutQuestion saved observed)

clarifiedCheckoutReused : ∀ ctx kind saved observed → ¬ Identity.CheckoutAssociation kind saved observed → CheckoutConfirmation ctx kind saved observed →
  Σ (CheckoutConfirmation ctx kind saved observed) (λ clarified → assessCheckout ctx kind saved observed ≡ reuseClarifiedCheckout clarified)
clarifiedCheckoutReused ctx kind saved observed unknown proof with Identity.checkoutAssociation? kind saved observed
... | yes same = ⊥-elim (unknown same)
... | no different with checkoutConfirmation? ctx kind saved observed
...   | yes clarified = clarified , refl
...   | no missing = ⊥-elim (missing proof)

resolvedFamily : ∀ ctx saved observed → FamilyDecision ctx saved observed → Maybe Identity.FamilyBinding
resolvedFamily ctx saved observed (reuseFamily same) = just (Identity.moveFamily saved observed same)
resolvedFamily ctx saved observed (reuseClarifiedFamily clarified) = just (Identity.reassociateFamily saved observed (FamilyConfirmation.suitable clarified))
resolvedFamily ctx saved observed (useNewRegistration fresh) = nothing
resolvedFamily ctx saved observed (clarifyFamily unknown missing absent question) = nothing

resolvedCheckout : ∀ ctx kind saved observed → CheckoutDecision ctx kind saved observed → Maybe Identity.CheckoutBinding
resolvedCheckout ctx kind saved observed (reuseCheckout same) = just (Identity.moveCheckout kind saved observed same)
resolvedCheckout ctx kind saved observed (reuseClarifiedCheckout clarified) = just (Identity.reassociateCheckout kind saved observed (CheckoutConfirmation.suitable clarified))
resolvedCheckout ctx kind saved observed (useNewCheckout fresh) = nothing
resolvedCheckout ctx kind saved observed (clarifyCheckout unknown missing absent question) = nothing

-- No automatic mode change: even after Git appears, ordinary association keeps
-- the directory registration and its ID. Conversion is an explicit request.
conversionOffered : Identity.FamilyBinding → Identity.Observation → Bool
conversionOffered saved observed with Identity.FamilyBinding.kind saved | Identity.Observation.gitInfo observed
... | Identity.directory | just gitView = true
... | _ | _ = false

record ConversionPermit (request : I.IntentInput I.convertDirectory) (saved : Identity.FamilyBinding) : Set where
  constructor explicitConversion
  field targetMatches : I.FamilyTarget.expectedFamily (I.Mutation.input request) ≡ Identity.FamilyBinding.id saved
        directoryBefore : Identity.FamilyBinding.kind saved ≡ Identity.directory

-- This is the intended final metadata. A running conversion retains its old
-- directory binding until fresh selection/publication work is completed.
convert : ∀ request saved → ConversionPermit request saved → Identity.GitObservation → Identity.FamilyBinding
convert request saved permitted = Identity.convertBinding saved

conversionIdentityPreserved : ∀ request saved permitted observed →
  Identity.FamilyBinding.id (convert request saved permitted observed) ≡ Identity.FamilyBinding.id saved
conversionIdentityPreserved request saved permitted observed = refl

record Replacement (previous : Identity.CheckoutBinding) : Set where
  field fresh : Identity.CheckoutBinding
        distinctId : Identity.CheckoutBinding.id fresh ≢ Identity.CheckoutBinding.id previous
        distinctIncarnation : Identity.CheckoutBinding.incarnation fresh ≢ Identity.CheckoutBinding.incarnation previous

-- Identity is durable data; metadata relocation changes no index version,
-- curated note, frozen configuration, or indexing authorization.
relocateRegistration : ∀ info saved observed → O.RegistrationInfo.identity info ≡ just saved →
  Identity.FamilyAssociation saved observed → O.RegistrationInfo
relocateRegistration info saved observed binding same = record info { identity = just (Identity.moveFamily saved observed same) }

relocateCheckout : ∀ kind info saved observed → O.CheckoutInfo.identity info ≡ just saved →
  Identity.CheckoutAssociation kind saved observed → O.CheckoutInfo
relocateCheckout kind info saved observed binding same = record info { identity = just (Identity.moveCheckout kind saved observed same) }

relocationKeepsAuthorization : ∀ info saved observed binding same →
  O.RegistrationInfo.indexingEnabled (relocateRegistration info saved observed binding same) ≡ O.RegistrationInfo.indexingEnabled info
relocationKeepsAuthorization info saved observed binding same = refl

relocationKeepsRetirement : ∀ info saved observed binding same →
  O.RegistrationInfo.retired (relocateRegistration info saved observed binding same) ≡ O.RegistrationInfo.retired info ×
  O.RegistrationInfo.missingSince (relocateRegistration info saved observed binding same) ≡ O.RegistrationInfo.missingSince info
relocationKeepsRetirement info saved observed binding same = refl , refl

checkoutRelocationKeepsControls : ∀ kind info saved observed binding same →
  O.CheckoutInfo.paused (relocateCheckout kind info saved observed binding same) ≡ O.CheckoutInfo.paused info ×
  O.CheckoutInfo.gitSuspended (relocateCheckout kind info saved observed binding same) ≡ O.CheckoutInfo.gitSuspended info ×
  O.CheckoutInfo.retired (relocateCheckout kind info saved observed binding same) ≡ O.CheckoutInfo.retired info
checkoutRelocationKeepsControls kind info saved observed binding same = refl , refl , refl

newFamilyChoiceCannotReuseOld : ∀ ctx saved observed →
  ¬ FamilyConfirmation (D.repairMany (D.Option.updates (familyNew observed)) ctx) saved observed
newFamilyChoiceCannotReuseOld ctx saved observed proof with FamilyConfirmation.choseSame proof
... | ()

newCheckoutChoiceCannotReuseOld : ∀ ctx kind saved observed →
  ¬ CheckoutConfirmation (D.repairMany (D.Option.updates (checkoutNew observed)) ctx) kind saved observed
newCheckoutChoiceCannotReuseOld ctx kind saved observed proof with CheckoutConfirmation.choseSame proof
... | ()

staleFamilyAnswerRejected : ∀ ctx saved observed previous →
  D.Facts.lookup "repository.familyObservation" (D.Context.facts ctx) ≡ just previous → previous ≢ observationText observed →
  ¬ FamilyConfirmation ctx saved observed
staleFamilyAnswerRejected ctx saved observed previous stored different proof = different
  (Data.Maybe.Properties.just-injective (trans (sym stored) (FamilyConfirmation.currentObservation proof)))


newFamilyResolved : ∀ ctx saved observed → ¬ Identity.FamilyAssociation saved observed → ¬ FamilyConfirmation ctx saved observed → NewFamilyConfirmation ctx observed →
  Σ (NewFamilyConfirmation ctx observed) (λ fresh → assessFamily ctx saved observed ≡ useNewRegistration fresh)
newFamilyResolved ctx saved observed unknown notSame fresh with Identity.familyAssociation? saved observed
... | yes same = ⊥-elim (unknown same)
... | no different with familyConfirmation? ctx saved observed
...   | yes same = ⊥-elim (notSame same)
...   | no missing with newFamilyConfirmation? ctx observed
...     | yes ready = ready , refl
...     | no absent = ⊥-elim (absent fresh)

newCheckoutResolved : ∀ ctx kind saved observed → ¬ Identity.CheckoutAssociation kind saved observed → ¬ CheckoutConfirmation ctx kind saved observed → NewCheckoutConfirmation ctx observed →
  Σ (NewCheckoutConfirmation ctx observed) (λ fresh → assessCheckout ctx kind saved observed ≡ useNewCheckout fresh)
newCheckoutResolved ctx kind saved observed unknown notSame fresh with Identity.checkoutAssociation? kind saved observed
... | yes same = ⊥-elim (unknown same)
... | no different with checkoutConfirmation? ctx kind saved observed
...   | yes same = ⊥-elim (notSame same)
...   | no missing with newCheckoutConfirmation? ctx observed
...     | yes ready = ready , refl
...     | no absent = ⊥-elim (absent fresh)

-- Reuse evidence excludes new-registration and unresolved-dialogue decisions.
data FamilyReuse (ctx : D.Context) (saved : Identity.FamilyBinding) (source : Identity.Observation) : Set where
  physicalFamily : Identity.FamilyAssociation saved source → FamilyReuse ctx saved source
  confirmedFamily : FamilyConfirmation ctx saved source → FamilyReuse ctx saved source

familyReuse : ∀ ctx saved source → Maybe (FamilyReuse ctx saved source)
familyReuse ctx saved source with assessFamily ctx saved source
... | reuseFamily proof = just (physicalFamily proof)
... | reuseClarifiedFamily proof = just (confirmedFamily proof)
... | useNewRegistration fresh = nothing
... | clarifyFamily unknown missing absent question = nothing

familyAfter : ∀ {ctx saved source} → FamilyReuse ctx saved source → Identity.FamilyBinding
familyAfter {saved = saved} {source = source} (physicalFamily proof) = Identity.moveFamily saved source proof
familyAfter {saved = saved} {source = source} (confirmedFamily proof) = Identity.reassociateFamily saved source (FamilyConfirmation.suitable proof)

familyAfterId : ∀ {ctx saved source} (proof : FamilyReuse ctx saved source) → Identity.FamilyBinding.id (familyAfter proof) ≡ Identity.FamilyBinding.id saved
familyAfterId (physicalFamily proof) = refl
familyAfterId {saved = saved} {source = source} (confirmedFamily proof) = Identity.reassociationKeepsFamilyId saved source (FamilyConfirmation.suitable proof)

familyAfterKind : ∀ {ctx saved source} (proof : FamilyReuse ctx saved source) → Identity.FamilyBinding.kind (familyAfter proof) ≡ Identity.FamilyBinding.kind saved
familyAfterKind (physicalFamily proof) = refl
familyAfterKind {saved = Identity.familyBinding id Identity.directory location anchor} (confirmedFamily proof) = refl
familyAfterKind {saved = Identity.familyBinding id Identity.git location anchor} {source = Identity.observation stamp requested root object nothing} (confirmedFamily proof) = ⊥-elim (FamilyConfirmation.suitable proof)
familyAfterKind {saved = Identity.familyBinding id Identity.git location anchor} {source = Identity.observation stamp requested root object (just observed)} (confirmedFamily proof) = refl

data CheckoutReuse (ctx : D.Context) (kind : Identity.Kind) (saved : Identity.CheckoutBinding) (source : Identity.Observation) : Set where
  physicalCheckout : Identity.CheckoutAssociation kind saved source → CheckoutReuse ctx kind saved source
  confirmedCheckout : CheckoutConfirmation ctx kind saved source → CheckoutReuse ctx kind saved source

checkoutReuse : ∀ ctx kind saved source → Maybe (CheckoutReuse ctx kind saved source)
checkoutReuse ctx kind saved source with assessCheckout ctx kind saved source
... | reuseCheckout proof = just (physicalCheckout proof)
... | reuseClarifiedCheckout proof = just (confirmedCheckout proof)
... | useNewCheckout fresh = nothing
... | clarifyCheckout unknown missing absent question = nothing

checkoutAfter : ∀ {ctx kind saved source} → CheckoutReuse ctx kind saved source → Identity.CheckoutBinding
checkoutAfter {kind = kind} {saved} {source} (physicalCheckout proof) = Identity.moveCheckout kind saved source proof
checkoutAfter {kind = kind} {saved} {source} (confirmedCheckout proof) = Identity.reassociateCheckout kind saved source (CheckoutConfirmation.suitable proof)

checkoutAfterIdentity : ∀ {ctx kind saved source} (proof : CheckoutReuse ctx kind saved source) →
  Identity.CheckoutBinding.id (checkoutAfter proof) ≡ Identity.CheckoutBinding.id saved ×
  Identity.CheckoutBinding.incarnation (checkoutAfter proof) ≡ Identity.CheckoutBinding.incarnation saved
checkoutAfterIdentity (physicalCheckout proof) = refl , refl
checkoutAfterIdentity {kind = kind} {saved} {source} (confirmedCheckout proof) = Identity.reassociationKeepsCheckoutId kind saved source (CheckoutConfirmation.suitable proof)
