{-# OPTIONS --safe #-}
-- Freshness is evidence about the selected stored view and an inspected source.
module Muninn.SearchReadiness where
import Muninn.OwnedState as O
import Muninn.WorkQueue as Q
import Muninn.FirstSearch as Start
import Muninn.SearchView as View
import Muninn.StoredPolicy as Policy
import Muninn.ContentViews as Content
import Muninn.CheckoutReconciliation as Reconciliation
import Muninn.CatalogInputs as I
import Muninn.Types as T
import Muninn.Worktree as W
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst)
module DB = O.DB

data Freshness : Set where unavailable suspended partial stale current unverified : Freshness

module Family (family registrationSlot selected policyPointer : ℕ) (world : O.World)
  (registration : O.RegistrationInfo) (checkout : O.CheckoutInfo)
  (registrationAt : DB.lookup registrationSlot world ≡ just (O.recordOf (O.family family) (O.registration registration)))
  (checkoutAt : DB.lookup selected world ≡ just (O.recordOf (O.family family) (O.checkout checkout)))
  (currentPolicy : Policy.Family.Saved family policyPointer world) where
  owner = O.family family
  module Published = View.Family family selected
  module Files = Content.Family (Policy.Family.rule family policyPointer currentPolicy)
  actual = Files.visible world selected

  -- An unreadable included file must have real saved work and be hidden.
  record HiddenReadWork (path : T.FilePath) : Set where
    field slot : ℕ
          jobId parent : I.OperationId
          versions : List ℕ
          input : I.FileJob
          phase : Q.Phase
          generation : ℕ
          located : DB.lookup slot world ≡ just (O.recordOf owner (O.acceptedWork versions
            (Q.work jobId parent I.analyzeFile input phase generation)))
          sameFamily : I.FamilyJob.family (I.CheckoutJob.parent (I.FileJob.parent input)) ≡ O.RegistrationInfo.id registration
          sameCheckout : I.CheckoutJob.checkout (I.FileJob.parent input) ≡ O.CheckoutInfo.id checkout
          samePath : I.FileJob.path input ≡ path
          hidden : actual path ≡ nothing

  -- The inspected inventory is an external source observation, not a goal
  -- supplied by a storage script. A finite inventory adapter must construct
  -- these comparisons and enumerate its read problems completely.
  module Observation (expected : Content.Files.Manifest) (waiting : Reconciliation.Waiting) (stamp : T.UUID) where
    Matched : Set
    Matched = ∀ path → actual path ≡ expected path
    data Alignment : Set where
      matches : Matched → Alignment
      differs : (path : T.FilePath) → actual path ≢ expected path → Alignment
    record Assessment : Set where
      field alignment : Alignment
            paths : List T.FilePath
            readWork : ∀ path → path ∈ paths → Σ Reconciliation.ReadProblem (λ problem → waiting path ≡ just problem × HiddenReadWork path)
            complete : ∀ path problem → waiting path ≡ just problem → path ∈ paths

    coverage : Assessment → Freshness
    coverage assessed with Assessment.paths assessed
    ... | path ∷ rest = partial
    ... | [] with Assessment.alignment assessed
    ...   | matches same = current
    ...   | differs path changed = stale

    coverageCurrent : ∀ assessed → coverage assessed ≡ current → Matched
    coverageCurrent assessed claimed with Assessment.paths assessed
    ... | path ∷ rest with claimed
    ...   | ()
    coverageCurrent assessed claimed | [] with Assessment.alignment assessed
    ... | matches same = same
    ... | differs path changed with claimed
    ...   | ()

    coveragePartial : ∀ assessed → coverage assessed ≡ partial → Σ T.FilePath HiddenReadWork
    coveragePartial assessed claimed with Assessment.paths assessed in paths
    ... | path ∷ rest with Assessment.readWork assessed path (subst (λ entries → path ∈ entries)
      (sym paths) (here refl))
    ...   | problem , pending , work = path , work
    coveragePartial assessed claimed | [] with Assessment.alignment assessed
    ... | matches same with claimed
    ...   | ()
    coveragePartial assessed claimed | [] | differs path changed with claimed
    ... | ()

    coverageStale : ∀ assessed → coverage assessed ≡ stale → Σ T.FilePath (λ path → actual path ≢ expected path)
    coverageStale assessed claimed with Assessment.paths assessed
    ... | path ∷ rest with claimed
    ...   | ()
    coverageStale assessed claimed | [] with Assessment.alignment assessed
    ... | matches same with claimed
    ...   | ()
    coverageStale assessed claimed | [] | differs path changed = path , changed

    coverageHasNoReadProblems : ∀ assessed → coverage assessed ≡ current → ∀ path → waiting path ≡ nothing
    coverageHasNoReadProblems assessed claimed path with Assessment.paths assessed in paths
    ... | first ∷ rest with claimed
    ...   | ()
    coverageHasNoReadProblems assessed claimed path | [] with waiting path in read
    ... | nothing = refl
    ... | just problem = ⊥-elim (impossible (subst (λ entries → path ∈ entries) paths (Assessment.complete assessed path problem read)))
      where impossible : path ∈ [] → ⊥
            impossible ()

    assess : Maybe Assessment → Freshness
    assess observed with Start.searchable owner world registration checkout | Published.observe world
    ... | false | _ = unavailable
    ... | true | nothing = unavailable
    ... | true | just view with O.CheckoutInfo.gitSuspended checkout
    ...   | true = suspended
    ...   | false with observed
    ...     | nothing = unverified
    ...     | just assessed = coverage assessed

    noViewUnavailable : ∀ observed → Published.observe world ≡ nothing → assess observed ≡ unavailable
    noViewUnavailable observed absent rewrite absent with Start.searchable owner world registration checkout
    ... | false = refl
    ... | true = refl

    currentRequiresInspection : ∀ observed → assess observed ≡ current → Σ Assessment (λ assessed → observed ≡ just assessed × Matched)
    currentRequiresInspection observed claimed with Start.searchable owner world registration checkout | Published.observe world
    ... | false | _ with claimed
    ...   | ()
    currentRequiresInspection observed claimed | true | nothing with claimed
    ... | ()
    currentRequiresInspection observed claimed | true | just view with O.CheckoutInfo.gitSuspended checkout
    ... | true with claimed
    ...   | ()
    currentRequiresInspection observed claimed | true | just view | false with observed
    ... | nothing with claimed
    ...   | ()
    currentRequiresInspection observed claimed | true | just view | false | just assessed = assessed , refl , coverageCurrent assessed claimed

    partialHasHiddenWork : ∀ observed → assess observed ≡ partial → Σ T.FilePath (λ path → HiddenReadWork path × actual path ≡ nothing)
    partialHasHiddenWork observed claimed with Start.searchable owner world registration checkout | Published.observe world
    ... | false | _ with claimed
    ...   | ()
    partialHasHiddenWork observed claimed | true | nothing with claimed
    ... | ()
    partialHasHiddenWork observed claimed | true | just view with O.CheckoutInfo.gitSuspended checkout
    ... | true with claimed
    ...   | ()
    partialHasHiddenWork observed claimed | true | just view | false with observed
    ... | nothing with claimed
    ...   | ()
    partialHasHiddenWork observed claimed | true | just view | false | just assessed with coveragePartial assessed claimed
    ... | path , work = path , work , HiddenReadWork.hidden work

    known : Maybe Assessment → Bool
    known nothing = false
    known (just assessed) = true
    pendingPaths : Maybe Assessment → List T.FilePath
    pendingPaths nothing = []
    pendingPaths (just assessed) = Assessment.paths assessed
    observationStamp : Maybe Assessment → Maybe T.UUID
    observationStamp nothing = nothing
    observationStamp (just assessed) = just stamp

    record Report (observed : Maybe Assessment) : Set where
      field state : Freshness
            stateCorrect : state ≡ assess observed
            familyId : W.FamilyId
            familyCorrect : familyId ≡ O.RegistrationInfo.id registration
            checkoutId : W.CheckoutId
            checkoutCorrect : checkoutId ≡ O.CheckoutInfo.id checkout
            gitSuspended : Bool
            gitCorrect : gitSuspended ≡ O.CheckoutInfo.gitSuspended checkout
            readWorkKnown : Bool
            knownCorrect : readWorkKnown ≡ known observed
            unresolvedFiles : List T.FilePath
            unresolvedCorrect : unresolvedFiles ≡ pendingPaths observed
            sourceStamp : Maybe T.UUID
            stampCorrect : sourceStamp ≡ observationStamp observed
    report : (observed : Maybe Assessment) → Report observed
    report observed = record
      { state = assess observed; stateCorrect = refl
      ; familyId = O.RegistrationInfo.id registration; familyCorrect = refl
      ; checkoutId = O.CheckoutInfo.id checkout; checkoutCorrect = refl
      ; gitSuspended = O.CheckoutInfo.gitSuspended checkout; gitCorrect = refl
      ; readWorkKnown = known observed; knownCorrect = refl
      ; unresolvedFiles = pendingPaths observed; unresolvedCorrect = refl
      ; sourceStamp = observationStamp observed; stampCorrect = refl }

    -- The final public dispatcher must return this wrapper for a known scope,
    -- rather than exposing a bare preparation message without its readiness.
    record KnownReply (observed : Maybe Assessment) : Set where
      field step : Start.Reply
            readiness : Report observed
    reply : ∀ step observed → KnownReply observed
    reply step observed = record { step = step; readiness = report observed }
