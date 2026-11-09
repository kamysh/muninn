{-# OPTIONS --safe #-}
-- Explicit conversion publishes a Git-filtered view and metadata atomically.
-- The storage adapter must realize fixed outcomes, as for ContentPublication.
module Muninn.DirectoryConversion where

import Muninn.RepositoryIdentity as Identity
import Muninn.RepositoryDiscovery as Discovery
import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.ContentViews as Content
import Muninn.ContentPublication as Publication
import Muninn.PublishedViews as Views
import Muninn.GitIgnore as Git
import Muninn.StoredPolicy as Policy
import Muninn.CatalogInputs as I
import Muninn.RequestIdentity as Meaning
import Muninn.ReceiptTypes as R
import Muninn.ReceiptLedger as Ledger
import Muninn.IdentityCheckpoint as Checkpoint
import Muninn.TransactionSequence as Sequence
import Muninn.Dialogue as D
import Relation.Nullary
import Data.Nat as Nat
open import Muninn.Types using (FilePath)
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false)
open import Data.String using (String)
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
module DB = O.DB

module Family (family familySlot checkoutSlot policyPointer generation : ℕ)
  (request : I.IntentInput I.convertDirectory) (source : Identity.Observation)
  (git : Identity.GitObservation) (gitPresent : Identity.Observation.gitInfo source ≡ just git)
  (sourceMatches : I.FamilyTarget.location (I.Mutation.input request) ≡ Identity.Observation.requested source)
  (before : O.World) (current : Policy.Family.Saved family policyPointer before)
  (registration : O.RegistrationInfo) (saved : Identity.FamilyBinding)
  (bindingAt : O.RegistrationInfo.identity registration ≡ just saved)
  (idMatches : O.RegistrationInfo.id registration ≡ Identity.FamilyBinding.id saved)
  (permitted : Discovery.ConversionPermit request saved)
  (checkout : O.CheckoutInfo) (oldCheckout : Identity.CheckoutBinding)
  (checkoutAt : O.CheckoutInfo.identity checkout ≡ just oldCheckout)
  (checkoutId : O.CheckoutInfo.id checkout ≡ Identity.CheckoutBinding.id oldCheckout)
  (checkoutIncarnation : O.CheckoutInfo.incarnation checkout ≡ Identity.CheckoutBinding.incarnation oldCheckout)
  (registered : DB.lookup familySlot before ≡ just (O.recordOf (O.family family) (O.registration registration)))
  (checkedOut : DB.lookup checkoutSlot before ≡ just (O.recordOf (O.family family) (O.checkout checkout)))
  (onlyCheckout : ∀ key info → DB.lookup key before ≡ just (O.recordOf (O.family family) (O.checkout info)) → key ≡ checkoutSlot)
  (advanceBase : Bool) where
  owner = O.family family
  module Stored = Policy.Family family policyPointer
  selection = Stored.rule current
  module C = Content.Family selection
  oldView = C.visible before checkoutSlot
  gitContext = Git.context family checkoutSlot generation

  -- Ask Git for every retained path in this checkout and generation. Reuse
  -- content versions, but do not reuse directory-mode ignore decisions.
  record Selection : Set where
    field answer : ∀ path entry → oldView path ≡ just entry → Git.Answer (FilePath.value path)
          fresh : ∀ path entry found → Git.at (answer path entry found) ≡ gitContext

  record Admission : Set where
    field noRemoval : E.pendingRemovalFor owner before ≡ false
          explicit : Discovery.ConversionPermit request saved
          gitObserved : Identity.Observation.gitInfo source ≡ just git
          requested : I.FamilyTarget.location (I.Mutation.input request) ≡ Identity.Observation.requested source
          familyLocated : DB.lookup familySlot before ≡ just (O.recordOf owner (O.registration registration))
          familyBound : O.RegistrationInfo.identity registration ≡ just saved
          familyNamed : O.RegistrationInfo.id registration ≡ Identity.FamilyBinding.id saved
          policyNamed : O.PolicyVersionInfo.familyId (Stored.Saved.info current) ≡ Identity.FamilyBinding.id saved
          checkoutLocated : DB.lookup checkoutSlot before ≡ just (O.recordOf owner (O.checkout checkout))
          checkoutBound : O.CheckoutInfo.identity checkout ≡ just oldCheckout
          checkoutNamed : O.CheckoutInfo.id checkout ≡ Identity.CheckoutBinding.id oldCheckout
          incarnationMatches : O.CheckoutInfo.incarnation checkout ≡ Identity.CheckoutBinding.incarnation oldCheckout
          singleDirectoryCheckout : ∀ key info → DB.lookup key before ≡ just (O.recordOf owner (O.checkout info)) → key ≡ checkoutSlot

  module Plan (selectionEvidence : Selection) where
    reclassify : ∀ path → (value : Maybe Content.Entry) → oldView path ≡ value → Maybe Content.Entry
    reclassify path nothing found = nothing
    reclassify path (just indexed) found = just (Content.entry (Content.Entry.version indexed)
      (Git.ignored (Selection.answer selectionEvidence path indexed found)))
    desired : Publication.Files.Manifest
    desired path = reclassify path (oldView path) refl
    module P = Publication.Plan selection before checkoutSlot advanceBase desired

    newRegistration : O.RegistrationInfo
    newRegistration = record registration { identity = just (Identity.convertBinding saved git) }
    newCheckout : O.CheckoutInfo
    newCheckout = record checkout { identity = just (record oldCheckout
      { root = Identity.Observation.root source; rootObject = Identity.Observation.rootObject source
      ; gitAdmin = Identity.GitObservation.adminObject git }) }
    registrationRow = O.recordOf owner (O.registration newRegistration)
    checkoutRow = O.recordOf owner (O.checkout newCheckout)

    identityPreserved : O.RegistrationInfo.id newRegistration ≡ O.RegistrationInfo.id registration ×
      O.CheckoutInfo.id newCheckout ≡ O.CheckoutInfo.id checkout ×
      O.CheckoutInfo.incarnation newCheckout ≡ O.CheckoutInfo.incarnation checkout
    identityPreserved = refl , refl , refl
    authorizationPreserved : O.RegistrationInfo.indexingEnabled newRegistration ≡ O.RegistrationInfo.indexingEnabled registration
    authorizationPreserved = refl
    pausedPreserved : O.CheckoutInfo.paused newCheckout ≡ O.CheckoutInfo.paused checkout
    pausedPreserved = refl

    record Outcome (after : O.World) : Set where
      field content : P.Represents after
            storeValid : O.Admissible after
            viewsValid : Views.Valid after
            registrationAt : DB.lookup familySlot after ≡ just registrationRow
            checkoutStored : DB.lookup checkoutSlot after ≡ just checkoutRow
            snapshot pointer : ℕ
            nodes edges : List ℕ
            payload : String
            published : DB.lookup pointer after ≡ just (O.recordOf owner (O.publishedView checkoutSlot snapshot))
            structure : DB.lookup snapshot after ≡ just (O.recordOf owner (O.structuralSnapshot checkoutSlot nodes edges payload))
            structureSelected : Publication.M.project selection after (O.recordOf owner (O.structuralSnapshot checkoutSlot nodes edges payload)) ≡
              O.recordOf owner (O.structuralSnapshot checkoutSlot nodes edges payload)
            baseRole : Σ ℕ (λ slot → Σ ℕ (λ baseCheckout →
              DB.lookup slot before ≡ just (O.recordOf owner (O.basePointer baseCheckout)) ×
              (advanceBase ≡ Relation.Nullary.does (checkoutSlot Nat.≟ baseCheckout))))
            -- Content and curated/configuration data are retained. Only view
            -- bindings, selectors, the two metadata rows and own receipt change.
            retained : ∀ key value → key ≢ familySlot → key ≢ checkoutSlot →
              O.kind (O.body value) ≢ O.baseBindingK → O.kind (O.body value) ≢ O.deltaBindingK →
              O.kind (O.body value) ≢ O.publishedViewK → O.kind (O.body value) ≢ O.receiptK →
              DB.lookup key before ≡ just value → DB.lookup key after ≡ just value
            otherFamilies : ∀ key value → O.owner value ≢ owner →
              (DB.lookup key before ≡ just value → DB.lookup key after ≡ just value) ×
              (DB.lookup key after ≡ just value → DB.lookup key before ≡ just value)
            cleanupSlot : ℕ
            cleanupText : String
            cleanupAt : DB.lookup cleanupSlot after ≡ just (O.recordOf owner
              (O.cleanupWork (I.Mutation.operationId request) (Publication.M.capture selection before) cleanupText))

    module Accepted (receiptSlot : ℕ) (progress : R.Work)
      (found : Ledger.find (I.Mutation.operationId request) before ≡ just (Ledger.found receiptSlot owner
        (R.active (Meaning.mutation Meaning.kConvertDirectory request) refl progress)))
      (located : DB.lookup receiptSlot before ≡ just (Ledger.recordAt owner
        (R.active (Meaning.mutation Meaning.kConvertDirectory request) refl progress))) where
      id = I.Mutation.operationId request
      input = Meaning.mutation Meaning.kConvertDirectory request
      module Guard = Publication.PolicyGuard owner policyPointer (Stored.Saved.version current)

      finish : String → DB.Transaction String
      finish result = DB.put familySlot registrationRow (DB.put checkoutSlot checkoutRow (DB.commit result))
      changed : O.World → O.World
      changed middle = DB.write checkoutSlot checkoutRow (DB.write familySlot registrationRow middle)

      record Prepared : Set where
        field admitted : Admission
              body : DB.Transaction String
              result continuation : String
              middle : O.World
              performs : DB.evaluate body before ≡ DB.committed result middle
              -- The precise composition is fixed here, including both metadata
              -- writes. This obligation also requires actual-row admission.
              isolates : ∀ world reply after → DB.evaluate (Sequence.then body finish) world ≡ DB.committed reply after → Ledger.ReceiptFrame world after
              changedValid : O.Admissible (changed middle)
              outcome : Outcome (DB.write receiptSlot (Ledger.recordAt {id = id} owner
                (R.active input refl (R.nextWork progress Data.List.[] result))) (changed middle))

      module Run (prepared : Prepared) where
        open Prepared prepared
        raw : Ledger.Effect
        raw = record { transaction = Sequence.then body finish; guidance = guidance; isolates = isolates }
          where
          guidance : String → D.Prompt
          guidance value = D.prompt (D.text 'C' "onverting the directory registration; the saved directory view remains available until the Git view is ready.") (D.text 'C' "ontinue this request to check progress.") Data.List.[]
        effect = Guard.effect raw continuation
        performsFinal : DB.evaluate (Ledger.Effect.transaction effect) before ≡ DB.committed result (changed middle)
        performsFinal = trans (Guard.ready (Ledger.Effect.transaction raw) continuation before (Stored.Saved.pointerAt current) (Admission.noRemoval admitted))
          (Sequence.committed body finish before result middle performs)
        module Seal = Checkpoint.Run id input refl owner receiptSlot progress result effect before (changed middle) changedValid found located performsFinal
        open Seal public
        goal : Outcome after
        goal = outcome
        selectedView : ∀ path → C.visible after checkoutSlot path ≡ P.safeDesired path
        selectedView = P.selectedView after (Outcome.content goal) (checkout , checkedOut)

        convergesToGoal : ∀ observed reply final → O.Execution.Interrupted (O.Execution.atomic Seal.request O.Execution.done) before observed →
          O.Execution.Completed (O.Execution.atomic Seal.request O.Execution.done) observed reply final → Outcome final
        convergesToGoal observed reply final interrupted completed =
          Relation.Binary.PropositionalEquality.subst Outcome (sym (Seal.converges observed reply final interrupted completed)) goal
