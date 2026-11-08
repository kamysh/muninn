{-# OPTIONS --safe #-}
module Muninn.CleanupNeedScope where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.ExclusionClassifier as C
import Muninn.CleanupCompletion as Completion
import Muninn.CleanupEffects as Effects
import Muninn.ReceiptTypes as Receipt
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.String using (String)
open import Data.List using (List)
import Muninn.CleanupOrder as Order
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Relation.Unary.All as All
open All using (All; []; _∷_)
open import Data.Maybe using (just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
module DB = O.DB

kindIndexed : O.Kind → Bool
kindIndexed O.registrationK = false
kindIndexed O.checkoutK = false
kindIndexed O.creationIntentK = false
kindIndexed O.defaultsK = false
kindIndexed O.policyVersionK = false
kindIndexed O.currentPolicyK = false
kindIndexed O.noteK = false
kindIndexed O.notePostingK = false
kindIndexed O.noteVectorK = false
kindIndexed O.fileVersionK = true
kindIndexed O.baseBindingK = true
kindIndexed O.deltaBindingK = true
kindIndexed O.basePointerK = true
kindIndexed O.chunkK = true
kindIndexed O.postingK = true
kindIndexed O.vectorK = true
kindIndexed O.symbolK = true
kindIndexed O.edgeK = true
kindIndexed O.structuralSnapshotK = true
kindIndexed O.legacyK = true
kindIndexed O.stagingK = true
kindIndexed O.acceptedWorkK = false
kindIndexed O.cleanupWorkK = false
kindIndexed O.activeReaderK = false
kindIndexed O.continuationK = false
kindIndexed O.receiptK = false
kindIndexed O.migrationK = false
kindIndexed O.usageK = false
kindIndexed O.bootstrapK = false
kindIndexed O.modelCacheK = false
kindIndexed O.coordinationK = false
kindIndexed O.schemaResourceK = false
kindIndexed O.graphResourceK = true
kindIndexed O.logFileK = false
kindIndexed O.bootstrapStageK = false
bodyIndexed : ∀ value → E.indexed value ≡ kindIndexed (O.kind (O.body value))

bodyIndexed (O.recordOf owner (O.registration _)) = refl
bodyIndexed (O.recordOf owner (O.checkout _)) = refl
bodyIndexed (O.recordOf owner (O.creationIntent _)) = refl
bodyIndexed (O.recordOf owner (O.defaults _)) = refl
bodyIndexed (O.recordOf owner (O.policyVersion _ _)) = refl
bodyIndexed (O.recordOf owner (O.currentPolicy _)) = refl
bodyIndexed (O.recordOf owner (O.note _)) = refl
bodyIndexed (O.recordOf owner (O.notePosting _ _)) = refl
bodyIndexed (O.recordOf owner (O.noteVector _ _)) = refl
bodyIndexed (O.recordOf owner (O.fileVersion _)) = refl
bodyIndexed (O.recordOf owner (O.baseBinding _ _)) = refl
bodyIndexed (O.recordOf owner (O.deltaBinding _ _ _)) = refl
bodyIndexed (O.recordOf owner (O.basePointer _)) = refl
bodyIndexed (O.recordOf owner (O.chunk _ _)) = refl
bodyIndexed (O.recordOf owner (O.posting _ _)) = refl
bodyIndexed (O.recordOf owner (O.vector _ _)) = refl
bodyIndexed (O.recordOf owner (O.symbol _ _ _)) = refl
bodyIndexed (O.recordOf owner (O.edge _ _ _)) = refl
bodyIndexed (O.recordOf owner (O.structuralSnapshot _ _ _ _)) = refl
bodyIndexed (O.recordOf owner (O.legacy _ _)) = refl
bodyIndexed (O.recordOf owner (O.staging _ _)) = refl
bodyIndexed (O.recordOf owner (O.acceptedWork _ _)) = refl
bodyIndexed (O.recordOf owner (O.cleanupWork _ _)) = refl
bodyIndexed (O.recordOf owner (O.activeReader _ _)) = refl
bodyIndexed (O.recordOf owner (O.continuation _ _)) = refl
bodyIndexed (O.recordOf owner (O.receipt (Receipt.entry id (Receipt.active input names work)))) = refl
bodyIndexed (O.recordOf owner (O.receipt (Receipt.entry id (Receipt.finished input names reply)))) = refl
bodyIndexed (O.recordOf owner (O.receipt (Receipt.entry id (Receipt.used)))) = refl
bodyIndexed (O.recordOf owner (O.migration _)) = refl
bodyIndexed (O.recordOf owner (O.usage _)) = refl
bodyIndexed (O.recordOf owner (O.bootstrap _)) = refl
bodyIndexed (O.recordOf owner (O.modelCache _)) = refl
bodyIndexed (O.recordOf owner (O.coordination _)) = refl
bodyIndexed (O.recordOf owner (O.schemaResource _)) = refl
bodyIndexed (O.recordOf owner (O.graphResource _ _ _)) = refl
bodyIndexed (O.recordOf owner (O.logFile _)) = refl
bodyIndexed (O.recordOf owner (O.bootstrapStage _)) = refl

andLeft : ∀ a b → a ∧ b ≡ true → a ≡ true
andLeft true b proof = refl
andLeft false b ()

andRight : ∀ a b → a ∧ b ≡ true → b ≡ true
andRight true b proof = proof
andRight false b ()

module Model (excluded : List String → String → Bool) where
  module M = E.Model excluded

  unindexedTargets : ∀ selection world value → E.indexed value ≡ false →
    All (λ ref → kindIndexed (O.expected ref) ≡ false) (M.referencesFor M.permanent selection world value)

  unindexedTargets selection world (O.recordOf owner (O.registration _)) proof = []
  unindexedTargets selection world (O.recordOf owner (O.checkout _)) proof = []
  unindexedTargets selection world (O.recordOf owner (O.creationIntent _)) proof = []
  unindexedTargets selection world (O.recordOf owner (O.defaults _)) proof = []
  unindexedTargets selection world (O.recordOf owner (O.policyVersion _ _)) proof = refl ∷ []
  unindexedTargets selection world (O.recordOf owner (O.currentPolicy _)) proof = refl ∷ []
  unindexedTargets selection world (O.recordOf owner (O.note _)) proof = []
  unindexedTargets selection world (O.recordOf owner (O.notePosting _ _)) proof = refl ∷ []
  unindexedTargets selection world (O.recordOf owner (O.noteVector _ _)) proof = refl ∷ []
  unindexedTargets selection world (O.recordOf owner (O.fileVersion _)) ()
  unindexedTargets selection world (O.recordOf owner (O.baseBinding _ _)) ()
  unindexedTargets selection world (O.recordOf owner (O.deltaBinding _ _ _)) ()
  unindexedTargets selection world (O.recordOf owner (O.basePointer _)) ()
  unindexedTargets selection world (O.recordOf owner (O.chunk _ _)) ()
  unindexedTargets selection world (O.recordOf owner (O.posting _ _)) ()
  unindexedTargets selection world (O.recordOf owner (O.vector _ _)) ()
  unindexedTargets selection world (O.recordOf owner (O.symbol _ _ _)) ()
  unindexedTargets selection world (O.recordOf owner (O.edge _ _ _)) ()
  unindexedTargets selection world (O.recordOf owner (O.structuralSnapshot _ _ _ _)) ()
  unindexedTargets selection world (O.recordOf owner (O.legacy _ _)) ()
  unindexedTargets selection world (O.recordOf owner (O.staging _ _)) ()
  unindexedTargets selection world (O.recordOf owner (O.acceptedWork _ _)) proof = []
  unindexedTargets selection world (O.recordOf owner (O.cleanupWork _ _)) proof = []
  unindexedTargets selection world (O.recordOf owner (O.activeReader _ _)) proof = []
  unindexedTargets selection world (O.recordOf owner (O.continuation _ _)) proof = []
  unindexedTargets selection world (O.recordOf owner (O.receipt (Receipt.entry id (Receipt.active input names work)))) proof = []
  unindexedTargets selection world (O.recordOf owner (O.receipt (Receipt.entry id (Receipt.finished input names reply)))) proof = []
  unindexedTargets selection world (O.recordOf owner (O.receipt (Receipt.entry id (Receipt.used)))) proof = []
  unindexedTargets selection world (O.recordOf owner (O.migration _)) proof = []
  unindexedTargets selection world (O.recordOf owner (O.usage _)) proof = []
  unindexedTargets selection world (O.recordOf owner (O.bootstrap _)) proof = []
  unindexedTargets selection world (O.recordOf owner (O.modelCache _)) proof = []
  unindexedTargets selection world (O.recordOf owner (O.coordination _)) proof = []
  unindexedTargets selection world (O.recordOf owner (O.schemaResource _)) proof = []
  unindexedTargets selection world (O.recordOf owner (O.graphResource _ _ _)) ()
  unindexedTargets selection world (O.recordOf owner (O.logFile _)) proof = []
  unindexedTargets selection world (O.recordOf owner (O.bootstrapStage _)) proof = []

  parentIndexed : ∀ selection world value ref → M.parentOf M.permanent selection world value ≡ just ref →
    kindIndexed (O.expected ref) ≡ true

  parentIndexed selection world (O.recordOf owner (O.registration _)) ref ()
  parentIndexed selection world (O.recordOf owner (O.checkout _)) ref ()
  parentIndexed selection world (O.recordOf owner (O.creationIntent _)) ref ()
  parentIndexed selection world (O.recordOf owner (O.defaults _)) ref ()
  parentIndexed selection world (O.recordOf owner (O.policyVersion _ _)) ref ()
  parentIndexed selection world (O.recordOf owner (O.currentPolicy _)) ref ()
  parentIndexed selection world (O.recordOf owner (O.note _)) ref ()
  parentIndexed selection world (O.recordOf owner (O.notePosting _ _)) ref ()
  parentIndexed selection world (O.recordOf owner (O.noteVector _ _)) ref ()
  parentIndexed selection world (O.recordOf owner (O.fileVersion _)) ref ()
  parentIndexed selection world (O.recordOf owner (O.baseBinding _ _)) ref ()
  parentIndexed selection world (O.recordOf owner (O.deltaBinding _ _ _)) ref ()
  parentIndexed selection world (O.recordOf owner (O.basePointer _)) ref ()
  parentIndexed selection world (O.recordOf owner (O.chunk _ _)) ref found with just-injective found
  ... | refl = refl
  parentIndexed selection world (O.recordOf owner (O.posting _ _)) ref found with just-injective found
  ... | refl = refl
  parentIndexed selection world (O.recordOf owner (O.vector _ _)) ref found with just-injective found
  ... | refl = refl
  parentIndexed selection world (O.recordOf owner (O.symbol version path payload)) ref found with M.versionPublishedAtPath selection world owner path version
  ... | false with found
  ...   | ()
  parentIndexed selection world (O.recordOf owner (O.symbol version path payload)) ref found | true with just-injective found
  ... | refl = refl
  parentIndexed selection world (O.recordOf owner (O.edge _ _ _)) ref ()
  parentIndexed selection world (O.recordOf owner (O.structuralSnapshot _ _ _ _)) ref ()
  parentIndexed selection world (O.recordOf owner (O.legacy _ _)) ref ()
  parentIndexed selection world (O.recordOf owner (O.staging _ _)) ref ()
  parentIndexed selection world (O.recordOf owner (O.acceptedWork _ _)) ref ()
  parentIndexed selection world (O.recordOf owner (O.cleanupWork _ _)) ref ()
  parentIndexed selection world (O.recordOf owner (O.activeReader _ _)) ref ()
  parentIndexed selection world (O.recordOf owner (O.continuation _ _)) ref ()
  parentIndexed selection world (O.recordOf owner (O.receipt (Receipt.entry id (Receipt.active input names work)))) ref ()
  parentIndexed selection world (O.recordOf owner (O.receipt (Receipt.entry id (Receipt.finished input names reply)))) ref ()
  parentIndexed selection world (O.recordOf owner (O.receipt (Receipt.entry id (Receipt.used)))) ref ()
  parentIndexed selection world (O.recordOf owner (O.migration _)) ref ()
  parentIndexed selection world (O.recordOf owner (O.usage _)) ref ()
  parentIndexed selection world (O.recordOf owner (O.bootstrap _)) ref ()
  parentIndexed selection world (O.recordOf owner (O.modelCache _)) ref ()
  parentIndexed selection world (O.recordOf owner (O.coordination _)) ref ()
  parentIndexed selection world (O.recordOf owner (O.schemaResource _)) ref ()
  parentIndexed selection world (O.recordOf owner (O.graphResource _ _ _)) ref ()
  parentIndexed selection world (O.recordOf owner (O.logFile _)) ref ()
  parentIndexed selection world (O.recordOf owner (O.bootstrapStage _)) ref ()

  referenceSourceIndexed : ∀ selection world value ref → ref ∈ M.referencesFor M.permanent selection world value →
    kindIndexed (O.expected ref) ≡ true → E.indexed value ≡ true
  referenceSourceIndexed selection world value ref present targetIndex with E.indexed value in indexed
  ... | true = refl
  ... | false = ⊥-elim (Effects.trueIsNotFalse (trans (sym targetIndex)
      (All.lookup (unindexedTargets selection world value indexed) present)))

  rootRegistration : ∀ selection world role → E.indexedRole role ≡ true → M.rootedRole selection world role ≡ true →
    M.familyRegistered selection world ≡ true
  rootRegistration selection world E.administrative () rooted
  rootRegistration selection world E.holder () rooted
  rootRegistration selection world E.artifact indexed ()
  rootRegistration selection world (E.attached parent gate) indexed ()
  rootRegistration selection world E.baselineAnchor indexed rooted =
    andLeft _ (M.anyCheckoutLive selection world) rooted
  rootRegistration selection world (E.baselineBinding path) indexed rooted =
    andLeft _ (M.anyCheckoutLive selection world ∧ M.included selection (E.targetOwner selection) path) rooted
  rootRegistration selection world (E.checkoutBinding selected path) indexed rooted =
    andLeft _ (M.checkoutLive selection world selected ∧ M.included selection (E.targetOwner selection) path) rooted
  rootRegistration selection world (E.snapshot selected) indexed rooted = andLeft _ (M.checkoutLive selection world selected) rooted
  rootRegistration selection world (E.legacyFile path) indexed rooted =
    andLeft _ (M.legacyReadable selection world ∧ M.included selection (E.targetOwner selection) path) rooted
  rootRegistration selection world (E.graphContainer Data.Maybe.nothing inUse) indexed rooted =
    andLeft _ (M.anyCheckoutLive selection world) (andRight inUse _ rooted)
  rootRegistration selection world (E.graphContainer (just selected) inUse) indexed rooted =
    andLeft _ (M.checkoutLive selection world selected) (andRight inUse _ rooted)

  ownedRootRegistration : ∀ selection world value → O.owner value ≡ E.targetOwner selection → E.indexed value ≡ true →
    M.rooted selection world value ≡ true → M.familyRegistered selection world ≡ true
  ownedRootRegistration selection world value owned indexed rooted with E.ownerEqual (O.owner value) (E.targetOwner selection)
  ... | yes same = rootRegistration selection world (E.classify (O.body value)) indexed rooted
  ... | no different = ⊥-elim (different owned)

  Component : E.Rule → O.World → ℕ → Set
  Component selection world key = C.At world key (λ value → O.owner value ≡ E.targetOwner selection × E.indexed value ≡ true)

  incomingClosed : ∀ selection world {source target} → M.Dependency M.permanent selection world source target →
    Component selection world target → Component selection world source
  incomingClosed selection world (M.reference source value ref found included resolved) (target , targetFound , owned , indexed) =
    value , found , sourceOwned , referenceSourceIndexed selection world value ref included expectedIndexed
    where
    sameTarget : O.Resolves.value resolved ≡ target
    sameTarget = just-injective (trans (sym (O.Resolves.found resolved)) targetFound)
    expectedIndexed : kindIndexed (O.expected ref) ≡ true
    expectedIndexed = trans (sym (cong kindIndexed (O.Resolves.rightKind resolved)))
      (trans (sym (bodyIndexed (O.Resolves.value resolved))) (subst (λ v → E.indexed v ≡ true) (sym sameTarget) indexed))
    sourceOwned : O.owner value ≡ E.targetOwner selection
    sourceOwned = Completion.familyReferenceOwner (O.owner value) (O.owner (O.Resolves.value resolved)) (E.family selection)
      (O.Resolves.rightOwner resolved) (trans (cong O.owner sameTarget) owned)
  incomingClosed selection world (M.attachment parent parentValue child childValue parentFound childFound attached sameOwner)
    (target , targetFound , owned , indexed) = parentValue , parentFound ,
      trans sameOwner (trans (cong O.owner sameTarget) owned) ,
      trans (bodyIndexed parentValue) (parentIndexed selection world childValue (O.reference parent (O.kind (O.body parentValue))) attached)
    where
    sameTarget : childValue ≡ target
    sameTarget = just-injective (trans (sym childFound) targetFound)

  neededRegistration : ∀ selection world key value → DB.lookup key world ≡ just value →
    O.owner value ≡ E.targetOwner selection → E.indexed value ≡ true → M.Needed selection world key →
    M.familyRegistered selection world ≡ true
  neededRegistration selection world key value found owned indexed needed with M.familyRegistered selection world in registered
  ... | true = refl
  ... | false = ⊥-elim (M.rootlessComponentIsUnneeded selection world (Component selection world) noRoots
      (incomingClosed selection world) key (value , found , owned , indexed) needed)
    where
    noRoots : ∀ key value → Component selection world key → DB.lookup key world ≡ just value → ¬ (M.rooted selection world value ≡ true)
    noRoots key value (stored , present , owned , indexed) found rooted with just-injective (trans (sym present) found)
    ... | refl = Effects.trueIsNotFalse (trans (sym (ownedRootRegistration selection world value owned indexed rooted)) registered)

  constantNotSnapshot : ∀ keys kind → kind ≢ O.structuralSnapshotK →
    All (λ ref → O.expected ref ≢ O.structuralSnapshotK) (Data.List.map (λ key → O.reference key kind) keys)
  constantNotSnapshot Data.List.[] kind distinct = []
  constantNotSnapshot (key Data.List.∷ keys) kind distinct = distinct ∷ constantNotSnapshot keys kind distinct

  permanentTargets : ∀ selection world value →
    All (λ ref → O.expected ref ≢ O.structuralSnapshotK) (M.referencesFor M.permanent selection world value)

  permanentTargets selection world (O.recordOf owner (O.registration _)) = []
  permanentTargets selection world (O.recordOf owner (O.checkout _)) = []
  permanentTargets selection world (O.recordOf owner (O.creationIntent _)) = []
  permanentTargets selection world (O.recordOf owner (O.defaults _)) = []
  permanentTargets selection world (O.recordOf owner (O.policyVersion _ _)) = (λ ()) ∷ []
  permanentTargets selection world (O.recordOf owner (O.currentPolicy _)) = (λ ()) ∷ []
  permanentTargets selection world (O.recordOf owner (O.note _)) = []
  permanentTargets selection world (O.recordOf owner (O.notePosting _ _)) = (λ ()) ∷ []
  permanentTargets selection world (O.recordOf owner (O.noteVector _ _)) = (λ ()) ∷ []
  permanentTargets selection world (O.recordOf owner (O.fileVersion _)) = []
  permanentTargets selection world (O.recordOf owner (O.baseBinding _ _)) = (λ ()) ∷ []
  permanentTargets selection world (O.recordOf owner (O.deltaBinding selected Data.Maybe.nothing path)) = (λ ()) ∷ []
  permanentTargets selection world (O.recordOf owner (O.deltaBinding selected (just version) path)) = (λ ()) ∷ (λ ()) ∷ []
  permanentTargets selection world (O.recordOf owner (O.basePointer _)) = (λ ()) ∷ []
  permanentTargets selection world (O.recordOf owner (O.chunk _ _)) = (λ ()) ∷ []
  permanentTargets selection world (O.recordOf owner (O.posting _ _)) = (λ ()) ∷ []
  permanentTargets selection world (O.recordOf owner (O.vector _ _)) = (λ ()) ∷ []
  permanentTargets selection world (O.recordOf owner (O.symbol _ _ _)) = (λ ()) ∷ []
  permanentTargets selection world (O.recordOf owner (O.edge _ _ _)) = (λ ()) ∷ (λ ()) ∷ []
  permanentTargets selection world (O.recordOf owner (O.structuralSnapshot selected nodes edges payload)) with E.ownerEqual owner (E.targetOwner selection)
  ... | yes same = (λ ()) ∷ Order.join
    (constantNotSnapshot (E.filterKeys (M.symbolVisible selection world owner selected) nodes) O.symbolK (λ ()))
    (constantNotSnapshot (E.filterKeys (M.edgeVisible selection world owner selected) edges) O.edgeK (λ ()))
  ... | no different = (λ ()) ∷ Order.join (constantNotSnapshot nodes O.symbolK (λ ())) (constantNotSnapshot edges O.edgeK (λ ()))
  permanentTargets selection world (O.recordOf owner (O.legacy _ _)) = []
  permanentTargets selection world (O.recordOf owner (O.staging _ _)) = (λ ()) ∷ []
  permanentTargets selection world (O.recordOf owner (O.acceptedWork _ _)) = []
  permanentTargets selection world (O.recordOf owner (O.cleanupWork _ _)) = []
  permanentTargets selection world (O.recordOf owner (O.activeReader _ _)) = []
  permanentTargets selection world (O.recordOf owner (O.continuation _ _)) = []
  permanentTargets selection world (O.recordOf owner (O.receipt (Receipt.entry id (Receipt.active input names work)))) = []
  permanentTargets selection world (O.recordOf owner (O.receipt (Receipt.entry id (Receipt.finished input names reply)))) = []
  permanentTargets selection world (O.recordOf owner (O.receipt (Receipt.entry id (Receipt.used)))) = []
  permanentTargets selection world (O.recordOf owner (O.migration _)) = []
  permanentTargets selection world (O.recordOf owner (O.usage _)) = []
  permanentTargets selection world (O.recordOf owner (O.bootstrap _)) = []
  permanentTargets selection world (O.recordOf owner (O.modelCache _)) = []
  permanentTargets selection world (O.recordOf owner (O.coordination _)) = []
  permanentTargets selection world (O.recordOf owner (O.schemaResource _)) = []
  permanentTargets selection world (O.recordOf owner (O.graphResource _ _ _)) = []
  permanentTargets selection world (O.recordOf owner (O.logFile _)) = []
  permanentTargets selection world (O.recordOf owner (O.bootstrapStage _)) = []

  parentNotSnapshot : ∀ selection world value ref → M.parentOf M.permanent selection world value ≡ just ref → O.expected ref ≢ O.structuralSnapshotK

  parentNotSnapshot selection world (O.recordOf owner (O.registration _)) ref ()
  parentNotSnapshot selection world (O.recordOf owner (O.checkout _)) ref ()
  parentNotSnapshot selection world (O.recordOf owner (O.creationIntent _)) ref ()
  parentNotSnapshot selection world (O.recordOf owner (O.defaults _)) ref ()
  parentNotSnapshot selection world (O.recordOf owner (O.policyVersion _ _)) ref ()
  parentNotSnapshot selection world (O.recordOf owner (O.currentPolicy _)) ref ()
  parentNotSnapshot selection world (O.recordOf owner (O.note _)) ref ()
  parentNotSnapshot selection world (O.recordOf owner (O.notePosting _ _)) ref ()
  parentNotSnapshot selection world (O.recordOf owner (O.noteVector _ _)) ref ()
  parentNotSnapshot selection world (O.recordOf owner (O.fileVersion _)) ref ()
  parentNotSnapshot selection world (O.recordOf owner (O.baseBinding _ _)) ref ()
  parentNotSnapshot selection world (O.recordOf owner (O.deltaBinding _ _ _)) ref ()
  parentNotSnapshot selection world (O.recordOf owner (O.basePointer _)) ref ()
  parentNotSnapshot selection world (O.recordOf owner (O.chunk _ _)) ref found with just-injective found
  ... | refl = λ ()
  parentNotSnapshot selection world (O.recordOf owner (O.posting _ _)) ref found with just-injective found
  ... | refl = λ ()
  parentNotSnapshot selection world (O.recordOf owner (O.vector _ _)) ref found with just-injective found
  ... | refl = λ ()
  parentNotSnapshot selection world (O.recordOf owner (O.symbol version path payload)) ref found with M.versionPublishedAtPath selection world owner path version
  ... | false with found
  ...   | ()
  parentNotSnapshot selection world (O.recordOf owner (O.symbol version path payload)) ref found | true with just-injective found
  ... | refl = λ ()
  parentNotSnapshot selection world (O.recordOf owner (O.edge _ _ _)) ref ()
  parentNotSnapshot selection world (O.recordOf owner (O.structuralSnapshot _ _ _ _)) ref ()
  parentNotSnapshot selection world (O.recordOf owner (O.legacy _ _)) ref ()
  parentNotSnapshot selection world (O.recordOf owner (O.staging _ _)) ref ()
  parentNotSnapshot selection world (O.recordOf owner (O.acceptedWork _ _)) ref ()
  parentNotSnapshot selection world (O.recordOf owner (O.cleanupWork _ _)) ref ()
  parentNotSnapshot selection world (O.recordOf owner (O.activeReader _ _)) ref ()
  parentNotSnapshot selection world (O.recordOf owner (O.continuation _ _)) ref ()
  parentNotSnapshot selection world (O.recordOf owner (O.receipt (Receipt.entry id (Receipt.active input names work)))) ref ()
  parentNotSnapshot selection world (O.recordOf owner (O.receipt (Receipt.entry id (Receipt.finished input names reply)))) ref ()
  parentNotSnapshot selection world (O.recordOf owner (O.receipt (Receipt.entry id (Receipt.used)))) ref ()
  parentNotSnapshot selection world (O.recordOf owner (O.migration _)) ref ()
  parentNotSnapshot selection world (O.recordOf owner (O.usage _)) ref ()
  parentNotSnapshot selection world (O.recordOf owner (O.bootstrap _)) ref ()
  parentNotSnapshot selection world (O.recordOf owner (O.modelCache _)) ref ()
  parentNotSnapshot selection world (O.recordOf owner (O.coordination _)) ref ()
  parentNotSnapshot selection world (O.recordOf owner (O.schemaResource _)) ref ()
  parentNotSnapshot selection world (O.recordOf owner (O.graphResource _ _ _)) ref ()
  parentNotSnapshot selection world (O.recordOf owner (O.logFile _)) ref ()
  parentNotSnapshot selection world (O.recordOf owner (O.bootstrapStage _)) ref ()
