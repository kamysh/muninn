{-# OPTIONS --safe #-}
-- Completion certificates and constructive deletion progress.
module Muninn.CleanupCompletion where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.ExclusionClassifier as C
import Muninn.CleanupEffects as Effects
import Muninn.CleanupStorage as Storage
import Muninn.CleanupOrder as Order
import Muninn.FiniteClosure as F
open import Data.Nat using (ℕ; _<_; _≤_)
open import Data.Nat.Properties using (<-≤-trans; <-irrefl)
open import Data.Bool using (Bool; true; false)
open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.All as All
open All using (All)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_; does)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
module DB = O.DB

Incoming : ℕ → O.World → Set
Incoming key world = Σ (ℕ × O.Record) (λ row → row ∈ world ×
  Σ O.Reference (λ ref → ref ∈ O.references (O.body (proj₂ row)) × O.target ref ≡ key))

incomingSource : ∀ {key world} → Incoming key world → ℕ
incomingSource ((source , value) , present , ref , included , same) = source

incoming? : ∀ key world → Dec (Incoming key world)
incoming? key world = F.choose
  (λ row → Σ O.Reference (λ ref → ref ∈ O.references (O.body (proj₂ row)) × O.target ref ≡ key))
  (λ row → F.choose (λ ref → O.target ref ≡ key) (λ ref → O.target ref Data.Nat.≟ key)
    (O.references (O.body (proj₂ row)))) world

noIncoming : ∀ key world → ¬ Incoming key world → All (O.NoIncomingTo key) world
noIncoming key world none = All.tabulate (λ {row} present → All.tabulate
  (λ {ref} included same → none (row , present , ref , included , same)))

decisionTrue : ∀ {A : Set} (decision : Dec A) → A → does decision ≡ true
decisionTrue (yes proof) present = refl
decisionTrue (no denied) present = ⊥-elim (denied present)

decisionWitness : ∀ {A : Set} (decision : Dec A) → does decision ≡ true → A
decisionWitness (yes proof) present = proof
decisionWitness (no denied) ()

familyReferenceOwner : ∀ source target id → O.MayReference source target → target ≡ O.family id → source ≡ O.family id
familyReferenceOwner source .source id O.own owned = owned
familyReferenceOwner source .O.installation id O.shared ()

module Model (excluded : List String → String → Bool) where
  module M = E.Model excluded
  module Classifier = C.Model excluded
  module Edits = Effects.Model excluded
  module Store = Storage.Model excluded

  module Contract (selection : E.Rule) (accepted : O.World) (intent : M.Intent selection accepted) where
    module Core = Edits.Core selection accepted intent

    Pending : ℕ → O.World → Set
    Pending key world = C.At world key (λ value → key ∈ M.Intent.keys intent ×
      (O.owner value ≡ E.targetOwner selection × (E.indexed value ≡ true ×
        (¬ M.Needed selection world key ⊎ (M.Needed selection world key × Core.Changed world value)))))

    pending? : ∀ key world → Dec (Pending key world)
    pending? key world = C.at? world key _ (λ value →
      C.both (F.member key (M.Intent.keys intent)) (C.both (E.ownerEqual (O.owner value) (E.targetOwner selection))
        (C.both (C.true? (E.indexed value))
          (C.either (Effects.not? (Assessment.needed? key)) (C.both (Assessment.needed? key) (Core.changed? world value))))))
      where module Assessment = Classifier.Assessment selection world

    pendingCaptured : ∀ key world → Pending key world → key ∈ M.Intent.keys intent
    pendingCaptured key world (value , found , captured , remaining) = captured

    -- The projection is either already exact or exposes an actual changed
    -- indexed member, with the ownership needed by the existing edit contract.
    projectionView : ∀ world value → (M.project selection world value ≡ value) ⊎
      (O.owner value ≡ E.targetOwner selection × (E.indexed value ≡ true × Core.Changed world value))
    projectionView world value with Store.shape selection world value
    ... | Store.plain equal = inj₁ equal
    ... | Store.snapshot owner selected nodes edges payload with E.ownerEqual owner (E.targetOwner selection)
    ...   | no different = inj₁ refl
    ...   | yes owned with Effects.listEqual (E.filterKeys (M.symbolVisible selection world owner selected) nodes) nodes
      | Effects.listEqual (E.filterKeys (M.edgeVisible selection world owner selected) edges) edges
    ...     | yes sameNodes | yes sameEdges = inj₁ (cong₂
        (λ ns es → O.recordOf owner (O.structuralSnapshot selected ns es payload)) sameNodes sameEdges)
    ...     | no changedNodes | _ = inj₂ (owned , refl , inj₁ changedNodes)
    ...     | _ | no changedEdges = inj₂ (owned , refl , inj₂ changedEdges)

    NoPending : O.World → Set
    NoPending world = ∀ key → ¬ Pending key world

    completeWithoutPending : ∀ world → O.Unique world → NoPending world → M.Complete selection accepted intent world world
    completeWithoutPending world unique none = record
      { safety = M.safetyReflexive selection world; uniqueAfter = unique
      ; canonical = canonical; outsideCapture = λ key value found outside → found
      ; reclaimed = λ key value captured found owned indexed unneeded →
          ⊥-elim (none key (value , found , captured , owned , indexed , inj₁ unneeded))
      ; noNewRecords = Order.lookupExists world }
      where
      canonical : ∀ key value → key ∈ M.Intent.keys intent → DB.lookup key world ≡ just value → M.Needed selection world key →
        DB.lookup key world ≡ just (M.project selection world value)
      canonical key value captured found needed with projectionView world value
      ... | inj₁ exact = trans found (cong just (sym exact))
      ... | inj₂ (owned , indexed , changed) = ⊥-elim (none key (value , found , captured , owned , indexed , inj₂ (needed , changed)))

    pendingExcludesComplete : ∀ key world → Pending key world → ¬ M.Complete selection accepted intent world world
    pendingExcludesComplete key world (value , found , captured , owned , indexed , inj₁ unneeded) completed =
      Effects.presentNotAbsent (trans (sym found) (M.Complete.reclaimed completed key value captured found owned indexed unneeded))
    pendingExcludesComplete key world (value , found , captured , owned , indexed , inj₂ (needed , changed)) completed =
      Core.changedIsActual world value changed (sym (just-injective
        (trans (sym found) (M.Complete.canonical completed key value captured found needed))))

    -- Candidates omit only the incoming-reference guard. The ordering proof
    -- below derives a real Removal in a closed, nonempty candidate component.
    Candidate : ℕ → O.World → Set
    Candidate key world = C.At world key (λ value → key ∈ M.Intent.keys intent ×
      (O.owner value ≡ E.targetOwner selection × (E.indexed value ≡ true ×
        (¬ M.Needed selection world key × ¬ M.Protected selection world key))))

    candidate? : ∀ key world → Dec (Candidate key world)
    candidate? key world = C.at? world key _ (λ value →
      C.both (F.member key (M.Intent.keys intent)) (C.both (E.ownerEqual (O.owner value) (E.targetOwner selection))
        (C.both (C.true? (E.indexed value)) (C.both (Effects.not? (Assessment.needed? key))
          (Effects.not? (Assessment.protected? key))))))
      where module Assessment = Classifier.Assessment selection world

    candidates : O.World → List ℕ
    candidates world = E.filterKeys (λ key → does (candidate? key world)) (M.Intent.keys intent)

    candidatesSound : ∀ world key → key ∈ candidates world → Candidate key world
    candidatesSound world key present = decisionWitness (candidate? key world)
      (E.filterKeysSound (λ key → does (candidate? key world)) (M.Intent.keys intent) key present)

    candidatesComplete : ∀ world key → Candidate key world → key ∈ candidates world
    candidatesComplete world key proof@(value , found , captured , remaining) =
      E.filterKeysComplete (λ key → does (candidate? key world)) (M.Intent.keys intent) key captured
        (decisionTrue (candidate? key world) proof)

    candidateRemoval : ∀ key world → Candidate key world → All (O.NoIncomingTo key) world → Core.Removal key world
    candidateRemoval key world (value , found , captured , owned , indexed , unneeded , unprotected) unreferenced =
      value , found , captured , owned , indexed , unneeded , unprotected , unreferenced

    incomingHigher : ∀ world key → O.Admissible world → (incoming : Incoming key world) →
      E.indexed (proj₂ (proj₁ incoming)) ≡ true → Order.rankAt key world < Order.rankAt (incomingSource incoming) world
    incomingHigher world key valid ((source , value) , present , ref , included , refl) indexed =
      Order.downDecreases world (Order.link source value ref
        (Order.memberLookup world source value (O.Admissible.unique valid) present) indexed included
        (All.lookup (All.lookup (O.Admissible.sound valid) present) included))

    -- A maximal-rank candidate cannot have an incoming edge from another
    -- candidate. This is a derived ordering fact, not a worker-supplied guard.
    maximalBoundary : ∀ world candidates chosen → O.Admissible world →
      (∀ key → key ∈ candidates → Candidate key world) →
      (∀ key → key ∈ candidates → Order.rankAt key world ≤ Order.rankAt chosen world) →
      (incoming : Incoming chosen world) → incomingSource incoming ∉ candidates
    maximalBoundary world candidates chosen valid suitable greatest incoming@((source , value) , present , ref , included , same) sourceIn
      with suitable source sourceIn
    ... | stored , found , captured , owned , indexed , unneeded , unprotected = <-irrefl refl
      (<-≤-trans (incomingHigher world chosen valid incoming
        (subst (λ v → E.indexed v ≡ true)
          (just-injective (trans (sym found) (Order.memberLookup world source value (O.Admissible.unique valid) present))) indexed))
        (greatest source sourceIn))

    closedComponentProgress : ∀ world candidates first → O.Admissible world → first ∈ candidates →
      (∀ key → key ∈ candidates → Candidate key world) →
      (∀ key → key ∈ candidates → (incoming : Incoming key world) → incomingSource incoming ∈ candidates) →
      Σ ℕ (λ key → key ∈ candidates × Core.Removal key world)
    closedComponentProgress world [] first valid () suitable closed
    closedComponentProgress world (head ∷ rest) first valid present suitable closed with Order.maximum world head rest
    ... | chosen , chosenIn , greatest with incoming? chosen world
    ...   | no none = chosen , chosenIn , candidateRemoval chosen world (suitable chosen chosenIn) (noIncoming chosen world none)
    ...   | yes incoming = ⊥-elim (maximalBoundary world (head ∷ rest) chosen valid suitable greatest incoming (closed chosen chosenIn incoming))
