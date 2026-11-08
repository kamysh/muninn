{-# OPTIONS --safe #-}
-- State-level completion certificates and concrete dependency obstructions.
module Muninn.CleanupCompletion where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.ExclusionClassifier as C
import Muninn.CleanupEffects as Effects
import Muninn.CleanupStorage as Storage
import Muninn.CleanupProgress as Progress
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

blockedIncoming : ∀ key world → ¬ All (O.NoIncomingTo key) world → Incoming key world
blockedIncoming key world blocked with incoming? key world
... | yes witness = witness
... | no none = ⊥-elim (blocked (noIncoming key world none))

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
  module Passes = Progress.Model excluded

  module Contract (selection : E.Rule) (accepted : O.World) (intent : M.Intent selection accepted) where
    module Core = Edits.Core selection accepted intent
    module Pass = Passes.Pass selection accepted intent

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

    data Blocker (key : ℕ) (world : O.World) : Set where
      protection : M.Protected selection world key → Blocker key world
      capturedDependency : (dependency : Incoming key world) → incomingSource dependency ∈ M.Intent.keys intent → Blocker key world
      laterDependency : (dependency : Incoming key world) → incomingSource dependency ∉ M.Intent.keys intent → Blocker key world

    scopeDependency : ∀ key world → Incoming key world → Blocker key world
    scopeDependency key world dependency with F.member (incomingSource dependency) (M.Intent.keys intent)
    ... | yes captured = capturedDependency dependency captured
    ... | no outside = laterDependency dependency outside

    pendingAtRest : ∀ key world → Pass.NoEdit world → Pending key world → Blocker key world
    pendingAtRest key world quiet (value , found , captured , owned , indexed , remaining) with Classifier.Assessment.protected? selection world key
    ... | yes pinned = protection pinned
    ... | no unprotected with remaining
    ...   | inj₂ (needed , changed) = ⊥-elim (quiet key (inj₂ (value , found , captured , owned , indexed , needed , unprotected , changed)))
    ...   | inj₁ unneeded with Effects.unreferenced? key world
    ...     | yes unreferenced = ⊥-elim (quiet key (inj₁ (value , found , captured , owned , indexed , unneeded , unprotected , unreferenced)))
    ...     | no referenced = scopeDependency key world (blockedIncoming key world referenced)

    -- Completion is the existing contract at this observed state. Recovering
    -- the whole historical trace/frame and external waiting remains #77.
    data StateAssessment (world : O.World) : Set where
      ready : M.Complete selection accepted intent world world → StateAssessment world
      waiting : (key : ℕ) → Pending key world → Blocker key world →
        ¬ M.Complete selection accepted intent world world → StateAssessment world

    assess : ∀ world → O.Unique world → Pass.NoEdit world → StateAssessment world
    assess world unique quiet with F.choose (λ key → Pending key world) (λ key → pending? key world) (M.Intent.keys intent)
    ... | yes (key , captured , pending) = waiting key pending (pendingAtRest key world quiet pending) (pendingExcludesComplete key world pending)
    ... | no none = ready (completeWithoutPending world unique
        (λ key pending → none (key , pendingCaptured key world pending , pending)))

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

    stoppedComponentBoundary : ∀ world candidates first → O.Admissible world → Pass.NoEdit world → first ∈ candidates →
      (∀ key → key ∈ candidates → Candidate key world) →
      Σ ℕ (λ key → key ∈ candidates × Σ (Incoming key world) (λ incoming → incomingSource incoming ∉ candidates))
    stoppedComponentBoundary world [] first valid quiet () suitable
    stoppedComponentBoundary world (head ∷ rest) first valid quiet present suitable with Order.maximum world head rest
    ... | chosen , chosenIn , greatest with incoming? chosen world
    ...   | yes incoming = chosen , chosenIn , incoming , maximalBoundary world (head ∷ rest) chosen valid suitable greatest incoming
    ...   | no none = ⊥-elim (quiet chosen (inj₁ (candidateRemoval chosen world (suitable chosen chosenIn) (noIncoming chosen world none))))

    -- The canonical set has a proved complete classification. A boundary is
    -- not created by a caller omitting an inconvenient unprotected record.
    canonicalBoundary : ∀ world key → O.Admissible world → Pass.NoEdit world → Candidate key world →
      Σ ℕ (λ chosen → chosen ∈ candidates world ×
        Σ (Incoming chosen world) (λ incoming → incomingSource incoming ∉ candidates world))
    canonicalBoundary world key valid quiet candidate = stoppedComponentBoundary world (candidates world) key valid quiet
      (candidatesComplete world key candidate) (λ other present → candidatesSound world other present)

    controlRooted : ∀ world role → E.indexedRole role ≡ false → M.rootedRole selection world role ≡ true
    controlRooted world E.administrative proof = refl
    controlRooted world E.holder proof = refl
    controlRooted world E.artifact ()
    controlRooted world E.baselineAnchor ()
    controlRooted world (E.baselineBinding _) ()
    controlRooted world (E.checkoutBinding _ _) ()
    controlRooted world (E.snapshot _) ()
    controlRooted world (E.legacyFile _) ()
    controlRooted world (E.graphContainer _ _) ()
    controlRooted world (E.attached _ _) ()

    unindexedRooted : ∀ world value → E.indexed value ≡ false → M.rooted selection world value ≡ true
    unindexedRooted world value proof with E.ownerEqual (O.owner value) (E.targetOwner selection)
    ... | yes same = controlRooted world (E.classify (O.body value)) proof
    ... | no different = refl

    unneededIndexed : ∀ world key value → DB.lookup key world ≡ just value → ¬ M.Needed selection world key → E.indexed value ≡ true
    unneededIndexed world key value found unneeded with E.indexed value in indexed
    ... | true = refl
    ... | false = ⊥-elim (unneeded (M.root key value found (unindexedRooted world value indexed)))

    neededAtRest : ∀ world key value → Pass.NoEdit world → DB.lookup key world ≡ just value →
      key ∈ M.Intent.keys intent → M.Needed selection world key →
      (M.project selection world value ≡ value) ⊎ M.Protected selection world key
    neededAtRest world key value quiet found captured needed with projectionView world value
    ... | inj₁ exact = inj₁ exact
    ... | inj₂ (owned , indexed , changed) with Classifier.Assessment.protected? selection world key
    ...   | yes pinned = inj₂ pinned
    ...   | no unprotected = ⊥-elim (quiet key (inj₂ (value , found , captured , owned , indexed , needed , unprotected , changed)))

    referenceUse : ∀ world value ref → ref ∈ O.references (O.body value) → M.project selection world value ≡ value →
      (ref ∈ M.referencesFor M.permanent selection world value) ⊎ (ref ∈ M.heldReferences value)
    referenceUse world value ref included exact with E.classify (O.body value)
    ... | E.administrative = inj₁ (subst (λ v → ref ∈ O.references (O.body v)) (sym exact) included)
    ... | E.artifact = inj₁ (subst (λ v → ref ∈ O.references (O.body v)) (sym exact) included)
    ... | E.baselineAnchor = inj₁ (subst (λ v → ref ∈ O.references (O.body v)) (sym exact) included)
    ... | E.baselineBinding path = inj₁ (subst (λ v → ref ∈ O.references (O.body v)) (sym exact) included)
    ... | E.checkoutBinding selected path = inj₁ (subst (λ v → ref ∈ O.references (O.body v)) (sym exact) included)
    ... | E.snapshot selected = inj₁ (subst (λ v → ref ∈ O.references (O.body v)) (sym exact) included)
    ... | E.legacyFile path = inj₁ (subst (λ v → ref ∈ O.references (O.body v)) (sym exact) included)
    ... | E.graphContainer selected inUse = inj₁ (subst (λ v → ref ∈ O.references (O.body v)) (sym exact) included)
    ... | E.attached parent gate = inj₁ (subst (λ v → ref ∈ O.references (O.body v)) (sym exact) included)
    ... | E.holder = inj₂ included

    referencedFromNeeded : ∀ world source value ref → DB.lookup source world ≡ just value →
      ref ∈ O.references (O.body value) → O.Resolves world (O.owner value) ref →
      M.Needed selection world source → M.project selection world value ≡ value →
      M.Needed selection world (O.target ref) ⊎ M.Protected selection world (O.target ref)
    referencedFromNeeded world source value ref found included resolved needed exact with referenceUse world value ref included exact
    ... | inj₁ permanent = inj₁ (M.required needed (M.reference source value ref found permanent resolved))
    ... | inj₂ held = inj₂ (M.held source value ref found held resolved)

    protectedReference : ∀ world source value ref → DB.lookup source world ≡ just value →
      ref ∈ O.references (O.body value) → O.Resolves world (O.owner value) ref →
      M.Protected selection world source → M.Protected selection world (O.target ref)
    protectedReference world source value ref found included resolved pinned =
      M.required pinned (M.reference source value ref found included resolved)

    boundaryOutsideCapture : ∀ world key → O.Admissible world → Pass.NoEdit world → Candidate key world →
      (incoming : Incoming key world) → incomingSource incoming ∉ candidates world → incomingSource incoming ∉ M.Intent.keys intent
    boundaryOutsideCapture world key valid quiet (target , targetFound , targetCaptured , targetOwned , targetIndexed , unneeded , unprotected)
      incoming@((source , value) , present , ref , included , refl) outside sourceCaptured
      with Classifier.Assessment.needed? selection world source
    ... | yes needed with neededAtRest world source value quiet
        (Order.memberLookup world source value (O.Admissible.unique valid) present) sourceCaptured needed
    ...   | inj₂ pinned = unprotected (protectedReference world source value ref sourceFound included resolved pinned)
      where
      sourceFound = Order.memberLookup world source value (O.Admissible.unique valid) present
      resolved = All.lookup (All.lookup (O.Admissible.sound valid) present) included
    ...   | inj₁ exact with referencedFromNeeded world source value ref
        (Order.memberLookup world source value (O.Admissible.unique valid) present) included
        (All.lookup (All.lookup (O.Admissible.sound valid) present) included) needed exact
    ...     | inj₁ live = unneeded live
    ...     | inj₂ pinned = unprotected pinned
    boundaryOutsideCapture world key valid quiet (target , targetFound , targetCaptured , targetOwned , targetIndexed , unneeded , unprotected)
      incoming@((source , value) , present , ref , included , refl) outside sourceCaptured | no sourceUnneeded
      with Classifier.Assessment.protected? selection world source
    ... | yes pinned = unprotected (protectedReference world source value ref sourceFound included resolved pinned)
      where
      sourceFound = Order.memberLookup world source value (O.Admissible.unique valid) present
      resolved = All.lookup (All.lookup (O.Admissible.sound valid) present) included
    ... | no sourceUnprotected = outside (candidatesComplete world source
      (value , sourceFound , sourceCaptured , sourceOwned , unneededIndexed world source value sourceFound sourceUnneeded , sourceUnneeded , sourceUnprotected))
      where
      sourceFound : DB.lookup source world ≡ just value
      sourceFound = Order.memberLookup world source value (O.Admissible.unique valid) present
      resolved : O.Resolves world (O.owner value) ref
      resolved = All.lookup (All.lookup (O.Admissible.sound valid) present) included
      targetSame : O.Resolves.value resolved ≡ target
      targetSame = just-injective (trans (sym (O.Resolves.found resolved)) targetFound)
      sourceOwned : O.owner value ≡ E.targetOwner selection
      sourceOwned = familyReferenceOwner (O.owner value) (O.owner (O.Resolves.value resolved)) (E.family selection)
        (O.Resolves.rightOwner resolved) (trans (cong O.owner targetSame) targetOwned)

    stoppedUnprotectedDependency : ∀ world key → O.Admissible world → Pass.NoEdit world → Candidate key world →
      Σ ℕ (λ chosen → Candidate chosen world × Σ (Incoming chosen world) (λ incoming → incomingSource incoming ∉ M.Intent.keys intent))
    stoppedUnprotectedDependency world key valid quiet candidate with canonicalBoundary world key valid quiet candidate
    ... | chosen , chosenIn , incoming , outside = chosen , candidatesSound world chosen chosenIn , incoming ,
      boundaryOutsideCapture world chosen valid quiet (candidatesSound world chosen chosenIn) incoming outside

    candidatePending : ∀ world key → Candidate key world → Pending key world
    candidatePending world key (value , found , captured , owned , indexed , unneeded , unprotected) =
      value , found , captured , owned , indexed , inj₁ unneeded

    -- Valid execution has only the two derived waiting obligations. The
    -- weaker raw-store assessment cannot be returned by this interface.
    data ValidAssessment (world : O.World) : Set where
      validReady : M.Complete selection accepted intent world world → ValidAssessment world
      waitProtected : (key : ℕ) → Pending key world → M.Protected selection world key →
        ¬ M.Complete selection accepted intent world world → ValidAssessment world
      waitLater : (key : ℕ) → Candidate key world → (incoming : Incoming key world) →
        incomingSource incoming ∉ M.Intent.keys intent → ¬ M.Complete selection accepted intent world world → ValidAssessment world

    assessValid : ∀ world → O.Admissible world → Pass.NoEdit world → ValidAssessment world
    assessValid world valid quiet with assess world (O.Admissible.unique valid) quiet
    ... | ready complete = validReady complete
    ... | waiting key pending@(value , found , captured , owned , indexed , remaining) blocker incomplete
      with Classifier.Assessment.protected? selection world key
    ...   | yes pinned = waitProtected key pending pinned incomplete
    ...   | no unprotected with remaining
    ...     | inj₂ (needed , changed) = ⊥-elim (quiet key (inj₂ (value , found , captured , owned , indexed , needed , unprotected , changed)))
    ...     | inj₁ unneeded with stoppedUnprotectedDependency world key valid quiet
          (value , found , captured , owned , indexed , unneeded , unprotected)
    ...       | chosen , candidate , incoming , outside = waitLater chosen candidate incoming outside
          (pendingExcludesComplete chosen world (candidatePending world chosen candidate))

    assessPass : ∀ before → O.Admissible before → ValidAssessment (Pass.Result.after (Pass.run before))
    assessPass before valid = assessValid (Pass.Result.after (Pass.run before))
      (Pass.traceAdmissible (Pass.Result.trace (Pass.run before)) valid) (Pass.Result.noEdit (Pass.run before))
