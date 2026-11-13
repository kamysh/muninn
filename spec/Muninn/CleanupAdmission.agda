{-# OPTIONS --safe #-}
module Muninn.CleanupAdmission where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.ExclusionClassifier as C
import Muninn.FiniteClosure as F
import Muninn.CleanupEffects as Effects
import Muninn.CleanupStorage as Storage
import Muninn.CleanupAdmissionStorage as Insert
import Muninn.CleanupObservations as Observations
import Muninn.CleanupProtection as Protection
import Muninn.ReceiptLedger as Ledger
import Muninn.PendingRemoval as Removal
open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (Bool; true; false)
open import Data.String using (String)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.All as All
open All using (All; []; _∷_)
open import Data.Maybe using (just; nothing)
import Data.Maybe.Properties
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
module DB = O.DB

allDec : ∀ {A : Set} (P : A → Set) → (∀ value → Dec (P value)) → ∀ values → Dec (All P values)
allDec P decide [] = yes []
allDec P decide (value ∷ values) with decide value | allDec P decide values
... | yes present | yes rest = yes (present ∷ rest)
... | no absent | _ = no (λ { (present ∷ rest) → absent present })
... | _ | no absent = no (λ { (present ∷ rest) → absent rest })

module Model (excluded : List String → String → Bool) where
  module M = E.Model excluded
  module Classify = C.Model excluded
  module Store = Storage.Model excluded
  module Frame = Insert.Model excluded
  module Pins = Protection.Model excluded

  module Family (selection : E.Rule) where
    claimFor : O.Record → List ℕ
    claimFor (O.recordOf owner (O.cleanupWork requestId ids payload)) with E.ownerEqual owner (E.targetOwner selection)
    ... | yes same = ids
    ... | no different = []
    claimFor _ = []

    claims : O.World → List ℕ
    claims [] = []
    claims ((slot , value) ∷ rows) = claimFor value ++ claims rows

    claimRow : ∀ world slot value key → (slot , value) ∈ world → key ∈ claimFor value → key ∈ claims world
    claimRow ((slot , value) ∷ rows) .slot .value key (here refl) captured = ∈-++⁺ˡ captured
    claimRow ((other , stored) ∷ rows) slot value key (there present) captured = ∈-++⁺ʳ (claimFor stored) (claimRow rows slot value key present captured)

    targetClaim : ∀ requestId ids payload → claimFor (O.recordOf (E.targetOwner selection) (O.cleanupWork requestId ids payload)) ≡ ids
    targetClaim requestId ids payload with E.ownerEqual (E.targetOwner selection) (E.targetOwner selection)
    ... | yes same = refl
    ... | no different = ⊥-elim (different refl)

    savedClaim : ∀ world slot requestId ids payload key → DB.lookup slot world ≡ just (O.recordOf (E.targetOwner selection) (O.cleanupWork requestId ids payload)) → key ∈ ids → key ∈ claims world
    savedClaim world slot requestId ids payload key found captured = claimRow world slot _ key (Observations.lookupMember world slot _ found)
      (subst (λ ids → key ∈ ids) (sym (targetClaim requestId ids payload)) captured)

    Canonical : O.World → O.Record → Set
    Canonical world value = M.project selection world value ≡ value

    canonical? : ∀ world value → Dec (Canonical world value)
    canonical? world value with Store.shape selection world value
    ... | Store.plain exact = yes exact
    ... | Store.snapshot owner selected nodes edges payload with E.ownerEqual owner (E.targetOwner selection)
    ...   | no different = yes refl
    ...   | yes same with Effects.listEqual (E.filterKeys (M.symbolVisible selection world owner selected) nodes) nodes
      | Effects.listEqual (E.filterKeys (M.edgeVisible selection world owner selected) edges) edges
    ...     | yes sameNodes | yes sameEdges = yes (cong₂ (λ ns es → O.recordOf owner (O.structuralSnapshot selected ns es payload)) sameNodes sameEdges)
    ...     | no different | _ = no (λ exact → different (cong E.snapshotNodes exact))
    ...     | _ | no different = no (λ exact → different (cong E.snapshotEdges exact))

    Pending : O.World → ℕ → Set
    Pending world key = key ∈ claims world × C.At world key (λ value → O.owner value ≡ E.targetOwner selection ×
      (E.indexed value ≡ true × (¬ M.Needed selection world key ⊎ ¬ Canonical world value)))

    pending? : ∀ world key → Dec (Pending world key)
    pending? world key = C.both (F.member key (claims world)) (C.at? world key _ (λ value →
      C.both (E.ownerEqual (O.owner value) (E.targetOwner selection)) (C.both (C.true? (E.indexed value))
        (C.either (Effects.not? (Classify.Assessment.needed? selection world key)) (Effects.not? (canonical? world value))))))

    sourceOf : ∀ {world key} → M.Protected selection world key → ℕ
    sourceOf (M.held source value ref found included resolved) = source
    sourceOf (M.required previous dependency) = sourceOf previous

    originReader : ∀ {world key} (pin : M.Protected selection world key) → M.readerOrigin pin ≡ M.readerAt world (sourceOf pin)
    originReader {world = world} (M.held source value ref found included resolved) = sym (M.readerAtMatches world source value found)
    originReader (M.required previous dependency) = originReader previous

    module Footprint (world : O.World) (source : ℕ) where
      module Facts = Classify.Assessment selection world
      flag = M.readerAt world source
      Seed : ℕ → Set
      Seed key = Facts.HeldAt key source
      seed? : ∀ key → Dec (Seed key)
      seed? key = Facts.heldAt? key source
      seedIn : ∀ {key} → Seed key → key ∈ C.keys world
      seedIn (value , found , ref , included , refl , resolved) = C.foundInKeys world (O.target ref) (O.Resolves.value resolved) (O.Resolves.found resolved)
      module Closure = F.Closure Seed (M.Dependency (M.temporaryFor flag) selection world) seed? (Facts.dependency? (M.temporaryFor flag))
        (C.keys world) seedIn (Facts.dependencyTargetIn (M.temporaryFor flag))
      open Closure public using (Reach; decide)

      mutual
        protected : ∀ {key} → Reach key → M.Protected selection world key
        protected (Closure.root (value , found , ref , included , refl , resolved)) = M.held source value ref found included resolved
        protected (Closure.step previous dependency) = M.required (protected previous)
          (subst (λ mode → M.Dependency mode selection world _ _) (cong M.temporaryFor (sym (protectedReader previous))) dependency)

        protectedReader : ∀ {key} (path : Reach key) → M.readerOrigin (protected path) ≡ flag
        protectedReader (Closure.root (value , found , ref , included , refl , resolved)) = sym (M.readerAtMatches world source value found)
        protectedReader (Closure.step previous dependency) = protectedReader previous

      fromProtection : ∀ {key} (pin : M.Protected selection world key) → sourceOf pin ≡ source → Reach key
      fromProtection (M.held actual value ref found included resolved) refl = Closure.root (value , found , ref , included , refl , resolved)
      fromProtection (M.required previous dependency) original = Closure.step (fromProtection previous original)
        (subst (λ mode → M.Dependency mode selection world _ _)
          (cong M.temporaryFor (trans (originReader previous) (cong (M.readerAt world) original))) dependency)

    CleanRef : O.World → O.Reference → Set
    CleanRef world ref = C.At world (O.target ref) (λ value → O.kind (O.body value) ≡ O.expected ref ×
      (O.MayReference (E.targetOwner selection) (O.owner value) × (Canonical world value × O.PublicReference ref)))

    cleanRef? : ∀ world ref → Dec (CleanRef world ref)
    cleanRef? world ref = C.at? world (O.target ref) _ (λ value → C.both (C.kindEqual (O.kind (O.body value)) (O.expected ref))
      (C.both (C.mayReference? (E.targetOwner selection) (O.owner value)) (C.both (canonical? world value)
        (O.publicReference? ref))))

    reader : List O.Reference → String → O.Record
    reader refs payload = O.recordOf (E.targetOwner selection) (O.activeReader refs payload)
    proposed : O.World → ℕ → List O.Reference → String → O.World
    proposed world slot refs payload = DB.write slot (reader refs payload) world

    Resolved : O.World → List O.Reference → Set
    Resolved world refs = All (O.Resolves world (E.targetOwner selection)) refs
    resolved? : ∀ world refs → Dec (Resolved world refs)
    resolved? world refs = allDec (O.Resolves world (E.targetOwner selection)) (C.resolves? world (E.targetOwner selection)) refs

    Clean : O.World → List O.Reference → Set
    Clean world refs = All (CleanRef world) refs
    clean? : ∀ world refs → Dec (Clean world refs)
    clean? world refs = allDec (CleanRef world) (cleanRef? world) refs

    Allowed : O.World → ℕ → List O.Reference → String → Set
    Allowed world slot refs payload = ∀ key → Pending world key → ¬ Footprint.Reach (proposed world slot refs payload) slot key

    allowed? : ∀ world slot refs payload → Dec (Allowed world slot refs payload)
    allowed? world slot refs payload with F.choose (λ key → Pending world key × Footprint.Reach (proposed world slot refs payload) slot key)
      (λ key → C.both (pending? world key) (Footprint.decide (proposed world slot refs payload) slot key)) (claims world)
    ... | yes (key , captured , pending , reached) = no (λ allowed → allowed key pending reached)
    ... | no none = yes (λ key pending reached → none (key , proj₁ pending , pending , reached))

    -- Replanning returns the caller's existing continuation value. It writes
    -- nothing and does not manufacture a terminal failure result.
    admitSnapshot : ∀ {A : Set} slot refs payload → (ℕ → A) → (O.World → A) → O.World → DB.Transaction A
    admitSnapshot slot refs payload ready replan world with F.member slot (Insert.reserved world)
    ... | yes reserved = DB.commit (replan world)
    ... | no fresh with resolved? world refs
    ...   | no unresolved = DB.commit (replan world)
    ...   | yes resolved with clean? (proposed world slot refs payload) refs
    ...     | no stale = DB.commit (replan world)
    ...     | yes clean with allowed? world slot refs payload
    ...       | no waiting = DB.commit (replan world)
    ...       | yes allowed = DB.put slot (reader refs payload) (DB.commit (ready slot))

    admit : ∀ {A : Set} slot refs payload → (ℕ → A) → (O.World → A) → DB.Transaction A
    admit slot refs payload ready replan = DB.scan λ world → choose (Removal.pending (E.targetOwner selection) world) world
      where
      choose : Bool → O.World → DB.Transaction _
      choose true world = DB.commit (replan world)
      choose false world = admitSnapshot slot refs payload ready replan world

    removalStopsNewReaders : ∀ {A : Set} slot refs payload (ready : ℕ → A) replan world →
      Removal.pending (E.targetOwner selection) world ≡ true →
      DB.execute (admit slot refs payload ready replan) world ≡ (replan world , world)
    removalStopsNewReaders slot refs payload ready replan world pending rewrite pending = refl

    effects : ∀ {A : Set} slot refs payload (ready : ℕ → A) replan world →
      (proj₂ (DB.execute (admit slot refs payload ready replan) world) ≡ world) ⊎
      (Insert.Fresh world slot × (Resolved world refs × (Clean (proposed world slot refs payload) refs ×
        (Allowed world slot refs payload × (proj₂ (DB.execute (admit slot refs payload ready replan) world) ≡ proposed world slot refs payload)))))
    effects slot refs payload ready replan world with Removal.pending (E.targetOwner selection) world
    ... | true = inj₁ refl
    ... | false with F.member slot (Insert.reserved world)
    ... | yes reserved = inj₁ refl
    ... | no fresh with resolved? world refs
    ...   | no unresolved = inj₁ refl
    ...   | yes resolved with clean? (proposed world slot refs payload) refs
    ...     | no stale = inj₁ refl
    ...     | yes clean with allowed? world slot refs payload
    ...       | no waiting = inj₁ refl
    ...       | yes allowed = inj₂ (fresh , resolved , clean , allowed , refl)

    insertedReceipts : ∀ world slot refs payload → Insert.Fresh world slot → Ledger.ReceiptFrame world (proposed world slot refs payload)
    insertedReceipts world slot refs payload fresh other owner receiptData =
      Insert.oldLookup world slot (reader refs payload) fresh other (O.recordOf owner (O.receipt receiptData)) , backward
      where
      disjoint : reader refs payload Relation.Binary.PropositionalEquality.≢ O.recordOf owner (O.receipt receiptData)
      disjoint ()
      backward : DB.lookup other (proposed world slot refs payload) ≡ just (O.recordOf owner (O.receipt receiptData)) →
        DB.lookup other world ≡ just (O.recordOf owner (O.receipt receiptData))
      backward found with slot ≟ other
      ... | no different = trans (sym (DB.writePreservesOther slot other (reader refs payload) world different)) found
      ... | yes same = ⊥-elim (disjoint (Data.Maybe.Properties.just-injective (trans (sym (DB.writeVisible slot (reader refs payload) world))
        (trans (cong (λ key → DB.lookup key (proposed world slot refs payload)) same) found))))

    receiptFrame : ∀ {A : Set} slot refs payload (ready : ℕ → A) replan world →
      Ledger.ReceiptFrame world (proj₂ (DB.execute (admit slot refs payload ready replan) world))
    receiptFrame slot refs payload ready replan world with effects slot refs payload ready replan world
    ... | inj₁ same = subst (Ledger.ReceiptFrame world) (sym same) (λ other owner receiptData → (λ found → found) , (λ found → found))
    ... | inj₂ (fresh , resolved , clean , allowed , same) = subst (Ledger.ReceiptFrame world) (sym same) (insertedReceipts world slot refs payload fresh)

    admissionSafety : ∀ {A : Set} slot refs payload (ready : ℕ → A) replan world →
      M.Safety selection world (proj₂ (DB.execute (admit slot refs payload ready replan) world))
    admissionSafety slot refs payload ready replan world with effects slot refs payload ready replan world
    ... | inj₁ same = subst (M.Safety selection world) (sym same) (M.safetyReflexive selection world)
    ... | inj₂ (fresh , resolved , clean , allowed , same) = subst (M.Safety selection world) (sym same)
      (Frame.insertionSafety selection world slot (reader refs payload) fresh)

    admissionAdmissible : ∀ {A : Set} slot refs payload (ready : ℕ → A) replan world → O.Admissible world →
      O.Admissible (proj₂ (DB.execute (admit slot refs payload ready replan) world))
    admissionAdmissible slot refs payload ready replan world valid with effects slot refs payload ready replan world
    ... | inj₁ same = subst O.Admissible (sym same) valid
    ... | inj₂ (fresh , resolved , clean , allowed , same) = subst O.Admissible (sym same)
      (Insert.insertAdmissible world slot (reader refs payload) valid fresh O.local resolved
        (All.map (λ {ref} (value , found , kind , owner , canonical , privateRefs) → privateRefs) clean))

    admitted : ∀ {A : Set} slot refs payload (ready : ℕ → A) replan world → Insert.Fresh world slot →
      DB.lookup slot (proj₂ (DB.execute (admit slot refs payload ready replan) world)) ≡ just (reader refs payload) →
      Clean (proj₂ (DB.execute (admit slot refs payload ready replan) world)) refs ×
      (∀ key → Pending world key → ¬ Footprint.Reach (proj₂ (DB.execute (admit slot refs payload ready replan) world)) slot key)
    admitted slot refs payload ready replan world fresh found with effects slot refs payload ready replan world
    ... | inj₁ same = ⊥-elim (Effects.presentNotAbsent (trans (sym found) (trans (cong (DB.lookup slot) same) (Insert.freshAbsent world slot fresh))))
    ... | inj₂ (fresh′ , resolved , clean , allowed , same) = subst (λ world → Clean world refs) (sym same) clean ,
      (λ key pending reached → allowed key pending (subst (λ world → Footprint.Reach world slot key) same reached))

    cannotExtend : ∀ {A : Set} slot refs payload (ready : ℕ → A) replan world → Insert.Fresh world slot →
      DB.lookup slot (proj₂ (DB.execute (admit slot refs payload ready replan) world)) ≡ just (reader refs payload) →
      ∀ key → Pending world key → (held : M.Protected selection (proj₂ (DB.execute (admit slot refs payload ready replan) world)) key) → sourceOf held ≡ slot → Data.Empty.⊥
    cannotExtend slot refs payload ready replan world fresh found key pending pin original =
      proj₂ (admitted slot refs payload ready replan world fresh found) key pending
        (Footprint.fromProtection (proj₂ (DB.execute (admit slot refs payload ready replan) world)) slot pin original)

    savedWorkset : ∀ {A : Set} slot refs payload (ready : ℕ → A) replan world task requestId ids note →
      DB.lookup task world ≡ just (O.recordOf (E.targetOwner selection) (O.cleanupWork requestId ids note)) →
      DB.lookup task (proj₂ (DB.execute (admit slot refs payload ready replan) world)) ≡ just (O.recordOf (E.targetOwner selection) (O.cleanupWork requestId ids note))
    savedWorkset slot refs payload ready replan world task requestId ids note found =
      M.Safety.metadata (admissionSafety slot refs payload ready replan world) task _ found refl

    existingUse : ∀ {A : Set} slot refs payload (ready : ℕ → A) replan world key → M.Protected selection world key →
      M.Protected selection (proj₂ (DB.execute (admit slot refs payload ready replan) world)) key
    existingUse slot refs payload ready replan world key = Pins.protectedSurvives selection world _ key (admissionSafety slot refs payload ready replan world)

    trackedAbsent : ∀ {A : Set} slot refs payload (ready : ℕ → A) replan world key → key ∈ Insert.reserved world → DB.lookup key world ≡ nothing →
      DB.lookup key (proj₂ (DB.execute (admit slot refs payload ready replan) world)) ≡ nothing
    trackedAbsent slot refs payload ready replan world key reserved absent with effects slot refs payload ready replan world
    ... | inj₁ same = trans (cong (DB.lookup key) same) absent
    ... | inj₂ (fresh , resolved , clean , allowed , same) = trans (cong (DB.lookup key) same)
      (trans (DB.writePreservesOther slot key (reader refs payload) world (λ { refl → fresh reserved })) absent)

    replansWhenHeld : ∀ {A : Set} slot refs payload (ready : ℕ → A) replan world → ¬ Allowed world slot refs payload →
      DB.execute (admit slot refs payload ready replan) world ≡ (replan world , world)
    replansWhenHeld slot refs payload ready replan world blocked with Removal.pending (E.targetOwner selection) world
    ... | true = refl
    ... | false with F.member slot (Insert.reserved world)
    ... | yes reserved = refl
    ... | no fresh with resolved? world refs
    ...   | no unresolved = refl
    ...   | yes resolved with clean? (proposed world slot refs payload) refs
    ...     | no stale = refl
    ...     | yes clean with allowed? world slot refs payload
    ...       | no waiting = refl
    ...       | yes allowed = ⊥-elim (blocked allowed)

    accepts : ∀ {A : Set} slot refs payload (ready : ℕ → A) replan world → Removal.pending (E.targetOwner selection) world ≡ false → Insert.Fresh world slot → Resolved world refs →
      Clean (proposed world slot refs payload) refs → Allowed world slot refs payload →
      DB.execute (admit slot refs payload ready replan) world ≡ (ready slot , proposed world slot refs payload)
    accepts slot refs payload ready replan world notRemoving fresh resolved clean allowed rewrite notRemoving with F.member slot (Insert.reserved world)
    ... | yes reserved = ⊥-elim (fresh reserved)
    ... | no fresh′ with resolved? world refs
    ...   | no unresolved = ⊥-elim (unresolved resolved)
    ...   | yes resolved′ with clean? (proposed world slot refs payload) refs
    ...     | no stale = ⊥-elim (stale clean)
    ...     | yes clean′ with allowed? world slot refs payload
    ...       | no waiting = ⊥-elim (waiting allowed)
    ...       | yes allowed′ = refl
