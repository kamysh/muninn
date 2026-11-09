{-# OPTIONS --safe #-}
-- Finite active cleanup passes. Stopping is not the task completion outcome.
module Muninn.CleanupProgress where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.ExclusionClassifier as C
import Muninn.CleanupEffects as Effects
import Muninn.CleanupStorage as Storage
import Muninn.FiniteClosure as F
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; _≟_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; <-≤-trans; m≤n+m; m≤m+n;
  +-mono-≤; +-mono-<-≤; +-mono-≤-<; +-assoc; +-comm)
open import Data.Bool using (Bool; true; false)
open import Data.String using (String)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans; subst)
module DB = O.DB

weight : O.Record → ℕ
weight value = suc (E.bindingPayload value + (length (E.snapshotNodes value) + length (E.snapshotEdges value)))

mass : O.World → ℕ
mass [] = zero
mass ((key , value) ∷ world) = weight value + mass world

swapSum : ∀ a b c → a + (b + c) ≡ b + (a + c)
swapSum a b c = trans (sym (+-assoc a b c)) (trans (cong (_+ c) (+-comm a b)) (+-assoc b a c))

deleteDoesNotGrow : ∀ key world → mass (DB.delete key world) ≤ mass world
deleteDoesNotGrow key [] = z≤n
deleteDoesNotGrow key ((other , value) ∷ world) with key ≟ other
... | yes _ = ≤-trans (deleteDoesNotGrow key world) (m≤n+m (mass world) (weight value))
... | no _ = +-mono-≤ ≤-refl (deleteDoesNotGrow key world)

removedWeightCovered : ∀ key world value → DB.lookup key world ≡ just value →
  weight value + mass (DB.delete key world) ≤ mass world
removedWeightCovered key [] value ()
removedWeightCovered key ((other , stored) ∷ world) value found with key ≟ other
... | yes _ with just-injective found
...   | refl = +-mono-≤ ≤-refl (deleteDoesNotGrow key world)
removedWeightCovered key ((other , stored) ∷ world) value found | no _
  rewrite swapSum (weight value) (weight stored) (mass (DB.delete key world)) =
    +-mono-≤ ≤-refl (removedWeightCovered key world value found)

deletionDecreases : ∀ key world value → DB.lookup key world ≡ just value → mass (DB.delete key world) < mass world
deletionDecreases key world value found = ≤-trans
  (s≤s (m≤n+m (mass (DB.delete key world)) (E.bindingPayload value + (length (E.snapshotNodes value) + length (E.snapshotEdges value)))))
  (removedWeightCovered key world value found)

replacementDecreases : ∀ key world old new → DB.lookup key world ≡ just old → weight new < weight old →
  mass (DB.write key new world) < mass world
replacementDecreases key world old new found smaller = <-≤-trans
  (+-mono-<-≤ smaller ≤-refl) (removedWeightCovered key world old found)

filterBound : ∀ keep keys → length (E.filterKeys keep keys) ≤ length keys
filterBound keep [] = z≤n
filterBound keep (key ∷ keys) with keep key
... | true = s≤s (filterBound keep keys)
... | false = ≤-trans (filterBound keep keys) (Data.Nat.Properties.n≤1+n (length keys))

filterStrict : ∀ keep keys → E.filterKeys keep keys ≢ keys → length (E.filterKeys keep keys) < length keys
filterStrict keep [] different = ⊥-elim (different refl)
filterStrict keep (key ∷ keys) different with keep key
... | true = s≤s (filterStrict keep keys (λ equal → different (cong (key ∷_) equal)))
... | false = s≤s (filterBound keep keys)

peel : ∀ {a b} → suc a ≤ suc b → a ≤ b
peel (s≤s proof) = proof

noSuccessorBelowZero : ∀ {n} → ¬ (suc n ≤ zero)
noSuccessorBelowZero ()

module Model where
  module M = E.Model
  module Edits = Effects.Model
  module Store = Storage.Model

  projectionDecreasesWeight : ∀ selection world value →
    ((E.snapshotNodes (M.project selection world value) ≢ E.snapshotNodes value ⊎
      E.snapshotEdges (M.project selection world value) ≢ E.snapshotEdges value) ⊎
     E.bindingPayload (M.project selection world value) ≢ E.bindingPayload value) →
    weight (M.project selection world value) < weight value
  projectionDecreasesWeight selection world value changed with Store.shape selection world value
  ... | Store.plain equal with changed
  ...   | inj₁ (inj₁ different) = ⊥-elim (different (cong E.snapshotNodes equal))
  ...   | inj₁ (inj₂ different) = ⊥-elim (different (cong E.snapshotEdges equal))
  ...   | inj₂ different = ⊥-elim (different (cong E.bindingPayload equal))
  projectionDecreasesWeight selection world value changed | Store.hiddenDelta owner selected version path answer same =
    subst (λ projected → weight projected < weight (O.recordOf owner (O.deltaBinding selected (just version) path answer)))
      (sym same) ≤-refl
  projectionDecreasesWeight selection world value changed | Store.snapshot owner selected nodes edges payload
    with E.ownerEqual owner (E.targetOwner selection)
  ... | no _ with changed
  ...   | inj₁ (inj₁ different) = ⊥-elim (different refl)
  ...   | inj₁ (inj₂ different) = ⊥-elim (different refl)
  ...   | inj₂ different = ⊥-elim (different refl)
  projectionDecreasesWeight selection world value changed | Store.snapshot owner selected nodes edges payload | yes _ with changed
  ... | inj₁ (inj₁ different) = s≤s (+-mono-<-≤
      (filterStrict (M.symbolVisible selection world owner selected) nodes different)
      (filterBound (M.edgeVisible selection world owner selected) edges))
  ... | inj₁ (inj₂ different) = s≤s (+-mono-≤-<
      (filterBound (M.symbolVisible selection world owner selected) nodes)
      (filterStrict (M.edgeVisible selection world owner selected) edges different))

  ... | inj₂ different = ⊥-elim (different refl)

  module Pass (selection : E.Rule) (accepted : O.World) (intent : M.Intent selection accepted) where
    module Core = Edits.Core selection accepted intent

    Ready : ℕ → O.World → Set
    Ready key world = Core.Removal key world ⊎ Core.Projection key world

    ready? : ∀ key world → Dec (Ready key world)
    ready? key world = C.either (Core.removal? key world) (Core.projection? key world)

    next : ℕ → O.World → O.World
    next key world = proj₂ (DB.execute (Core.transaction key) world)

    editDecreases : ∀ key world → Ready key world → mass (next key world) < mass world
    editDecreases key world (inj₁ ready@(value , found , conditions)) =
      subst (λ after → mass after < mass world) (sym (cong proj₂ (Core.removalExecutes key world ready)))
        (deletionDecreases key world value found)
    editDecreases key world (inj₂ ready@(value , found , captured , owned , indexed , needed , unprotected , changed)) =
      subst (λ after → mass after < mass world) (sym (cong proj₂ (Core.projectionExecutes key world ready)))
        (replacementDecreases key world value (M.project selection world value) found
          (projectionDecreasesWeight selection world value changed))

    Available : O.World → Set
    Available world = Σ ℕ (λ key → key ∈ M.Intent.keys intent × Ready key world)

    available? : ∀ world → Dec (Available world)
    available? world = F.choose (λ key → Ready key world) (λ key → ready? key world) (M.Intent.keys intent)

    capturedReady : ∀ key world → Ready key world → key ∈ M.Intent.keys intent
    capturedReady key world (inj₁ (value , found , captured , conditions)) = captured
    capturedReady key world (inj₂ (value , found , captured , conditions)) = captured

    NoEdit : O.World → Set
    NoEdit world = ∀ key → ¬ Ready key world

    noAvailableMeansNoEdit : ∀ world → ¬ Available world → NoEdit world
    noAvailableMeansNoEdit world none key ready = none (key , capturedReady key world ready , ready)

    -- Each edge is one actual committed transaction, on its own current world.
    data Trace : ℕ → O.World → O.World → Set where
      stop : ∀ world → Trace zero world world
      edit : ∀ {count after} key before → Ready key before →
        Trace count (next key before) after → Trace (suc count) before after

    traceBound : ∀ {count before after} → Trace count before after → count + mass after ≤ mass before
    traceBound (stop world) = ≤-refl
    traceBound (edit key before ready later) = ≤-trans (s≤s (traceBound later)) (editDecreases key before ready)

    traceAdmissible : ∀ {count before after} → Trace count before after → O.Admissible before → O.Admissible after
    traceAdmissible (stop world) valid = valid
    traceAdmissible (edit key before ready later) valid = traceAdmissible later (Core.transactionAdmissible key before valid)

    traceUnrelated : ∀ {count before after} → Trace count before after → ∀ key value →
      DB.lookup key before ≡ just value → O.owner value ≢ E.targetOwner selection → DB.lookup key after ≡ just value
    traceUnrelated (stop world) key value found unrelated = found
    traceUnrelated (edit chosen before ready later) key value found unrelated = traceUnrelated later key value
      (M.Safety.unrelated (Core.transactionSafety chosen before) key value found unrelated) unrelated

    traceMetadata : ∀ {count before after} → Trace count before after → ∀ key value →
      DB.lookup key before ≡ just value → E.indexed value ≡ false → DB.lookup key after ≡ just value
    traceMetadata (stop world) key value found metadata = found
    traceMetadata (edit chosen before ready later) key value found metadata = traceMetadata later key value
      (M.Safety.metadata (Core.transactionSafety chosen before) key value found metadata) metadata

    traceOutsideCapture : ∀ {count before after} → Trace count before after → ∀ key value →
      DB.lookup key before ≡ just value → key ∉ M.Intent.keys intent → DB.lookup key after ≡ just value
    traceOutsideCapture (stop world) key value found outside = found
    traceOutsideCapture (edit chosen before ready later) key value found outside = traceOutsideCapture later key value
      (Core.transactionOutsideCapture chosen before key value found outside) outside

    traceNoNewKeys : ∀ {count before after} → Trace count before after → ∀ key →
      DB.lookup key before ≡ nothing → DB.lookup key after ≡ nothing
    traceNoNewKeys (stop world) key absent = absent
    traceNoNewKeys (edit chosen before ready later) key absent = traceNoNewKeys later key
      (Core.transactionNoNewKeys chosen before key absent)

    record Result (before : O.World) : Set where
      constructor result
      field after : O.World
            count : ℕ
            trace : Trace count before after
            noEdit : NoEdit after

    -- The capacity is at least the current mass. At zero, a proposed edit
    -- contradicts strict descent; it is never silently dropped as a timeout.
    runWithin : ∀ capacity world → mass world ≤ capacity → Result world
    runWithin zero world bound with available? world
    ... | no none = result world zero (stop world) (noAvailableMeansNoEdit world none)
    ... | yes (key , captured , ready) = ⊥-elim (noSuccessorBelowZero (≤-trans (editDecreases key world ready) bound))
    runWithin (suc capacity) world bound with available? world
    ... | no none = result world zero (stop world) (noAvailableMeansNoEdit world none)
    ... | yes (key , captured , ready) with runWithin capacity (next key world) (peel (≤-trans (editDecreases key world ready) bound))
    ...   | result after count trail noEdit = result after (suc count) (edit key world ready trail) noEdit

    run : ∀ world → Result world
    run world = runWithin (mass world) world ≤-refl

    passBound : ∀ world → Result.count (run world) + mass (Result.after (run world)) ≤ mass world
    passBound world = traceBound (Result.trace (run world))

    restartBound : ∀ observed → Result.count (run observed) ≤ mass observed
    restartBound observed = ≤-trans (m≤m+n (Result.count (run observed)) (mass (Result.after (run observed)))) (passBound observed)

    idle : ∀ capacity world bound → NoEdit world →
      (Result.after (runWithin capacity world bound) ≡ world) × (Result.count (runWithin capacity world bound) ≡ zero)
    idle zero world bound quiet with available? world
    ... | no none = refl , refl
    ... | yes (key , captured , ready) = ⊥-elim (quiet key ready)
    idle (suc capacity) world bound quiet with available? world
    ... | no none = refl , refl
    ... | yes (key , captured , ready) = ⊥-elim (quiet key ready)

    repeatedPassDoesNoWork : ∀ world →
      (Result.after (run (Result.after (run world))) ≡ Result.after (run world)) ×
      (Result.count (run (Result.after (run world))) ≡ zero)
    repeatedPassDoesNoWork world = idle (mass (Result.after (run world))) (Result.after (run world)) ≤-refl (Result.noEdit (run world))
