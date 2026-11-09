{-# OPTIONS --safe #-}
-- A current-snapshot decision and at most one committed record mutation.
module Muninn.CleanupEffects where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.ExclusionClassifier as C
import Muninn.CleanupStorage as S
import Muninn.FiniteClosure as F
open import Data.Nat using (ℕ; suc; _≟_)
open import Data.Bool using (Bool; true; false)
open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
module DB = O.DB

not? : ∀ {A : Set} → Dec A → Dec (¬ A)
not? (yes proof) = no (λ denied → denied proof)
not? (no denied) = yes denied

all? : ∀ {A : Set} (P : A → Set) → (∀ value → Dec (P value)) → (values : List A) → Dec (All P values)
all? P decide [] = yes []
all? P decide (value ∷ values) with decide value | all? P decide values
... | yes proof | yes rest = yes (proof ∷ rest)
... | no denied | _ = no (λ { (proof ∷ rest) → denied proof })
... | _ | no denied = no (λ { (proof ∷ rest) → denied rest })

unreferenced? : ∀ key world → Dec (All (O.NoIncomingTo key) world)
unreferenced? key = all? (O.NoIncomingTo key) (λ row →
  all? (λ ref → O.target ref ≢ key) (λ ref → not? (O.target ref ≟ key)) (O.references (O.body (proj₂ row))))

listEqual : (first second : List ℕ) → Dec (first ≡ second)
listEqual [] [] = yes refl
listEqual [] (_ ∷ _) = no (λ ())
listEqual (_ ∷ _) [] = no (λ ())
listEqual (a ∷ as) (b ∷ bs) with a ≟ b | listEqual as bs
... | yes refl | yes refl = yes refl
... | no different | _ = no (λ { refl → different refl })
... | _ | no different = no (λ { refl → different refl })

trueIsNotFalse : true ≢ false
trueIsNotFalse ()

data Reply : Set where unchanged removed projected : Reply

-- Evidence is indexed by the actual shared transaction, not by a separately
-- maintained step counter. Adding another put/remove invalidates this proof.
data MutationBound {A : Set} : ℕ → DB.Transaction A → Set where
  returnWithin : ∀ capacity result → MutationBound capacity (DB.commit result)
  abortWithin : ∀ capacity result → MutationBound capacity (DB.abort result)
  putWithin : ∀ {capacity next} key value → MutationBound capacity next →
    MutationBound (suc capacity) (DB.put key value next)
  removeWithin : ∀ {capacity next} key → MutationBound capacity next →
    MutationBound (suc capacity) (DB.remove key next)
  scanWithin : ∀ capacity next → (∀ world → MutationBound capacity (next world)) →
    MutationBound capacity (DB.scan next)

presentNotAbsent : ∀ {value : O.Record} → just value ≢ nothing
presentNotAbsent ()

module Model (excluded : List String → String → Bool) where
  module M = E.Model excluded
  module Classifier = C.Model excluded
  module Store = S.Model excluded

  eraseSafety : ∀ selection world key value → DB.lookup key world ≡ just value →
    O.owner value ≡ E.targetOwner selection → E.indexed value ≡ true →
    ¬ M.Needed selection world key → ¬ M.Protected selection world key →
    M.Safety selection world (DB.delete key world)
  eraseSafety selection world key value found owned indexed unneeded unprotected = record
    { unrelated = unrelated; metadata = metadata
    ; needed = λ other stored present live → stored ,
        (trans (DB.deletePreservesOther key other world (λ { refl → unneeded live })) present ,
          refl , (λ member seen → seen) , (λ member seen → seen))
    ; protected = λ other stored present pinned →
        trans (DB.deletePreservesOther key other world (λ { refl → unprotected pinned })) present }
    where
    unrelated : ∀ other stored → DB.lookup other world ≡ just stored → O.owner stored ≢ E.targetOwner selection →
      DB.lookup other (DB.delete key world) ≡ just stored
    unrelated other stored present distinct = trans (DB.deletePreservesOther key other world differentKeys) present
      where
      differentKeys : key ≢ other
      differentKeys refl = distinct (trans (sym (cong O.owner (just-injective (trans (sym found) present)))) owned)
    metadata : ∀ other stored → DB.lookup other world ≡ just stored → E.indexed stored ≡ false →
      DB.lookup other (DB.delete key world) ≡ just stored
    metadata other stored present control = trans (DB.deletePreservesOther key other world differentKeys) present
      where
      differentKeys : key ≢ other
      differentKeys refl = trueIsNotFalse (trans (sym indexed)
        (trans (cong E.indexed (just-injective (trans (sym found) present))) control))

  projectSafety : ∀ selection world key value → DB.lookup key world ≡ just value →
    O.owner value ≡ E.targetOwner selection → E.indexed value ≡ true →
    ¬ M.Protected selection world key → M.Safety selection world (DB.write key (M.project selection world value) world)
  projectSafety selection world key value found owned indexed unprotected = record
    { unrelated = unrelated; metadata = metadata; needed = needed
    ; protected = λ other stored present pinned →
        trans (DB.writePreservesOther key other (M.project selection world value) world
          (λ { refl → unprotected pinned })) present }
    where
    unrelated : ∀ other stored → DB.lookup other world ≡ just stored → O.owner stored ≢ E.targetOwner selection →
      DB.lookup other (DB.write key (M.project selection world value) world) ≡ just stored
    unrelated other stored present distinct = trans (DB.writePreservesOther key other (M.project selection world value) world differentKeys) present
      where
      differentKeys : key ≢ other
      differentKeys refl = distinct (trans (sym (cong O.owner (just-injective (trans (sym found) present)))) owned)
    metadata : ∀ other stored → DB.lookup other world ≡ just stored → E.indexed stored ≡ false →
      DB.lookup other (DB.write key (M.project selection world value) world) ≡ just stored
    metadata other stored present control = trans (DB.writePreservesOther key other (M.project selection world value) world differentKeys) present
      where
      differentKeys : key ≢ other
      differentKeys refl = trueIsNotFalse (trans (sym indexed)
        (trans (cong E.indexed (just-injective (trans (sym found) present))) control))
    needed : ∀ other stored → DB.lookup other world ≡ just stored → M.Needed selection world other →
      Σ O.Record (λ retained → (DB.lookup other (DB.write key (M.project selection world value) world) ≡ just retained) ×
        ((M.project selection world retained ≡ M.project selection world stored) ×
          ((∀ member → member ∈ E.snapshotNodes retained → member ∈ E.snapshotNodes stored) ×
           (∀ member → member ∈ E.snapshotEdges retained → member ∈ E.snapshotEdges stored))))
    needed other stored present live with key ≟ other
    ... | no different = stored , (trans (DB.writePreservesOther key other (M.project selection world value) world different) present ,
      refl , (λ member seen → seen) , (λ member seen → seen))
    ... | yes refl with just-injective (trans (sym found) present)
    ...   | refl = M.project selection world stored ,
      DB.writeVisible other (M.project selection world stored) world ,
      Store.projectIdempotent selection world stored ,
      Store.projectNodesSubset selection world stored , Store.projectEdgesSubset selection world stored

  module Core (selection : E.Rule) (accepted : O.World) (intent : M.Intent selection accepted) where
    Changed : O.World → O.Record → Set
    Changed world value =
      E.snapshotNodes (M.project selection world value) ≢ E.snapshotNodes value ⊎
      E.snapshotEdges (M.project selection world value) ≢ E.snapshotEdges value

    changed? : ∀ world value → Dec (Changed world value)
    changed? world value = C.either
      (not? (listEqual (E.snapshotNodes (M.project selection world value)) (E.snapshotNodes value)))
      (not? (listEqual (E.snapshotEdges (M.project selection world value)) (E.snapshotEdges value)))

    changedIsActual : ∀ world value → Changed world value → M.project selection world value ≢ value
    changedIsActual world value (inj₁ different) same = different (cong E.snapshotNodes same)
    changedIsActual world value (inj₂ different) same = different (cong E.snapshotEdges same)

    Removal : ℕ → O.World → Set
    Removal key world = C.At world key (λ value → key ∈ M.Intent.keys intent ×
      (O.owner value ≡ E.targetOwner selection × (E.indexed value ≡ true ×
        (¬ M.Needed selection world key × (¬ M.Protected selection world key × All (O.NoIncomingTo key) world)))))

    Projection : ℕ → O.World → Set
    Projection key world = C.At world key (λ value → key ∈ M.Intent.keys intent ×
      (O.owner value ≡ E.targetOwner selection × (E.indexed value ≡ true ×
        (M.Needed selection world key × (¬ M.Protected selection world key × Changed world value)))))

    removal? : ∀ key world → Dec (Removal key world)
    removal? key world = C.at? world key _ (λ value →
      C.both (F.member key (M.Intent.keys intent)) (C.both (E.ownerEqual (O.owner value) (E.targetOwner selection))
        (C.both (C.true? (E.indexed value)) (C.both (not? (Assessment.needed? key))
          (C.both (not? (Assessment.protected? key)) (unreferenced? key world))))))
      where module Assessment = Classifier.Assessment selection world

    projection? : ∀ key world → Dec (Projection key world)
    projection? key world = C.at? world key _ (λ value →
      C.both (F.member key (M.Intent.keys intent)) (C.both (E.ownerEqual (O.owner value) (E.targetOwner selection))
        (C.both (C.true? (E.indexed value)) (C.both (Assessment.needed? key)
          (C.both (not? (Assessment.protected? key)) (changed? world value))))))
      where module Assessment = Classifier.Assessment selection world

    data Plan (key : ℕ) (world : O.World) : Set where
      retain : ¬ (Removal key world ⊎ Projection key world) → Plan key world
      erase : Removal key world → Plan key world
      trim : Projection key world → Plan key world

    decide : ∀ key world → Plan key world
    decide key world with removal? key world
    ... | yes ready = erase ready
    ... | no cannotRemove with projection? key world
    ...   | yes ready = trim ready
    ...   | no cannotProject = retain (λ { (inj₁ ready) → cannotRemove ready; (inj₂ ready) → cannotProject ready })

    compile : ∀ key world → Plan key world → DB.Transaction Reply
    compile key world (retain denied) = DB.commit unchanged
    compile key world (erase ready) = DB.remove key (DB.commit removed)
    compile key world (trim (value , found , ready)) = DB.put key (M.project selection world value) (DB.commit projected)

    transaction : ℕ → DB.Transaction Reply
    transaction key = DB.scan (λ world → compile key world (decide key world))

    compileBound : ∀ key world (plan : Plan key world) → MutationBound 1 (compile key world plan)
    compileBound key world (retain denied) = returnWithin 1 unchanged
    compileBound key world (erase ready) = removeWithin key (returnWithin 0 removed)
    compileBound key world (trim (value , found , ready)) =
      putWithin key (M.project selection world value) (returnWithin 0 projected)

    transactionBound : ∀ key → MutationBound 1 (transaction key)
    transactionBound key = scanWithin 1 (λ world → compile key world (decide key world))
      (λ world → compileBound key world (decide key world))

    planSafety : ∀ key world (plan : Plan key world) → M.Safety selection world (proj₂ (DB.execute (compile key world plan) world))
    planSafety key world (retain denied) = M.safetyReflexive selection world
    planSafety key world (erase (value , found , captured , owned , indexed , unneeded , unprotected , unreferenced)) =
      eraseSafety selection world key value found owned indexed unneeded unprotected
    planSafety key world (trim (value , found , captured , owned , indexed , needed , unprotected , changed)) =
      projectSafety selection world key value found owned indexed unprotected

    planAdmissible : ∀ key world (plan : Plan key world) → O.Admissible world →
      O.Admissible (proj₂ (DB.execute (compile key world plan) world))
    planAdmissible key world (retain denied) valid = valid
    planAdmissible key world (erase (value , found , captured , owned , indexed , unneeded , unprotected , unreferenced)) valid =
      O.deleteUnreferencedPreservesAdmissibility key world valid unreferenced
    planAdmissible key world (trim (value , found , captured , owned , indexed , needed , unprotected , changed)) valid =
      Store.projectAdmissible selection world key value valid found

    planOutsideCapture : ∀ key world (plan : Plan key world) other value →
      DB.lookup other world ≡ just value → other ∉ M.Intent.keys intent →
      DB.lookup other (proj₂ (DB.execute (compile key world plan) world)) ≡ just value
    planOutsideCapture key world (retain denied) other value found outside = found
    planOutsideCapture key world (erase (value , found , captured , ready)) other stored present outside =
      trans (DB.deletePreservesOther key other world (λ { refl → outside captured })) present
    planOutsideCapture key world (trim (value , found , captured , ready)) other stored present outside =
      trans (DB.writePreservesOther key other (M.project selection world value) world (λ { refl → outside captured })) present

    planNoNewKeys : ∀ key world (plan : Plan key world) other → DB.lookup other world ≡ nothing →
      DB.lookup other (proj₂ (DB.execute (compile key world plan) world)) ≡ nothing
    planNoNewKeys key world (retain denied) other absent = absent
    planNoNewKeys key world (erase ready) other absent = O.deleteKeepsAbsent key other world absent
    planNoNewKeys key world (trim (value , found , ready)) other absent =
      trans (DB.writePreservesOther key other (M.project selection world value) world different) absent
      where
      different : key ≢ other
      different refl = presentNotAbsent (trans (sym found) absent)

    transactionSafety : ∀ key world → M.Safety selection world (proj₂ (DB.execute (transaction key) world))
    transactionSafety key world = planSafety key world (decide key world)

    transactionAdmissible : ∀ key world → O.Admissible world → O.Admissible (proj₂ (DB.execute (transaction key) world))
    transactionAdmissible key world = planAdmissible key world (decide key world)

    transactionOutsideCapture : ∀ key world other value → DB.lookup other world ≡ just value → other ∉ M.Intent.keys intent →
      DB.lookup other (proj₂ (DB.execute (transaction key) world)) ≡ just value
    transactionOutsideCapture key world = planOutsideCapture key world (decide key world)

    transactionNoNewKeys : ∀ key world other → DB.lookup other world ≡ nothing →
      DB.lookup other (proj₂ (DB.execute (transaction key) world)) ≡ nothing
    transactionNoNewKeys key world = planNoNewKeys key world (decide key world)

    -- The shared recovery semantics includes a stop before commit and a lost
    -- acknowledgement after it. No tentative statement prefix is published.
    oneStep : ℕ → O.Execution.Script Reply
    oneStep key = O.Execution.atomic (transaction key) O.Execution.done

    interruptionSafety : ∀ key before after → O.Execution.Interrupted (oneStep key) before after → M.Safety selection before after
    interruptionSafety key before .before (_ , O.Execution.stop) = M.safetyReflexive selection before
    interruptionSafety key before after (_ , O.Execution.committed O.Execution.stop) = transactionSafety key before

    interruptionAdmissible : ∀ key before after → O.Admissible before →
      O.Execution.Interrupted (oneStep key) before after → O.Admissible after
    interruptionAdmissible key before .before valid (_ , O.Execution.stop) = valid
    interruptionAdmissible key before after valid (_ , O.Execution.committed O.Execution.stop) = transactionAdmissible key before valid

    -- Work-ready certificates cannot be swallowed by a vacuous retain plan.
    removalExecutes : ∀ key world → Removal key world →
      DB.execute (transaction key) world ≡ (removed , DB.delete key world)
    removalExecutes key world ready@(old , original , captured′ , owned′ , indexed′ , unneeded , unprotected , unreferenced) with decide key world
    ... | erase other = refl
    ... | retain denied = ⊥-elim (denied (inj₁ ready))
    ... | trim (value , found , captured , owned , indexed , needed , rest) =
      ⊥-elim (unneeded needed)

    projectionExecutes : ∀ key world (ready : Projection key world) →
      DB.execute (transaction key) world ≡ (projected , DB.write key (M.project selection world (proj₁ ready)) world)
    projectionExecutes key world ready with decide key world
    ... | trim (value , found , conditions) with just-injective (trans (sym found) (proj₁ (proj₂ ready)))
    ...   | refl = refl
    projectionExecutes key world ready | retain denied = ⊥-elim (denied (inj₂ ready))
    projectionExecutes key world (value , found , captured , owned , indexed , needed , rest)
      | erase (other , present , captured′ , owned′ , indexed′ , unneeded , rest′) = ⊥-elim (unneeded needed)
