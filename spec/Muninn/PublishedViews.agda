{-# OPTIONS --safe #-}
-- Current publication is distinct from older retained snapshot versions.
module Muninn.PublishedViews where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.CleanupStorage as Storage
import Muninn.CleanupNeedScope as Scope
import Muninn.CleanupAlignment as Alignment
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false)
open import Data.String using (String)
open import Data.List using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
module DB = O.DB

SnapshotAt : O.World → O.Owner → ℕ → ℕ → Set
SnapshotAt world owner selected snapshot = Σ (List ℕ) (λ nodes →
  Σ (List ℕ) (λ edges → Σ String (λ payload →
    DB.lookup snapshot world ≡ just (O.recordOf owner (O.structuralSnapshot selected nodes edges payload)))))

CurrentAt : O.World → O.Owner → ℕ → ℕ → Set
CurrentAt world owner selected snapshot = Σ ℕ (λ pointer →
  DB.lookup pointer world ≡ just (O.recordOf owner (O.publishedView selected snapshot)))

-- The assembled publication/catalog operation must preserve this domain invariant
-- as well as the shared store's ownership/reference admissibility.
record Valid (world : O.World) : Set where
  field
    onePerCheckout : ∀ first second owner selected before after →
      DB.lookup first world ≡ just (O.recordOf owner (O.publishedView selected before)) →
      DB.lookup second world ≡ just (O.recordOf owner (O.publishedView selected after)) →
      first ≡ second
    sameCheckout : ∀ pointer owner selected snapshot →
      DB.lookup pointer world ≡ just (O.recordOf owner (O.publishedView selected snapshot)) →
      SnapshotAt world owner selected snapshot

snapshotInjective : ∀ owner selected before after →
  O.recordOf owner (O.publishedView selected before) ≡ O.recordOf owner (O.publishedView selected after) →
  before ≡ after
snapshotInjective owner selected before .before refl = refl

currentUnique : ∀ world owner selected before after → Valid world →
  CurrentAt world owner selected before → CurrentAt world owner selected after → before ≡ after
currentUnique world owner selected before after valid (first , found) (second , present) =
  snapshotInjective owner selected before after (just-injective (trans (sym found) (trans (cong (λ key → DB.lookup key world) (Valid.onePerCheckout valid first second owner selected before after found present)) present)))

currentMatchesCheckout : ∀ world owner selected snapshot → Valid world →
  CurrentAt world owner selected snapshot → SnapshotAt world owner selected snapshot
currentMatchesCheckout world owner selected snapshot valid (pointer , found) =
  Valid.sameCheckout valid pointer owner selected snapshot found

snapshotFromFacts : ∀ world owner selected snapshot value →
  DB.lookup snapshot world ≡ just value → O.kind (O.body value) ≡ O.structuralSnapshotK →
  O.owner value ≡ owner → E.snapshotCheckout value ≡ just selected →
  SnapshotAt world owner selected snapshot
snapshotFromFacts world owner selected snapshot (O.recordOf actualOwner (O.structuralSnapshot actualSelected nodes edges payload)) found kind owned checkout
  with owned | just-injective checkout
... | refl | refl = nodes , edges , payload , found

module Model where
  module M = E.Model
  module Targets = Scope.Model

  storedSnapshotNotRoot : ∀ selection world selected nodes edges payload →
    M.rooted selection world (O.recordOf (E.targetOwner selection) (O.structuralSnapshot selected nodes edges payload)) ≡ false
  storedSnapshotNotRoot selection world selected nodes edges payload with E.ownerEqual (E.targetOwner selection) (E.targetOwner selection)
  ... | yes same = refl
  ... | no different = ⊥-elim (different refl)

  currentRooted : ∀ selection world selected snapshot →
    M.familyRegistered selection world ≡ true → M.checkoutLive selection world selected ≡ true →
    M.rooted selection world (O.recordOf (E.targetOwner selection) (O.publishedView selected snapshot)) ≡ true
  currentRooted selection world selected snapshot registered live with E.ownerEqual (E.targetOwner selection) (E.targetOwner selection)
  ... | yes same rewrite registered | live = refl
  ... | no different = ⊥-elim (different refl)

  currentSnapshotNeeded : ∀ selection world pointer selected snapshot →
    O.Admissible world →
    DB.lookup pointer world ≡ just (O.recordOf (E.targetOwner selection) (O.publishedView selected snapshot)) →
    M.familyRegistered selection world ≡ true → M.checkoutLive selection world selected ≡ true →
    M.Needed selection world snapshot
  currentSnapshotNeeded selection world pointer selected snapshot valid found registered live =
    M.required (M.root pointer (O.recordOf (E.targetOwner selection) (O.publishedView selected snapshot)) found (currentRooted selection world selected snapshot registered live)) (M.reference pointer (O.recordOf (E.targetOwner selection) (O.publishedView selected snapshot)) (O.reference snapshot O.structuralSnapshotK) found (there (here refl)) (All.lookup (Storage.lookupAll world pointer (O.recordOf (E.targetOwner selection) (O.publishedView selected snapshot)) (O.Admissible.sound valid) found) (there (here refl))))

  onlyPublishedReferencesSnapshots : ∀ selection world value ref →
    ref ∈ M.referencesFor M.permanent selection world value →
    O.expected ref ≡ O.structuralSnapshotK → O.kind (O.body value) ≡ O.publishedViewK
  onlyPublishedReferencesSnapshots selection world value ref included =
    All.lookup (Targets.permanentTargets selection world value) included


  module Cleanup (selection : E.Rule) (accepted : O.World) (intent : M.Intent selection accepted) where
    module Aligned = Alignment.Model.Contract selection accepted intent
    module Pass = Aligned.Pass

    validAfterCleanup : ∀ {count before after} → Pass.Trace count before after →
      O.Admissible before → Valid before → Valid after
    validAfterCleanup {before = before} {after = after} trail storeValid viewsValid = record
      { onePerCheckout = λ first second owner selected old current found present →
          Valid.onePerCheckout viewsValid first second owner selected old current
            (Aligned.backwardPlain trail storeValid first _ found ((λ ()) , (λ ())))
            (Aligned.backwardPlain trail storeValid second _ present ((λ ()) , (λ ())))
      ; sameCheckout = keepsCheckout }
      where
      keepsCheckout : ∀ pointer owner selected snapshot →
        DB.lookup pointer after ≡ just (O.recordOf owner (O.publishedView selected snapshot)) →
        SnapshotAt after owner selected snapshot
      keepsCheckout pointer owner selected snapshot found
        with Valid.sameCheckout viewsValid pointer owner selected snapshot
          (Aligned.backwardPlain trail storeValid pointer _ found ((λ ()) , (λ ())))
      ... | nodes , edges , payload , prior =
        let
          stored = O.recordOf owner (O.publishedView selected snapshot)
          afterValid = Pass.traceAdmissible trail storeValid
          linked = All.lookup (Storage.lookupAll after pointer stored (O.Admissible.sound afterValid) found) (there (here refl))
          actual = O.Resolves.value linked
          origin = Aligned.traceAncestor trail snapshot actual (O.Resolves.found linked)
          originalSame = just-injective (trans (sym (Aligned.Ancestor.found origin)) prior)
        in snapshotFromFacts after owner selected snapshot actual (O.Resolves.found linked) (O.Resolves.rightKind linked)
          (trans (Aligned.Ancestor.owner origin) (cong O.owner originalSame))
          (trans (Aligned.Ancestor.checkout origin) (cong E.snapshotCheckout originalSame))
