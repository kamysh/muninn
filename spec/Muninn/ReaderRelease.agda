{-# OPTIONS --safe #-}
-- A finished search releases its private reader without removing indexed data.
module Muninn.ReaderRelease where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.ExclusionClassifier as C
import Muninn.CleanupStorage as Storage
import Muninn.CleanupEffects as Effects
import Muninn.CleanupProtection as Protection
import Muninn.CleanupReleased as Released
import Muninn.CleanupAdmission as Admission
import Muninn.ReceiptLedger as Ledger
open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (Bool; true; false)
open import Data.String using (String)
open import Data.List using (List; [])
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Relation.Unary.All as All
open All using (All)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
module DB = O.DB
module Exec = O.Execution

readerBody : ∀ body → O.kind body ≡ O.activeReaderK →
  Σ (List O.Reference) (λ refs → Σ String (λ payload → body ≡ O.activeReader refs payload))
readerBody (O.activeReader refs payload) same = refs , payload , refl

ReaderAt : O.Owner → ℕ → O.World → Set
ReaderAt owner key world = C.At world key (λ value → O.owner value ≡ owner × O.kind (O.body value) ≡ O.activeReaderK)

readerAt? : ∀ owner key world → Dec (ReaderAt owner key world)
readerAt? owner key world = C.at? world key _ (λ value → C.both (E.ownerEqual (O.owner value) owner)
  (C.kindEqual (O.kind (O.body value)) O.activeReaderK))

finishSnapshot : ∀ {A : Set} owner key → A → (O.World → A) → O.World → DB.Transaction A
finishSnapshot owner key ready replan world with readerAt? owner key world
... | yes actual = DB.remove key (DB.commit ready)
... | no different with DB.lookup key world
...   | nothing = DB.commit ready
...   | just value = DB.commit (replan world)

finish : ∀ {A : Set} → O.Owner → ℕ → A → (O.World → A) → DB.Transaction A
finish owner key ready replan = DB.scan (finishSnapshot owner key ready replan)

effects : ∀ {A : Set} owner key (ready : A) replan world →
  (proj₂ (DB.execute (finish owner key ready replan) world) ≡ world) ⊎
  (ReaderAt owner key world × proj₂ (DB.execute (finish owner key ready replan) world) ≡ DB.delete key world)
effects owner key ready replan world with readerAt? owner key world
... | yes actual = inj₂ (actual , refl)
... | no different with DB.lookup key world
...   | nothing = inj₁ refl
...   | just value = inj₁ refl

executes : ∀ {A : Set} owner key (ready : A) replan world → ReaderAt owner key world →
  DB.execute (finish owner key ready replan) world ≡ (ready , DB.delete key world)
executes owner key ready replan world actual with readerAt? owner key world
... | yes same = refl
... | no different = ⊥-elim (different actual)

absent : ∀ {A : Set} owner key (ready : A) replan world → DB.lookup key world ≡ nothing →
  DB.execute (finish owner key ready replan) world ≡ (ready , world)
absent owner key ready replan world missing with readerAt? owner key world
... | yes (value , found , rest) = ⊥-elim (Effects.presentNotAbsent (trans (sym found) missing))
... | no different rewrite missing = refl

idempotent : ∀ {A : Set} owner key (ready : A) replan world →
  DB.execute (finish owner key ready replan) (proj₂ (DB.execute (finish owner key ready replan) world)) ≡
    DB.execute (finish owner key ready replan) world
idempotent owner key ready replan world with effects owner key ready replan world
... | inj₁ same = cong (DB.execute (finish owner key ready replan)) same
... | inj₂ (actual , same) = trans (cong (DB.execute (finish owner key ready replan)) same)
  (trans (absent owner key ready replan (DB.delete key world) (DB.deleteAbsent key world))
    (sym (executes owner key ready replan world actual)))

lookupBeforeDelete : ∀ world removed key value → DB.lookup key (DB.delete removed world) ≡ just value → DB.lookup key world ≡ just value
lookupBeforeDelete world removed key value found with removed ≟ key
... | yes refl = ⊥-elim (Effects.presentNotAbsent (trans (sym found) (DB.deleteAbsent key world)))
... | no different = trans (sym (DB.deletePreservesOther removed key world different)) found

privateUnreferenced : ∀ world owner key → O.Admissible world → ReaderAt owner key world → All (O.NoIncomingTo key) world
privateUnreferenced world owner key valid (reader , found , owned , sameKind) =
  O.privateUnreferenced key world reader valid found (cong O.privateTarget sameKind)

admissible : ∀ {A : Set} owner key (ready : A) replan world → O.Admissible world →
  O.Admissible (proj₂ (DB.execute (finish owner key ready replan) world))
admissible owner key ready replan world valid with effects owner key ready replan world
... | inj₁ same = subst O.Admissible (sym same) valid
... | inj₂ (actual , same) = subst O.Admissible (sym same)
  (O.deleteUnreferencedPreservesAdmissibility key world valid (privateUnreferenced world owner key valid actual))

differentFromReader : ∀ world owner removed → ReaderAt owner removed world → ∀ key value →
  DB.lookup key world ≡ just value → O.kind (O.body value) ≢ O.activeReaderK → removed ≢ key
differentFromReader world owner removed (reader , present , owned , sameKind) .removed value found nonReader refl =
  nonReader (trans (cong (λ value → O.kind (O.body value)) (just-injective (trans (sym found) present))) sameKind)

otherRow : ∀ {A : Set} owner removed (ready : A) replan world key → removed ≢ key →
  DB.lookup key (proj₂ (DB.execute (finish owner removed ready replan) world)) ≡ DB.lookup key world
otherRow owner removed ready replan world key different with effects owner removed ready replan world
... | inj₁ same = cong (DB.lookup key) same
... | inj₂ (actual , same) = trans (cong (DB.lookup key) same) (DB.deletePreservesOther removed key world different)

nonReaderRow : ∀ {A : Set} owner removed (ready : A) replan world key value →
  DB.lookup key world ≡ just value → O.kind (O.body value) ≢ O.activeReaderK →
  DB.lookup key (proj₂ (DB.execute (finish owner removed ready replan) world)) ≡ just value
nonReaderRow owner removed ready replan world key value found nonReader with effects owner removed ready replan world
... | inj₁ same = trans (cong (DB.lookup key) same) found
... | inj₂ (actual , same) = trans (cong (DB.lookup key) same)
  (trans (DB.deletePreservesOther removed key world (differentFromReader world owner removed actual key value found nonReader)) found)

readerMetadata : ∀ value → O.kind (O.body value) ≡ O.activeReaderK → E.indexed value ≡ Data.Bool.false
readerMetadata (O.recordOf owner body) same with readerBody body same
... | refs , payload , refl = refl

indexedRow : ∀ {A : Set} owner removed (ready : A) replan world key value →
  DB.lookup key world ≡ just value → E.indexed value ≡ Data.Bool.true →
  DB.lookup key (proj₂ (DB.execute (finish owner removed ready replan) world)) ≡ just value
indexedRow owner removed ready replan world key value found indexed = nonReaderRow owner removed ready replan world key value found
  (λ same → impossible (trans (sym indexed) (readerMetadata value same)))
  where impossible : Data.Bool.true ≢ Data.Bool.false
        impossible ()

savedWorkset : ∀ {A : Set} owner removed (ready : A) replan world task taskOwner requestId ids note →
  DB.lookup task world ≡ just (O.recordOf taskOwner (O.cleanupWork requestId ids note)) →
  DB.lookup task (proj₂ (DB.execute (finish owner removed ready replan) world)) ≡ just (O.recordOf taskOwner (O.cleanupWork requestId ids note))
savedWorkset owner removed ready replan world task taskOwner requestId ids note found =
  nonReaderRow owner removed ready replan world task _ found (λ ())

resolveBeforeDelete : ∀ world removed source ref → O.Resolves (DB.delete removed world) source ref → O.Resolves world source ref
resolveBeforeDelete world removed source ref resolved = record
  { value = O.Resolves.value resolved
  ; found = lookupBeforeDelete world removed (O.target ref) (O.Resolves.value resolved) (O.Resolves.found resolved)
  ; rightKind = O.Resolves.rightKind resolved; rightOwner = O.Resolves.rightOwner resolved }

finishedAbsent : ∀ {A : Set} owner removed (ready : A) replan world → ReaderAt owner removed world →
  DB.lookup removed (proj₂ (DB.execute (finish owner removed ready replan) world)) ≡ nothing
finishedAbsent owner removed ready replan world actual = trans
  (cong (λ result → DB.lookup removed (proj₂ result)) (executes owner removed ready replan world actual))
  (DB.deleteAbsent removed world)

receiptFrame : ∀ {A : Set} owner removed (ready : A) replan world →
  Ledger.ReceiptFrame world (proj₂ (DB.execute (finish owner removed ready replan) world))
receiptFrame owner removed ready replan world key taskOwner receiptData =
  (λ found → nonReaderRow owner removed ready replan world key _ found (λ ())) , backward
  where
  backward : DB.lookup key (proj₂ (DB.execute (finish owner removed ready replan) world)) ≡ just (O.recordOf taskOwner (O.receipt receiptData)) →
    DB.lookup key world ≡ just (O.recordOf taskOwner (O.receipt receiptData))
  backward found with effects owner removed ready replan world
  ... | inj₁ same = trans (sym (cong (DB.lookup key) same)) found
  ... | inj₂ (actual , same) = lookupBeforeDelete world removed key _ (trans (sym (cong (DB.lookup key) same)) found)

module Model (excluded : List String → String → Bool) where
  module M = E.Model excluded
  module Pins = Protection.Model excluded

  module Family (selection : E.Rule) where
    module Gate = Admission.Model.Family excluded selection

    protectedPresent : ∀ world key → M.Protected selection world key → Σ O.Record (λ value → DB.lookup key world ≡ just value)
    protectedPresent world .(O.target ref) (M.held source value ref found included resolved) = O.Resolves.value resolved , O.Resolves.found resolved
    protectedPresent world .(O.target ref) (M.required previous (M.reference source value ref found included resolved)) = O.Resolves.value resolved , O.Resolves.found resolved
    protectedPresent world child (M.required previous (M.attachment parent parentValue .child childValue parentFound childFound attached sameOwner)) = childValue , childFound

    mutual
      protectedBackward : ∀ world removed key → M.Protected selection (DB.delete removed world) key → M.Protected selection world key
      protectedBackward world removed .(O.target ref) (M.held source value ref found included resolved) =
        M.held source value ref (lookupBeforeDelete world removed source value found) included (resolveBeforeDelete world removed (O.owner value) ref resolved)
      protectedBackward world removed .(O.target ref) (M.required previous (M.reference source value ref found included resolved)) =
        M.requireReference source value ref (protectedBackward world removed source previous)
          (lookupBeforeDelete world removed source value found)
          (subst (λ refs → ref ∈ refs) (M.holdingReferences (M.readerOrigin previous) selection (DB.delete removed world) value) included)
          (resolveBeforeDelete world removed (O.owner value) ref resolved)
      protectedBackward world removed child (M.required previous (M.attachment parent parentValue .child childValue parentFound childFound attached sameOwner)) =
        M.required (protectedBackward world removed parent previous)
          (subst (λ mode → M.Dependency mode selection world parent child)
            (cong M.temporaryFor (sym (backwardReader world removed parent previous)))
            (M.attachment parent parentValue child childValue (lookupBeforeDelete world removed parent parentValue parentFound)
              (lookupBeforeDelete world removed child childValue childFound)
              (trans (Pins.holdingParentStable (M.readerOrigin previous) selection world (DB.delete removed world) childValue) attached) sameOwner))

      backwardReader : ∀ world removed key (pin : M.Protected selection (DB.delete removed world) key) →
        M.readerOrigin (protectedBackward world removed key pin) ≡ M.readerOrigin pin
      backwardReader world removed .(O.target ref) (M.held source value ref found included resolved) = refl
      backwardReader world removed .(O.target ref) (M.required previous (M.reference source value ref found included resolved)) = backwardReader world removed source previous
      backwardReader world removed child (M.required previous (M.attachment parent parentValue .child childValue parentFound childFound attached sameOwner)) =
        backwardReader world removed parent previous

    backwardSource : ∀ world removed key (pin : M.Protected selection (DB.delete removed world) key) →
      Gate.sourceOf (protectedBackward world removed key pin) ≡ Gate.sourceOf pin
    backwardSource world removed .(O.target ref) (M.held source value ref found included resolved) = refl
    backwardSource world removed .(O.target ref) (M.required previous (M.reference source value ref found included resolved)) = backwardSource world removed source previous
    backwardSource world removed child (M.required previous (M.attachment parent parentValue .child childValue parentFound childFound attached sameOwner)) =
      backwardSource world removed parent previous

    notFromRemoved : ∀ world removed key (pin : M.Protected selection (DB.delete removed world) key) → Gate.sourceOf pin ≢ removed
    notFromRemoved world removed .(O.target ref) (M.held .removed value ref found included resolved) refl =
      Effects.presentNotAbsent (trans (sym found) (DB.deleteAbsent removed world))
    notFromRemoved world removed key (M.required previous dependency) same = notFromRemoved world removed _ previous same

    noParentForReader : ∀ world value → O.kind (O.body value) ≡ O.activeReaderK → M.parentOf M.temporary selection world value ≡ nothing
    noParentForReader world (O.recordOf owner body) same with readerBody body same
    ... | refs , payload , refl = refl

    attachmentNotReader : ∀ world value ref → M.parentOf M.temporary selection world value ≡ just ref → O.kind (O.body value) ≢ O.activeReaderK
    attachmentNotReader world value ref attached same = impossible (trans (sym attached) (noParentForReader world value same))
      where impossible : just ref ≢ nothing
            impossible ()

    holdingAttachmentNotReader : ∀ flag world value ref → M.parentOf (M.temporaryFor flag) selection world value ≡ just ref → O.kind (O.body value) ≢ O.activeReaderK
    holdingAttachmentNotReader true world value ref ()
    holdingAttachmentNotReader false world value ref attached = attachmentNotReader world value ref attached

    module Removing (world : O.World) (owner : O.Owner) (removed : ℕ) (valid : O.Admissible world) (actual : ReaderAt owner removed world) where
      unreferenced = privateUnreferenced world owner removed valid actual

      resolvedSurvives : ∀ source value ref → DB.lookup source world ≡ just value → ref ∈ O.references (O.body value) →
        O.Resolves world (O.owner value) ref → O.Resolves (DB.delete removed world) (O.owner value) ref
      resolvedSurvives source value ref found included resolved = O.referenceSurvivesOtherDeletion world (O.owner value) ref removed
        (All.lookup (Storage.lookupAll world source value unreferenced found) included) resolved

      survivingProtectionDistinct : ∀ key → M.Protected selection (DB.delete removed world) key → removed ≢ key
      survivingProtectionDistinct .removed pin refl with protectedPresent (DB.delete removed world) removed pin
      ... | value , found = Effects.presentNotAbsent (trans (sym found) (DB.deleteAbsent removed world))

      mutual
        otherHolds : ∀ key (pin : M.Protected selection world key) → Gate.sourceOf pin ≢ removed → M.Protected selection (DB.delete removed world) key
        otherHolds .(O.target ref) (M.held source value ref found included resolved) different =
          M.held source value ref (trans (DB.deletePreservesOther removed source world (λ equal → different (sym equal))) found) included
            (resolvedSurvives source value ref found (Released.Model.heldRaw excluded value ref included) resolved)
        otherHolds .(O.target ref) (M.required previous (M.reference source value ref found included resolved)) different =
          M.requireReference source value ref earlier
            (trans (DB.deletePreservesOther removed source world (survivingProtectionDistinct source earlier)) found) raw
            (resolvedSurvives source value ref found raw resolved)
          where
          earlier = otherHolds source previous different
          raw = subst (λ refs → ref ∈ refs) (M.holdingReferences (M.readerOrigin previous) selection world value) included
        otherHolds child (M.required previous (M.attachment parent parentValue .child childValue parentFound childFound attached sameOwner)) different =
          M.required earlier
            (subst (λ mode → M.Dependency mode selection (DB.delete removed world) parent child)
              (cong M.temporaryFor (sym (otherReader parent previous different)))
              (M.attachment parent parentValue child childValue
                (trans (DB.deletePreservesOther removed parent world (survivingProtectionDistinct parent earlier)) parentFound)
                (trans (DB.deletePreservesOther removed child world (differentFromReader world owner removed actual child childValue childFound
                  (holdingAttachmentNotReader (M.readerOrigin previous) world childValue _ attached))) childFound)
                (trans (sym (Pins.holdingParentStable (M.readerOrigin previous) selection world (DB.delete removed world) childValue)) attached) sameOwner))
          where earlier = otherHolds parent previous different

        otherReader : ∀ key (pin : M.Protected selection world key) (different : Gate.sourceOf pin ≢ removed) →
          M.readerOrigin (otherHolds key pin different) ≡ M.readerOrigin pin
        otherReader .(O.target ref) (M.held source value ref found included resolved) different = refl
        otherReader .(O.target ref) (M.required previous (M.reference source value ref found included resolved)) different = otherReader source previous different
        otherReader child (M.required previous (M.attachment parent parentValue .child childValue parentFound childFound attached sameOwner)) different =
          otherReader parent previous different

    noNewProtection : ∀ {A : Set} owner removed (ready : A) replan world key →
      M.Protected selection (proj₂ (DB.execute (finish owner removed ready replan) world)) key → M.Protected selection world key
    noNewProtection owner removed ready replan world key pin with effects owner removed ready replan world
    ... | inj₁ same = subst (λ world → M.Protected selection world key) same pin
    ... | inj₂ (actual , same) = protectedBackward world removed key (subst (λ world → M.Protected selection world key) same pin)

    otherReaderHolds : ∀ {A : Set} owner removed (ready : A) replan world → O.Admissible world → ReaderAt owner removed world →
      ∀ key (pin : M.Protected selection world key) → Gate.sourceOf pin ≢ removed →
      M.Protected selection (proj₂ (DB.execute (finish owner removed ready replan) world)) key
    otherReaderHolds owner removed ready replan world valid actual key pin different =
      subst (λ world → M.Protected selection world key) (sym (cong proj₂ (executes owner removed ready replan world actual)))
        (Removing.otherHolds world owner removed valid actual key pin different)
