{-# OPTIONS --safe #-}
-- New structural searches select the actual current snapshot inside admission.
module Muninn.CurrentReader where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.CleanupAdmission as Admission
import Muninn.CleanupAdmissionStorage as Insert
import Muninn.CleanupResumption as Resumption
import Muninn.RecordAllocation as Allocation
import Muninn.ViewReplacement as Replacement
import Muninn.PublishedViews as Views
import Muninn.PublicationVisibility as Visibility
import Muninn.ReceiptLedger as Ledger
import Muninn.PendingRemoval as Removal
open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (Bool; true; false)
open import Data.String using (String)
open import Data.List using (List; []; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
module DB = O.DB

nothingNotJust : ∀ {A : Set} {value : A} → nothing ≡ just value → ⊥
nothingNotJust ()

module Model where
  module M = E.Model

  module Family (selection : E.Rule) (pointer selected : ℕ) where
    owner = E.targetOwner selection
    module Gate = Admission.Model.Family selection
    module Fresh = Allocation.Model.Family selection

    references : ℕ → List O.Reference
    references root = O.reference root O.structuralSnapshotK ∷ []

    recordRoot : O.Record → Maybe ℕ
    recordRoot (O.recordOf actualOwner body) with Replacement.publishedInfo body
    ... | nothing = nothing
    ... | just (checkout , root) with E.ownerEqual actualOwner owner | checkout ≟ selected
    ...   | yes same | yes matches = just root
    ...   | _ | _ = nothing

    recordKnown : ∀ root → recordRoot (O.recordOf owner (O.publishedView selected root)) ≡ just root
    recordKnown root with E.ownerEqual owner owner | selected ≟ selected
    ... | yes same | yes matches = refl
    ... | no different | _ = ⊥-elim (different refl)
    ... | _ | no different = ⊥-elim (different refl)

    recordSound : ∀ value root → recordRoot value ≡ just root → value ≡ O.recordOf owner (O.publishedView selected root)
    recordSound (O.recordOf actualOwner body) root seen with Replacement.publishedInfo body in info
    ... | nothing = impossible seen
      where impossible : nothing ≡ just root → O.recordOf actualOwner body ≡ O.recordOf owner (O.publishedView selected root)
            impossible ()
    ... | just (checkout , storedRoot) with E.ownerEqual actualOwner owner | checkout ≟ selected
    ...   | no different | _ = impossible seen
      where impossible : nothing ≡ just root → O.recordOf actualOwner body ≡ O.recordOf owner (O.publishedView selected root)
            impossible ()
    ...   | yes same | no different = impossible seen
      where impossible : nothing ≡ just root → O.recordOf actualOwner body ≡ O.recordOf owner (O.publishedView selected root)
            impossible ()
    ...   | yes refl | yes refl with just-injective seen
    ...     | refl = cong (O.recordOf owner) (Replacement.publishedBody body selected storedRoot info)

    currentRoot : O.World → Maybe ℕ
    currentRoot world with M.familyRegistered selection world | M.checkoutLive selection world selected
    ... | true | true with DB.lookup pointer world
    ...   | nothing = nothing
    ...   | just value = recordRoot value
    currentRoot world | _ | _ = nothing

    currentKnown : ∀ world root → M.familyRegistered selection world ≡ true → M.checkoutLive selection world selected ≡ true →
      DB.lookup pointer world ≡ just (O.recordOf owner (O.publishedView selected root)) → currentRoot world ≡ just root
    currentKnown world root registered live found rewrite registered | live | found = recordKnown root

    currentSound : ∀ world root → currentRoot world ≡ just root →
      DB.lookup pointer world ≡ just (O.recordOf owner (O.publishedView selected root)) ×
        (M.familyRegistered selection world ≡ true × M.checkoutLive selection world selected ≡ true)
    currentSound world root seen with M.familyRegistered selection world in registered | M.checkoutLive selection world selected in live
    ... | false | _ = ⊥-elim (nothingNotJust seen)
    ... | true | false = ⊥-elim (nothingNotJust seen)
    ... | true | true with DB.lookup pointer world in found
    ...   | nothing = ⊥-elim (nothingNotJust seen)
    ...   | just value = cong just (recordSound value root seen) , refl , refl

    admitSnapshot : ∀ {A : Set} → String → (ℕ → ℕ → A) → (O.World → A) → O.World → DB.Transaction A
    admitSnapshot payload ready replan world with currentRoot world
    ... | nothing = DB.commit (replan world)
    ... | just root = Fresh.admit (references root) payload (ready root) replan

    admit : ∀ {A : Set} → String → (ℕ → ℕ → A) → (O.World → A) → DB.Transaction A
    admit payload ready replan = DB.scan (admitSnapshot payload ready replan)

    fromCurrent : ∀ {A : Set} world root payload (ready : ℕ → ℕ → A) replan → currentRoot world ≡ just root →
      DB.execute (admit payload ready replan) world ≡ DB.execute (Fresh.admit (references root) payload (ready root) replan) world
    fromCurrent world root payload ready replan found rewrite found = refl

    contextContinuation : ∀ {A : Set} world payload (ready : ℕ → ℕ → A) replan → currentRoot world ≡ nothing →
      DB.execute (admit payload ready replan) world ≡ (replan world , world)
    contextContinuation world payload ready replan missing rewrite missing = refl

    admissible : ∀ {A : Set} world payload (ready : ℕ → ℕ → A) replan → O.Admissible world →
      O.Admissible (proj₂ (DB.execute (admit payload ready replan) world))
    admissible world payload ready replan valid with currentRoot world
    ... | nothing = valid
    ... | just root = Fresh.admissionAdmissible (references root) payload (ready root) replan world valid

    receipts : ∀ {A : Set} world payload (ready : ℕ → ℕ → A) replan →
      Ledger.ReceiptFrame world (proj₂ (DB.execute (admit payload ready replan) world))
    receipts world payload ready replan with currentRoot world
    ... | nothing = λ key recordOwner receiptData → (λ found → found) , (λ found → found)
    ... | just root = Fresh.admissionReceipts (references root) payload (ready root) replan world

    oldLookup : ∀ {A : Set} world payload (ready : ℕ → ℕ → A) replan key value → DB.lookup key world ≡ just value →
      DB.lookup key (proj₂ (DB.execute (admit payload ready replan) world)) ≡ just value
    oldLookup world payload ready replan key value found with currentRoot world
    ... | nothing = found
    ... | just root with Gate.effects (Allocation.freshId world) (references root) payload (ready root) replan world
    ...   | inj₁ same = trans (cong (DB.lookup key) same) found
    ...   | inj₂ (fresh , resolved , clean , allowed , same) = trans (cong (DB.lookup key) same)
      (Insert.oldLookup world (Allocation.freshId world) (Gate.reader (references root) payload) fresh key value found)

    savedWorkset : ∀ {A : Set} world payload (ready : ℕ → ℕ → A) replan task requestId ids text →
      DB.lookup task world ≡ just (O.recordOf owner (O.cleanupWork requestId ids text)) →
      DB.lookup task (proj₂ (DB.execute (admit payload ready replan) world)) ≡ just (O.recordOf owner (O.cleanupWork requestId ids text))
    savedWorkset world payload ready replan task requestId ids text found with currentRoot world
    ... | nothing = found
    ... | just root = Gate.savedWorkset (Allocation.freshId world) (references root) payload (ready root) replan world task requestId ids text found

    existingUse : ∀ {A : Set} world payload (ready : ℕ → ℕ → A) replan key → M.Protected selection world key →
      M.Protected selection (proj₂ (DB.execute (admit payload ready replan) world)) key
    existingUse world payload ready replan key pin with currentRoot world
    ... | nothing = pin
    ... | just root = Gate.existingUse (Allocation.freshId world) (references root) payload (ready root) replan world key pin

    selectedSnapshot : ∀ world root → Views.Valid world → currentRoot world ≡ just root → Views.SnapshotAt world owner selected root
    selectedSnapshot world root valid observed = Views.Valid.sameCheckout valid pointer owner selected root (proj₁ (currentSound world root observed))

    resolved : ∀ world root → Views.Valid world → currentRoot world ≡ just root → Gate.Resolved world (references root)
    resolved world root valid observed with selectedSnapshot world root valid observed
    ... | nodes , edges , payload , found = record
      { value = O.recordOf owner (O.structuralSnapshot selected nodes edges payload)
      ; found = found; rightKind = refl; rightOwner = O.own } All.∷ All.[]

    accepts : ∀ {A : Set} world root payload (ready : ℕ → ℕ → A) replan → Views.Valid world →
      currentRoot world ≡ just root → Removal.pending (E.targetOwner selection) world ≡ false → Gate.Clean (Gate.proposed world (Allocation.freshId world) (references root) payload) (references root) →
      Gate.Allowed world (Allocation.freshId world) (references root) payload →
      DB.execute (admit payload ready replan) world ≡
        (ready root (Allocation.freshId world) , Gate.proposed world (Allocation.freshId world) (references root) payload)
    accepts world root payload ready replan valid observed notRemoving clean allowed = trans (fromCurrent world root payload ready replan observed)
      (Fresh.admits (references root) payload (ready root) replan world notRemoving (resolved world root valid observed) clean allowed)

    insertedViews : ∀ world slot refs payload → Insert.Fresh world slot → Views.Valid world →
      Views.Valid (Gate.proposed world slot refs payload)
    insertedViews world slot refs payload fresh valid = record
      { onePerCheckout = λ first second recordOwner checkout firstRoot secondRoot firstFound secondFound →
          Views.Valid.onePerCheckout valid first second recordOwner checkout firstRoot secondRoot
            (backward first _ firstFound (λ ())) (backward second _ secondFound (λ ()))
      ; sameCheckout = keepsCheckout }
      where
      after = Gate.proposed world slot refs payload
      backward : ∀ key value → DB.lookup key after ≡ just value → O.kind (O.body value) ≢ O.activeReaderK →
        DB.lookup key world ≡ just value
      backward key value found different with slot ≟ key
      ... | yes refl = ⊥-elim (different (sym (cong (λ row → O.kind (O.body row))
        (just-injective (trans (sym (DB.writeVisible slot (Gate.reader refs payload) world)) found)))))
      ... | no distinct = trans (sym (DB.writePreservesOther slot key (Gate.reader refs payload) world distinct)) found

      keepsCheckout : ∀ currentPointer recordOwner checkout root →
        DB.lookup currentPointer after ≡ just (O.recordOf recordOwner (O.publishedView checkout root)) →
        Views.SnapshotAt after recordOwner checkout root
      keepsCheckout currentPointer recordOwner checkout root found with
        Views.Valid.sameCheckout valid currentPointer recordOwner checkout root (backward currentPointer _ found (λ ()))
      ... | nodes , edges , text , snapshotFound = nodes , edges , text , Insert.oldLookup world slot (Gate.reader refs payload) fresh root _ snapshotFound

    currentViews : ∀ {A : Set} world payload (ready : ℕ → ℕ → A) replan → Views.Valid world →
      Views.Valid (proj₂ (DB.execute (admit payload ready replan) world))
    currentViews world payload ready replan valid with currentRoot world
    ... | nothing = valid
    ... | just root with Gate.effects (Allocation.freshId world) (references root) payload (ready root) replan world
    ...   | inj₁ same = subst Views.Valid (sym same) valid
    ...   | inj₂ (fresh , resolved , clean , allowed , same) = subst Views.Valid (sym same)
      (insertedViews world (Allocation.freshId world) (references root) payload fresh valid)

    cleanCurrent : ∀ world root payload → Views.Valid world → currentRoot world ≡ just root →
      (∀ value → DB.lookup root world ≡ just value → M.project selection world value ≡ value) →
      Gate.Clean (Gate.proposed world (Allocation.freshId world) (references root) payload) (references root)
    cleanCurrent world root payload valid observed canonical with selectedSnapshot world root valid observed
    ... | nodes , edges , text , found =
      (O.recordOf owner (O.structuralSnapshot selected nodes edges text) ,
        Insert.oldLookup world slot (Gate.reader (references root) payload) (Allocation.fresh world) root _ found ,
        refl , O.own , Frame.canonicalPersists _ (canonical _ found) , refl) All.∷ All.[]
      where
      slot = Allocation.freshId world
      module Frame = Visibility.Model.Insert selection world slot (Gate.reader (references root) payload)
        (Allocation.fresh world) (Visibility.reader owner (references root) payload)

    module AfterCleanup (before : O.World) (valid : O.Admissible before) (viewsValid : Views.Valid before) where
      module Prepared = Resumption.Model.Current selection before valid
      module ViewCleanup = Views.Model.Cleanup selection before Prepared.intent
      after = Prepared.after

      viewsAfter : Views.Valid after
      viewsAfter = ViewCleanup.validAfterCleanup Prepared.trail valid viewsValid

      needed : ∀ root → currentRoot after ≡ just root → M.Needed selection after root
      needed root observed with currentSound after root observed
      ... | found , registered , live = Views.Model.currentSnapshotNeeded selection after pointer selected root
        Prepared.validAfter found registered live

      canonical : Prepared.Work.Use.Released before → ∀ root → currentRoot after ≡ just root →
        ∀ value → DB.lookup root after ≡ just value → M.project selection after value ≡ value
      canonical released root observed value found with selectedSnapshot after root viewsAfter observed
      ... | nodes , edges , payload , snapshotFound = Prepared.Work.canonicalAtRest after root value
        (Prepared.Work.Use.releasedTrace Prepared.trail valid released)
        (Prepared.Work.Pass.Result.noEdit Prepared.result) found
        (Prepared.coveredAfter root value found
          (cong O.owner (just-injective (trans (sym found) snapshotFound))))
        (needed root observed)

      finishes : ∀ {A : Set} root payload (ready : ℕ → ℕ → A) replan →
        Prepared.Work.Use.Released before → currentRoot after ≡ just root → Removal.pending (E.targetOwner selection) after ≡ false →
        DB.execute (admit payload ready replan) after ≡
          (ready root (Allocation.freshId after) , Gate.proposed after (Allocation.freshId after) (references root) payload)
      finishes root payload ready replan released observed notRemoving = accepts after root payload ready replan viewsAfter observed notRemoving
        (cleanCurrent after root payload viewsAfter observed (canonical released root observed))
        (Prepared.allowed released (Allocation.freshId after) (references root) payload)
