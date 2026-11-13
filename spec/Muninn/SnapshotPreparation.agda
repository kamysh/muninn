{-# OPTIONS --safe #-}
-- Prepare a filtered snapshot inside the caller's atomic publication transaction.
module Muninn.SnapshotPreparation where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.CleanupStorage as Storage
import Muninn.CleanupAdmissionStorage as Insert
import Muninn.CleanupObservations as Observations
import Muninn.CleanupHistory as History
import Muninn.CleanupAlignment as Alignment
import Muninn.RecordAllocation as Allocation
import Muninn.PublishedViews as Views
import Muninn.ReceiptLedger as Ledger
open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (Bool; true; false)
open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Relation.Unary.All as All
open All using (All)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
module DB = O.DB

filterIdempotent : ∀ keep keys → E.filterKeys keep (E.filterKeys keep keys) ≡ E.filterKeys keep keys
filterIdempotent keep [] = refl
filterIdempotent keep (first ∷ keys) with keep first in selected
... | true rewrite selected = cong (first ∷_) (filterIdempotent keep keys)
... | false = filterIdempotent keep keys

module Model where
  module M = E.Model
  module Store = Storage.Model
  module Added = Insert.Model
  module Obs = Observations.Model

  projectIdempotent : ∀ selection world value →
    M.project selection world (M.project selection world value) ≡ M.project selection world value
  projectIdempotent = Store.projectIdempotent

  module Family (selection : E.Rule) where
    owner = E.targetOwner selection

    -- No commit here: publication continues in this same transaction.
    prepareValue : ∀ {A : Set} → (ℕ → DB.Transaction A) → (O.World → DB.Transaction A) →
      O.World → Maybe O.Record → DB.Transaction A
    prepareValue next replan world nothing = replan world
    prepareValue next replan world (just value) with Observations.snapshotView value
    ... | Observations.plain nonSnapshot = replan world
    ... | Observations.delta owner selected version path answer = replan world
    ... | Observations.snapshot sourceOwner selected nodes edges payload with E.ownerEqual sourceOwner owner
    ...   | yes same = DB.put (Allocation.freshId world) (M.project selection world (O.recordOf sourceOwner (O.structuralSnapshot selected nodes edges payload))) (next (Allocation.freshId world))
    ...   | no different = replan world

    prepare : ∀ {A : Set} → ℕ → (ℕ → DB.Transaction A) → (O.World → DB.Transaction A) → DB.Transaction A
    prepare source next replan = DB.scan (λ world → prepareValue next replan world (DB.lookup source world))

    prepares : ∀ {A : Set} world source selected nodes edges payload (next : ℕ → DB.Transaction A) replan →
      DB.lookup source world ≡ just (O.recordOf owner (O.structuralSnapshot selected nodes edges payload)) →
      DB.evaluate (prepare source next replan) world ≡
        DB.evaluate (next (Allocation.freshId world))
          (DB.write (Allocation.freshId world) (M.project selection world (O.recordOf owner (O.structuralSnapshot selected nodes edges payload))) world)
    prepares world source selected nodes edges payload next replan found rewrite found with E.ownerEqual owner owner in decision
    ... | yes same rewrite decision = refl
    ... | no different = ⊥-elim (different refl)

    missingUsesContinuation : ∀ {A : Set} world source (next : ℕ → DB.Transaction A) replan →
      DB.lookup source world ≡ nothing →
      DB.evaluate (prepare source next replan) world ≡ DB.evaluate (replan world) world
    missingUsesContinuation world source next replan missing rewrite missing = refl

    otherFamilyUsesContinuation : ∀ {A : Set} world source sourceOwner selected nodes edges payload
      (next : ℕ → DB.Transaction A) replan →
      sourceOwner ≢ owner →
      DB.lookup source world ≡ just (O.recordOf sourceOwner (O.structuralSnapshot selected nodes edges payload)) →
      DB.evaluate (prepare source next replan) world ≡ DB.evaluate (replan world) world
    otherFamilyUsesContinuation world source sourceOwner selected nodes edges payload next replan different found
      rewrite found with E.ownerEqual sourceOwner owner
    ... | yes same = ⊥-elim (different same)
    ... | no denied = refl

    module Current (before : O.World) (valid : O.Admissible before) (viewsValid : Views.Valid before)
      (pointer source selected : ℕ) (nodes edges : List ℕ) (payload : String)
      (found : DB.lookup source before ≡ just (O.recordOf owner (O.structuralSnapshot selected nodes edges payload)))
      (published : DB.lookup pointer before ≡ just (O.recordOf owner (O.publishedView selected source)))
      (registered : M.familyRegistered selection before ≡ true) (live : M.checkoutLive selection before selected ≡ true) where

      original = O.recordOf owner (O.structuralSnapshot selected nodes edges payload)
      slot = Allocation.freshId before
      fresh = Allocation.fresh before
      copied = M.project selection before original
      after = DB.write slot copied before
      intent = M.captureIntent selection before (O.Admissible.unique valid)
      module Aligned = Alignment.Model.Contract selection before intent
      module Hist = History.Model.History selection before intent
      module CurrentView = Views.Model

      copiedOwner : O.owner copied ≡ owner
      copiedOwner = Store.projectOwner selection before original

      copiedKind : O.kind (O.body copied) ≡ O.structuralSnapshotK
      copiedKind = Store.projectKind selection before original

      sourceNeeded : M.Needed selection before source
      sourceNeeded = CurrentView.currentSnapshotNeeded selection before pointer selected source valid published registered live

      oldLookup : ∀ key value → DB.lookup key before ≡ just value → DB.lookup key after ≡ just value
      oldLookup = Insert.oldLookup before slot copied fresh

      copiedVisible : DB.lookup slot after ≡ just copied
      copiedVisible = DB.writeVisible slot copied before

      oldSound : All (O.Resolves before owner) (O.references (O.body original))
      oldSound = Storage.lookupAll before source original (O.Admissible.sound valid) found

      copiedSound : All (O.Resolves before (O.owner copied)) (O.references (O.body copied))
      copiedSound = subst (λ who → All (O.Resolves before who) (O.references (O.body copied))) (sym copiedOwner)
        (All.tabulate (λ {ref} included → All.lookup oldSound (Store.projectReferences selection before original ref included)))

      copiedPrivate : O.PrivateBookkeepingReferences copied
      copiedPrivate = All.tabulate (λ {ref} included → All.lookup
        (Storage.lookupAll before source original (O.Admissible.privateBookkeeping valid) found)
        (Store.projectReferences selection before original ref included))

      afterValid : O.Admissible after
      afterValid = Insert.insertAdmissible before slot copied valid fresh
        (Store.projectPlaced selection before original O.local) copiedSound copiedPrivate

      backwardPlain : ∀ key value → DB.lookup key after ≡ just value →
        O.kind (O.body value) ≢ O.structuralSnapshotK → DB.lookup key before ≡ just value
      backwardPlain key value present plain with slot ≟ key
      ... | yes refl = ⊥-elim (plain (trans
        (sym (cong (λ row → O.kind (O.body row)) (just-injective (trans (sym copiedVisible) present)))) copiedKind))
      ... | no different = trans (sym (DB.writePreservesOther slot key copied before different)) present

      support : Obs.Support selection before after
      support = record
        { safe = Added.insertionSafety selection before slot copied fresh
        ; uniqueBefore = O.Admissible.unique valid; uniqueAfter = O.Admissible.unique afterValid
        ; backwardPlain = λ key value present facts → backwardPlain key value present (proj₁ facts)
        ; backwardDelta = λ key value present kind → value ,
            backwardPlain key value present (λ equal → Storage.snapshotNotDelta (trans (sym equal) kind)) , Storage.deltaUnchanged value kind }

      viewsAfter : Views.Valid after
      viewsAfter = record
        { onePerCheckout = λ first second currentOwner checkout old current firstFound secondFound →
            Views.Valid.onePerCheckout viewsValid first second currentOwner checkout old current
              (backwardPlain first _ firstFound (λ ())) (backwardPlain second _ secondFound (λ ()))
        ; sameCheckout = keepsCheckout }
        where
        keepsCheckout : ∀ currentPointer currentOwner checkout snapshot →
          DB.lookup currentPointer after ≡ just (O.recordOf currentOwner (O.publishedView checkout snapshot)) →
          Views.SnapshotAt after currentOwner checkout snapshot
        keepsCheckout currentPointer currentOwner checkout snapshot currentFound
          with Views.Valid.sameCheckout viewsValid currentPointer currentOwner checkout snapshot
            (backwardPlain currentPointer _ currentFound (λ ()))
        ... | ns , es , text , snapshotFound = ns , es , text , oldLookup snapshot _ snapshotFound

      projectedSourceSame : M.project selection after original ≡ copied
      projectedSourceSame =
        trans (sym (Aligned.earlierCanonical before after support registered original)) (Hist.absorbProjection before after source selected nodes edges payload original valid support found sourceNeeded refl refl refl (λ key seen → seen) (λ key seen → seen))

      copiedCanonical : M.project selection after copied ≡ copied
      copiedCanonical = trans (cong (M.project selection after) (sym projectedSourceSame))
        (trans (projectIdempotent selection after original) projectedSourceSame)

      receiptFrame : Ledger.ReceiptFrame before after
      receiptFrame key receiptOwner receiptData =
        (λ present → oldLookup key _ present) ,
        (λ present → backwardPlain key _ present (λ ()))

      preparesCopy : ∀ {A : Set} (next : ℕ → DB.Transaction A) replan →
        DB.evaluate (prepare source next replan) before ≡ DB.evaluate (next slot) after
      preparesCopy next replan = prepares before source selected nodes edges payload next replan found
