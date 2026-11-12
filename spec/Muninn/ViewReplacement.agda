{-# OPTIONS --safe #-}
-- Guarded selector replacement within the existing publication transaction.
module Muninn.ViewReplacement where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.ExclusionClassifier as C
import Muninn.CleanupStorage as Storage
import Muninn.CleanupReleased as Released
import Muninn.PublishedViews as Views
import Muninn.ReceiptLedger as Ledger
import Muninn.Dialogue as D
open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (Bool; true; false)
open import Data.String using (String)
open import Data.List using (List; [])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.All as All
open All using (All; _∷_; [])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
module DB = O.DB

publishedInfo : O.Body → Maybe (ℕ × ℕ)
publishedInfo (O.publishedView selected snapshot) = just (selected , snapshot)
publishedInfo _ = nothing

publishedInfo? : ∀ selected snapshot body → Dec (publishedInfo body ≡ just (selected , snapshot))
publishedInfo? selected snapshot body with publishedInfo body
... | nothing = no (λ ())
... | just (actualSelected , actualSnapshot) with actualSelected ≟ selected | actualSnapshot ≟ snapshot
...   | yes refl | yes refl = yes refl
...   | no different | _ = no (λ same → different (cong proj₁ (just-injective same)))
...   | _ | no different = no (λ same → different (cong proj₂ (just-injective same)))

publishedBody : ∀ body selected snapshot →
  publishedInfo body ≡ just (selected , snapshot) → body ≡ O.publishedView selected snapshot
publishedBody (O.publishedView actualSelected actualSnapshot) selected snapshot same with just-injective same
... | refl = refl

snapshotCheckout? : ∀ selected value → Dec (E.snapshotCheckout value ≡ just selected)
snapshotCheckout? selected value with E.snapshotCheckout value
... | nothing = no (λ ())
... | just actual with actual ≟ selected
...   | yes refl = yes refl
...   | no different = no (λ same → different (just-injective same))

snapshotKind : ∀ value selected → E.snapshotCheckout value ≡ just selected → O.kind (O.body value) ≡ O.structuralSnapshotK
snapshotKind (O.recordOf owner (O.structuralSnapshot actual nodes edges payload)) selected same = refl

module Model (excluded : List String → String → Bool) where
  module M = E.Model excluded
  module Use = Released.Model excluded

  module Family (selection : E.Rule) where
    owner = E.targetOwner selection

    selectorNoIncoming : ∀ world pointer selected snapshot → O.Admissible world →
      DB.lookup pointer world ≡ just (O.recordOf owner (O.publishedView selected snapshot)) →
      All (O.NoIncomingTo pointer) world
    selectorNoIncoming world pointer selected snapshot valid found =
      O.privateUnreferenced pointer world (O.recordOf owner (O.publishedView selected snapshot)) valid found refl

    selectorParent : ∀ flag world selected snapshot →
      M.parentOf (M.temporaryFor flag) selection world (O.recordOf owner (O.publishedView selected snapshot)) ≡ nothing
    selectorParent true world selected snapshot = refl
    selectorParent false world selected snapshot = refl

    selectorUnheld : ∀ world pointer selected snapshot → O.Admissible world →
      DB.lookup pointer world ≡ just (O.recordOf owner (O.publishedView selected snapshot)) →
      ¬ M.Protected selection world pointer
    selectorUnheld world pointer selected snapshot valid found (M.held source value ref present included resolved) =
      All.lookup (Storage.lookupAll world source value
        (selectorNoIncoming world pointer selected snapshot valid found) present) (Use.heldRaw value ref included) refl
    selectorUnheld world pointer selected snapshot valid found (M.required previous (M.reference source value ref present included resolved)) =
      All.lookup (Storage.lookupAll world source value
        (selectorNoIncoming world pointer selected snapshot valid found) present)
        (subst (λ refs → ref ∈ refs) (M.holdingReferences (M.readerOrigin previous) selection world value) included) refl
    selectorUnheld world pointer selected snapshot valid found
      (M.required previous (M.attachment parent parentValue child childValue parentFound childFound attached sameOwner))
      with just-injective (trans (sym childFound) found)
    ... | refl = impossible (trans (sym attached) (selectorParent (M.readerOrigin previous) world selected snapshot))
      where impossible : just (O.reference parent (O.kind (O.body parentValue))) ≢ nothing
            impossible ()

    module Selector (pointer oldRoot newRoot selected : ℕ) where
      oldRecord = O.recordOf owner (O.publishedView selected oldRoot)
      newRecord = O.recordOf owner (O.publishedView selected newRoot)

      PointerAt : O.World → Set
      PointerAt world = C.At world pointer (λ value →
        O.owner value ≡ owner × publishedInfo (O.body value) ≡ just (selected , oldRoot))

      TargetAt : O.World → Set
      TargetAt world = C.At world newRoot (λ value →
        O.owner value ≡ owner × E.snapshotCheckout value ≡ just selected)

      pointerAt? : ∀ world → Dec (PointerAt world)
      pointerAt? world = C.at? world pointer _ (λ value →
        C.both (E.ownerEqual (O.owner value) owner) (publishedInfo? selected oldRoot (O.body value)))

      targetAt? : ∀ world → Dec (TargetAt world)
      targetAt? world = C.at? world newRoot _ (λ value →
        C.both (E.ownerEqual (O.owner value) owner) (snapshotCheckout? selected value))

      pointerFound : ∀ world → PointerAt world → DB.lookup pointer world ≡ just oldRecord
      pointerFound world (O.recordOf actualOwner body , found , owned , matches)
        with publishedBody body selected oldRoot matches
      ... | refl rewrite owned = found

      targetFound : ∀ world → TargetAt world → Views.SnapshotAt world owner selected newRoot
      targetFound world (value , found , owned , matches) =
        Views.snapshotFromFacts world owner selected newRoot value found (snapshotKind value selected matches) owned matches

      Ready : O.World → Set
      Ready world = PointerAt world × TargetAt world

      ready? : ∀ world → Dec (Ready world)
      ready? world = C.both (pointerAt? world) (targetAt? world)

      replaceSnapshot : String → String → O.World → DB.Transaction String
      replaceSnapshot result continuation world with ready? world
      ... | yes verified = DB.put pointer newRecord (DB.commit result)
      ... | no unresolved = DB.abort continuation

      replace : String → String → DB.Transaction String
      replace result continuation = DB.scan (replaceSnapshot result continuation)

      performs : ∀ world result continuation → Ready world →
        DB.evaluate (replace result continuation) world ≡ DB.committed result (DB.write pointer newRecord world)
      performs world result continuation verified with ready? world
      ... | yes same = refl
      ... | no unresolved = ⊥-elim (unresolved verified)

      continues : ∀ world result continuation → ¬ Ready world →
        DB.evaluate (replace result continuation) world ≡ DB.aborted continuation
      continues world result continuation unresolved with ready? world
      ... | yes verified = ⊥-elim (unresolved verified)
      ... | no same = refl

      committedReady : ∀ world result continuation reply after →
        DB.evaluate (replace result continuation) world ≡ DB.committed reply after →
        Ready world × after ≡ DB.write pointer newRecord world
      committedReady world result continuation reply after committed with ready? world
      ... | yes verified with committed
      ...   | refl = verified , refl
      committedReady world result continuation reply after committed | no unresolved = impossible committed
        where impossible : DB.aborted continuation ≡ DB.committed reply after → Ready world × after ≡ DB.write pointer newRecord world
              impossible ()

      unresolvedKeepsWorld : ∀ world result continuation → ¬ Ready world →
        DB.execute (replace result continuation) world ≡ (continuation , world)
      unresolvedKeepsWorld world result continuation unresolved =
        cong (λ outcome → DB.reply outcome , DB.publish world outcome) (continues world result continuation unresolved)

      guardedReceiptFrame : ∀ world → Ready world → Ledger.ReceiptFrame world (DB.write pointer newRecord world)
      guardedReceiptFrame world verified key receiptOwner receiptData = forward , backward
        where
        located = pointerFound world (proj₁ verified)
        forward : DB.lookup key world ≡ just (O.recordOf receiptOwner (O.receipt receiptData)) →
          DB.lookup key (DB.write pointer newRecord world) ≡ just (O.recordOf receiptOwner (O.receipt receiptData))
        forward found with pointer ≟ key
        ... | yes refl = ⊥-elim (impossible (just-injective (trans (sym located) found)))
          where impossible : oldRecord ≢ O.recordOf receiptOwner (O.receipt receiptData)
                impossible ()
        ... | no different = trans (DB.writePreservesOther pointer key newRecord world different) found
        backward : DB.lookup key (DB.write pointer newRecord world) ≡ just (O.recordOf receiptOwner (O.receipt receiptData)) →
          DB.lookup key world ≡ just (O.recordOf receiptOwner (O.receipt receiptData))
        backward found with pointer ≟ key
        ... | yes refl = ⊥-elim (impossible (just-injective (trans (sym (DB.writeVisible pointer newRecord world)) found)))
          where impossible : newRecord ≢ O.recordOf receiptOwner (O.receipt receiptData)
                impossible ()
        ... | no different = trans (sym (DB.writePreservesOther pointer key newRecord world different)) found

      effect : String → String → (String → D.Prompt) → Ledger.Effect
      effect result continuation guidance = record
        { transaction = replace result continuation; guidance = guidance
        ; isolates = λ world reply after committed →
            subst (Ledger.ReceiptFrame world) (sym (proj₂ (committedReady world result continuation reply after committed)))
              (guardedReceiptFrame world (proj₁ (committedReady world result continuation reply after committed))) }

      module Current (before : O.World) (valid : O.Admissible before) (viewsValid : Views.Valid before)
        (verified : Ready before) where
        located = pointerFound before (proj₁ verified)
        target = targetFound before (proj₂ verified)
        after = DB.write pointer newRecord before

        oldSound : All (O.Resolves before owner) (O.references (O.body oldRecord))
        oldSound = Storage.lookupAll before pointer oldRecord (O.Admissible.sound valid) located

        targetResolves : O.Resolves before owner (O.reference newRoot O.structuralSnapshotK)
        targetResolves with target
        ... | nodes , edges , payload , found = record
          { value = O.recordOf owner (O.structuralSnapshot selected nodes edges payload)
          ; found = found; rightKind = refl; rightOwner = O.own }

        afterValid : O.Admissible after
        afterValid = Storage.writeResolvedAdmissible before pointer oldRecord newRecord valid located refl refl O.local
          (All.lookup oldSound (here refl) ∷ targetResolves ∷ []) (refl ∷ refl ∷ [])

        notSelector : ∀ key value → DB.lookup key before ≡ just value →
          O.kind (O.body value) ≢ O.publishedViewK → key ≢ pointer
        notSelector .pointer value found distinct refl =
          distinct (cong (λ row → O.kind (O.body row)) (just-injective (trans (sym found) located)))

        oldLookup : ∀ key value → key ≢ pointer → DB.lookup key before ≡ just value → DB.lookup key after ≡ just value
        oldLookup key value different found = trans
          (DB.writePreservesOther pointer key newRecord before (λ same → different (sym same))) found

        snapshotPreserved : ∀ currentOwner checkout root nodes edges payload →
          DB.lookup root before ≡ just (O.recordOf currentOwner (O.structuralSnapshot checkout nodes edges payload)) →
          DB.lookup root after ≡ just (O.recordOf currentOwner (O.structuralSnapshot checkout nodes edges payload))
        snapshotPreserved currentOwner checkout root nodes edges payload found =
          oldLookup root _ (notSelector root _ found (λ ())) found

        protectedRecord : ∀ key value → DB.lookup key before ≡ just value →
          M.Protected selection before key → DB.lookup key after ≡ just value
        protectedRecord key value found pinned with pointer ≟ key
        ... | yes refl = ⊥-elim (selectorUnheld before pointer selected oldRoot valid located pinned)
        ... | no different = trans (DB.writePreservesOther pointer key newRecord before different) found

        receiptFrame : Ledger.ReceiptFrame before after
        receiptFrame = guardedReceiptFrame before verified

        currentVisible : DB.lookup pointer after ≡ just newRecord
        currentVisible = DB.writeVisible pointer newRecord before

        associationBefore : ∀ key currentOwner checkout root →
          DB.lookup key after ≡ just (O.recordOf currentOwner (O.publishedView checkout root)) →
          Σ ℕ (λ prior → DB.lookup key before ≡ just (O.recordOf currentOwner (O.publishedView checkout prior)))
        associationBefore key currentOwner checkout root found with pointer ≟ key
        ... | yes refl with just-injective (trans (sym (DB.writeVisible pointer newRecord before)) found)
        ...   | refl = oldRoot , located
        associationBefore key currentOwner checkout root found | no different =
          root , trans (sym (DB.writePreservesOther pointer key newRecord before different)) found

        viewsAfter : Views.Valid after
        viewsAfter = record
          { onePerCheckout = unique
          ; sameCheckout = keepsCheckout }
          where
          unique : ∀ first second currentOwner checkout firstRoot secondRoot →
            DB.lookup first after ≡ just (O.recordOf currentOwner (O.publishedView checkout firstRoot)) →
            DB.lookup second after ≡ just (O.recordOf currentOwner (O.publishedView checkout secondRoot)) →
            first ≡ second
          unique first second currentOwner checkout firstRoot secondRoot firstFound secondFound
            with associationBefore first currentOwner checkout firstRoot firstFound |
                 associationBefore second currentOwner checkout secondRoot secondFound
          ... | prior , firstBefore | other , secondBefore =
            Views.Valid.onePerCheckout viewsValid first second currentOwner checkout prior other firstBefore secondBefore

          keepsCheckout : ∀ key currentOwner checkout root →
            DB.lookup key after ≡ just (O.recordOf currentOwner (O.publishedView checkout root)) →
            Views.SnapshotAt after currentOwner checkout root
          keepsCheckout key currentOwner checkout root found with pointer ≟ key
          ... | yes refl with just-injective (trans (sym (DB.writeVisible pointer newRecord before)) found)
          ...   | refl with target
          ...     | nodes , edges , payload , targetFound =
            nodes , edges , payload , snapshotPreserved owner selected newRoot nodes edges payload targetFound
          keepsCheckout key currentOwner checkout root found | no different
            with Views.Valid.sameCheckout viewsValid key currentOwner checkout root
              (trans (sym (DB.writePreservesOther pointer key newRecord before different)) found)
          ... | nodes , edges , payload , targetFound =
            nodes , edges , payload , snapshotPreserved currentOwner checkout root nodes edges payload targetFound
