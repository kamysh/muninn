{-# OPTIONS --safe #-}
-- Fixed identities remain tracked until completion. The proof-carrying scan
-- cannot report success merely because a cursor forgot a retained record.
module Muninn.Workset where

open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.Nat using (ℕ; suc; _<_; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Bool using (Bool; true; false; not; if_then_else_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Relation.Nullary using (Dec)
import Muninn.Database
import Relation.Nullary

module Queue (Key Value : Set) (equal : (a b : Key) → Dec (a ≡ b)) where
  module DB = Muninn.Database.Store Key Value equal
  Row = Key × Value


  record Manifest : Set where
    constructor manifest
    field originalIds : List Key

  contains : Key → List Key → Bool
  contains key [] = false
  contains key (other ∷ rest) with equal key other
  ... | Relation.Nullary.yes _ = true
  ... | Relation.Nullary.no _ = contains key rest

  private
    module For (captured : Key → Bool) (useful held : Value → Bool) where
      -- Independent world predicate: every stored captured record is useful.
      -- Absent records satisfy it without removing their identity from the task.
      obligation : Row → Bool
      obligation (key , value) = if captured key then useful value else true

      deletable : Row → Bool
      deletable (key , value) = if captured key then
        (if useful value then false else not (held value)) else false

      Goal : DB.Rows → Set
      Goal rows = All (λ row → obligation row ≡ true) rows

      Available : DB.Rows → Set
      Available rows = Any (λ row → deletable row ≡ true) rows

      data Decision (rows : DB.Rows) : Set where
        satisfied : Goal rows → Decision rows
        waiting : All (λ row → deletable row ≡ false) rows →
          Any (λ row → obligation row ≡ false) rows → Decision rows
        advance : Available rows → Decision rows

      goodNotDeletable : ∀ row → obligation row ≡ true → deletable row ≡ false
      goodNotDeletable (key , value) good with captured key
      ... | false = refl
      ... | true with useful value | good
      ...   | true | refl = refl

      goodAllNotDeletable : ∀ {rows} → Goal rows → All (λ row → deletable row ≡ false) rows
      goodAllNotDeletable [] = []
      goodAllNotDeletable (good ∷ rest) = goodNotDeletable _ good ∷ goodAllNotDeletable rest

      liftGood : ∀ row {rows} → obligation row ≡ true → Decision rows → Decision (row ∷ rows)
      liftGood row good (satisfied rest) = satisfied (good ∷ rest)
      liftGood row good (waiting locked unmet) = waiting (goodNotDeletable row good ∷ locked) (there unmet)
      liftGood row good (advance available) = advance (there available)

      liftBlocked : ∀ row {rows} → obligation row ≡ false → deletable row ≡ false →
        Decision rows → Decision (row ∷ rows)
      liftBlocked row unmet locked (satisfied rest) =
        waiting (locked ∷ goodAllNotDeletable rest) (here unmet)
      liftBlocked row unmet locked (waiting rest other) = waiting (locked ∷ rest) (here unmet)
      liftBlocked row unmet locked (advance available) = advance (there available)

      inspect : ∀ rows → Decision rows
      inspect [] = satisfied []
      inspect ((key , value) ∷ rows) with captured key in selected
      ... | false = liftGood (key , value) (cong (λ b → if b then useful value else true) selected) (inspect rows)
      ... | true with useful value in needed
      ...   | true = liftGood (key , value) (trans (cong (λ b → if b then useful value else true) selected) needed) (inspect rows)
      ...   | false with held value in pinned
      ...     | false = advance (here (trans (cong (λ b → if b then (if useful value then false else not (held value)) else false) selected) (trans (cong (λ b → if b then false else not (held value)) needed) (cong not pinned))))
      ...     | true = liftBlocked (key , value) (trans (cong (λ b → if b then useful value else true) selected) needed) (trans (cong (λ b → if b then (if useful value then false else not (held value)) else false) selected) (trans (cong (λ b → if b then false else not (held value)) needed) (cong not pinned))) (inspect rows)

      retain : DB.Predicate
      retain key value = not (deletable (key , value))

      dirtyFromAvailable : ∀ {rows} → Available rows → DB.dirty retain rows ≡ true
      dirtyFromAvailable {((key , value) ∷ rows)} (here free)
        with deletable (key , value) | free
      ... | true | refl = refl
      dirtyFromAvailable {((key , value) ∷ rows)} (there available)
        with deletable (key , value)
      ... | true = refl
      ... | false = dirtyFromAvailable available

      strictlyProgresses : ∀ rows → Available rows →
        length (DB.eraseOne retain rows) < length rows
      strictlyProgresses rows available = DB.eraseDecreases retain rows (dirtyFromAvailable available)

      actionableWithoutReaders : ∀ row → (∀ value → useful value ≡ held value) →
        obligation row ≡ false → deletable row ≡ true
      actionableWithoutReaders (key , value) same unmet with captured key
      ... | true with useful value | held value | same value | unmet
      ...   | false | false | refl | refl = refl

      noWaitingWithoutReaders : ∀ {rows} → (∀ value → useful value ≡ held value) →
        All (λ row → deletable row ≡ false) rows → Any (λ row → obligation row ≡ false) rows → ⊥
      noWaitingWithoutReaders same (locked ∷ rest) (here unmet)
        with trans (sym locked) (actionableWithoutReaders _ same unmet)
      ... | ()
      noWaitingWithoutReaders same (locked ∷ rest) (there unmet) =
        noWaitingWithoutReaders same rest unmet

      tracked : DB.Predicate
      tracked key value = captured key

      remaining : DB.Rows → ℕ
      remaining rows = length (DB.select tracked rows)

      freeCaptured : ∀ key value → deletable (key , value) ≡ true → captured key ≡ true
      freeCaptured key value free with captured key
      ... | true = refl
      ... | false with free
      ...   | ()

      strictlyCapturedProgresses : ∀ rows → Available rows →
        remaining (DB.eraseOne retain rows) < remaining rows
      strictlyCapturedProgresses ((key , value) ∷ rows) available
        with deletable (key , value) in free
      ... | true rewrite freeCaptured key value free = ≤-refl
      ... | false with available
      ...   | here impossible with trans (sym free) impossible
      ...     | ()
      strictlyCapturedProgresses ((key , value) ∷ rows) available | false | there rest
        with captured key
      ... | true = s≤s (strictlyCapturedProgresses rows rest)
      ... | false = strictlyCapturedProgresses rows rest

      trackedDeleteOutside : ∀ key rows → captured key ≡ false →
        DB.select tracked (DB.delete key rows) ≡ DB.select tracked rows
      trackedDeleteOutside key [] outside = refl
      trackedDeleteOutside key ((other , value) ∷ rows) outside with equal key other
      ... | Relation.Nullary.yes refl rewrite outside = trackedDeleteOutside key rows outside
      ... | Relation.Nullary.no different with captured other
      ...   | true = cong ((other , value) ∷_) (trackedDeleteOutside key rows outside)
      ...   | false = trackedDeleteOutside key rows outside

      newUnrelatedRecordDoesNotGrowTask : ∀ key value rows → captured key ≡ false →
        remaining (DB.write key value rows) ≡ remaining rows
      newUnrelatedRecordDoesNotGrowTask key value rows outside rewrite outside =
        cong length (trackedDeleteOutside key rows outside)


  -- Public kernel uses a FINITE immutable list, not an open predicate that a
  -- later indexing pass can extend. The saved task row is outside this list.
  module Fixed (saved : Manifest) (useful held : Value → Bool) where
    captured : Key → Bool
    captured key = contains key (Manifest.originalIds saved)

    module View = For captured useful held

    observe : ∀ rows → View.Decision rows
    observe = View.inspect

    commitOne : DB.Rows → DB.Rows
    commitOne rows = proj₂ (DB.execute
      (DB.eraseRows 1 View.retain (DB.commit tt)) rows)

    next : ∀ rows → View.Decision rows → DB.Rows
    next rows (View.satisfied goal) = rows
    next rows (View.waiting blocked unmet) = rows
    next rows (View.advance free) = commitOne rows

    productiveStepDecreases : ∀ rows → View.Available rows →
      View.remaining (commitOne rows) < View.remaining rows
    productiveStepDecreases rows free = View.strictlyCapturedProgresses rows free

    waitingPreservesWholeCheckpoint : ∀ rows blocked unmet →
      next rows (View.waiting blocked unmet) ≡ rows
    waitingPreservesWholeCheckpoint rows blocked unmet = refl

    keepUncaptured : ∀ key value → captured key ≡ false → View.retain key value ≡ true
    keepUncaptured key value outside rewrite outside = refl

    -- Instantiating value with the saved manifest/receipt proves that the
    -- actual committed deletion cannot change or drop the durable checkpoint.
    preservesUncapturedCheckpoint : ∀ slot value rows → captured slot ≡ false →
      DB.lookup slot rows ≡ just value → DB.lookup slot (commitOne rows) ≡ just value
    preservesUncapturedCheckpoint slot value rows outside found =
      DB.eraseRetainsLookup View.retain rows slot value found (keepUncaptured slot value outside)

    noAvailable : ∀ rows → All (λ row → View.deletable row ≡ false) rows →
      View.Available rows → ⊥
    noAvailable (row ∷ rows) (blocked ∷ rest) (here free)
      with trans (sym blocked) free
    ... | ()
    noAvailable (row ∷ rows) (blocked ∷ rest) (there available) =
      noAvailable rows rest available

    data ChoosesAdvance (rows : DB.Rows) : View.Decision rows → Set where
      advances : ∀ free → ChoosesAdvance rows (View.advance free)

    inspectCannotStarveAvailableWork : ∀ rows → View.Available rows →
      ChoosesAdvance rows (observe rows)
    inspectCannotStarveAvailableWork rows available with observe rows
    ... | View.satisfied goal = ⊥-elim (noAvailable rows (View.goodAllNotDeletable goal) available)
    ... | View.waiting blocked unmet = ⊥-elim (noAvailable rows blocked available)
    ... | View.advance free = advances free

    availableAfterReadersRelease : ∀ rows → (∀ value → useful value ≡ held value) →
      Any (λ row → View.obligation row ≡ false) rows → View.Available rows
    availableAfterReadersRelease [] same ()
    availableAfterReadersRelease (row ∷ rows) same (here unmet) =
      here (View.actionableWithoutReaders row same unmet)
    availableAfterReadersRelease (row ∷ rows) same (there unmet) =
      there (availableAfterReadersRelease rows same unmet)
