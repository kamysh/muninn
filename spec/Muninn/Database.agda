{-# OPTIONS --safe #-}
-- Shared finite-store and transaction semantics. Operations may instantiate
-- keys/values, but cannot replace the meaning of read/write/delete/rollback.
module Muninn.Database where

open import Data.List using (List; []; _∷_; length)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _+_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Empty using (⊥-elim)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)

module Store (Key Value : Set) (equal : (a b : Key) → Dec (a ≡ b)) where
  Rows : Set
  Rows = List (Key × Value)

  lookup : Key → Rows → Maybe Value
  lookup key [] = nothing
  lookup key ((other , value) ∷ rows) with equal key other
  ... | yes _ = just value
  ... | no _ = lookup key rows

  delete : Key → Rows → Rows
  delete key [] = []
  delete key ((other , value) ∷ rows) with equal key other
  ... | yes _ = delete key rows
  ... | no _ = (other , value) ∷ delete key rows

  write : Key → Value → Rows → Rows
  write key value rows = (key , value) ∷ delete key rows

  deleteAbsent : ∀ key rows → lookup key (delete key rows) ≡ nothing
  deleteAbsent key [] = refl
  deleteAbsent key ((other , value) ∷ rows) with equal key other
  ... | yes _ = deleteAbsent key rows
  ... | no different with equal key other
  ...   | yes same = ⊥-elim (different same)
  ...   | no _ = deleteAbsent key rows

  deletePreservesOther : ∀ key other rows → ¬ (key ≡ other) →
    lookup other (delete key rows) ≡ lookup other rows
  deletePreservesOther key other [] distinct = refl
  deletePreservesOther key other ((stored , value) ∷ rows) distinct
    with equal key stored | equal other stored
  ... | yes refl | yes same = ⊥-elim (distinct (Relation.Binary.PropositionalEquality.sym same))
  ... | yes _ | no _ = deletePreservesOther key other rows distinct
  ... | no _ | yes same with equal other stored
  ...   | yes _ = refl
  ...   | no different = ⊥-elim (different same)
  deletePreservesOther key other ((stored , value) ∷ rows) distinct | no _ | no different
    with equal other stored
  ... | yes same = ⊥-elim (different same)
  ... | no _ = deletePreservesOther key other rows distinct

  lookupHead : ∀ key value rows → lookup key ((key , value) ∷ rows) ≡ just value
  lookupHead key value rows with equal key key
  ... | yes _ = refl
  ... | no different = ⊥-elim (different refl)

  lookupPast : ∀ key other value rows → ¬ (key ≡ other) →
    lookup key ((other , value) ∷ rows) ≡ lookup key rows
  lookupPast key other value rows distinct with equal key other
  ... | yes same = ⊥-elim (distinct same)
  ... | no _ = refl

  writePreservesOther : ∀ key other value rows → ¬ (key ≡ other) →
    lookup other (write key value rows) ≡ lookup other rows
  writePreservesOther key other value rows distinct with equal other key
  ... | yes same = ⊥-elim (distinct (Relation.Binary.PropositionalEquality.sym same))
  ... | no _ = deletePreservesOther key other rows distinct

  writeVisible : ∀ key value rows → lookup key (write key value rows) ≡ just value
  writeVisible key value rows with equal key key
  ... | yes _ = refl
  ... | no different = ⊥-elim (different refl)

  -- SQL-style bounded predicate deletion. The bound counts deleted rows,
  -- not examined rows, so a retained prefix cannot starve cleanup forever.
  Predicate : Set
  Predicate = Key → Value → Bool

  select : Predicate → Rows → Rows
  select keep [] = []
  select keep ((key , value) ∷ rows) with keep key value
  ... | true = (key , value) ∷ select keep rows
  ... | false = select keep rows

  eraseOne : Predicate → Rows → Rows
  eraseOne keep [] = []
  eraseOne keep ((key , value) ∷ rows) with keep key value
  ... | true = (key , value) ∷ eraseOne keep rows
  ... | false = rows

  eraseOneKept : ∀ keep key value rows → keep key value ≡ true →
    eraseOne keep ((key , value) ∷ rows) ≡ (key , value) ∷ eraseOne keep rows
  eraseOneKept keep key value rows kept with keep key value | kept
  ... | true | refl = refl

  eraseOneDropped : ∀ keep key value rows → keep key value ≡ false →
    eraseOne keep ((key , value) ∷ rows) ≡ rows
  eraseOneDropped keep key value rows dropped with keep key value | dropped
  ... | false | refl = refl

  erase : ℕ → Predicate → Rows → Rows
  erase zero keep rows = rows
  erase (suc n) keep rows = erase n keep (eraseOne keep rows)

  eraseOneAtMostOne : ∀ keep rows → length rows ≤ suc (length (eraseOne keep rows))
  eraseOneAtMostOne keep [] = z≤n
  eraseOneAtMostOne keep ((key , value) ∷ rows) with keep key value
  ... | true = s≤s (eraseOneAtMostOne keep rows)
  ... | false = ≤-refl

  eraseAtMostBound : ∀ bound keep rows →
    length rows ≤ bound + length (erase bound keep rows)
  eraseAtMostBound zero keep rows = ≤-refl
  eraseAtMostBound (suc bound) keep rows = ≤-trans (eraseOneAtMostOne keep rows)
    (s≤s (eraseAtMostBound bound keep (eraseOne keep rows)))

  eraseRetainsLookup : ∀ keep rows key value → lookup key rows ≡ just value →
    keep key value ≡ true → lookup key (eraseOne keep rows) ≡ just value
  eraseRetainsLookup keep ((other , stored) ∷ rows) key value found kept
    with equal key other
  ... | yes refl with found
  ...   | refl = Relation.Binary.PropositionalEquality.trans
      (cong (lookup key) (eraseOneKept keep key value rows kept)) (lookupHead key value (eraseOne keep rows))
  eraseRetainsLookup keep ((other , stored) ∷ rows) key value found kept | no different
    with keep other stored in decision
  ... | true = Relation.Binary.PropositionalEquality.trans
      (lookupPast key other stored (eraseOne keep rows) different)
      (eraseRetainsLookup keep rows key value found kept)
  ... | false = found

  dirty : Predicate → Rows → Bool
  dirty keep [] = false
  dirty keep ((key , value) ∷ rows) with keep key value
  ... | true = dirty keep rows
  ... | false = true

  eraseDecreases : ∀ keep rows → dirty keep rows ≡ true →
    length (eraseOne keep rows) < length rows
  eraseDecreases keep ((key , value) ∷ rows) hasDead with keep key value
  ... | true = s≤s (eraseDecreases keep rows hasDead)
  ... | false = ≤-refl

  cleanIsSelected : ∀ keep rows → dirty keep rows ≡ false → select keep rows ≡ rows
  cleanIsSelected keep [] clean = refl
  cleanIsSelected keep ((key , value) ∷ rows) clean with keep key value
  ... | true = cong ((key , value) ∷_) (cleanIsSelected keep rows clean)

  selectIdempotent : ∀ keep rows → select keep (select keep rows) ≡ select keep rows
  selectIdempotent keep [] = refl
  selectIdempotent keep ((key , value) ∷ rows) with keep key value in decision
  ... | true rewrite decision = cong ((key , value) ∷_) (selectIdempotent keep rows)
  ... | false = selectIdempotent keep rows

  selectAfterEraseOne : ∀ keep rows → select keep (eraseOne keep rows) ≡ select keep rows
  selectAfterEraseOne keep [] = refl
  selectAfterEraseOne keep ((key , value) ∷ rows) with keep key value in decision
  ... | true rewrite decision = cong ((key , value) ∷_) (selectAfterEraseOne keep rows)
  ... | false = refl

  eraseOneSelected : ∀ keep rows → eraseOne keep (select keep rows) ≡ select keep rows
  eraseOneSelected keep [] = refl
  eraseOneSelected keep ((key , value) ∷ rows) with keep key value in decision
  ... | true rewrite decision = cong ((key , value) ∷_) (eraseOneSelected keep rows)
  ... | false = eraseOneSelected keep rows

  selectKeeps : ∀ keep rows key value → (key , value) ∈ rows →
    keep key value ≡ true → (key , value) ∈ select keep rows
  selectKeeps keep ((key , value) ∷ rows) key value (here refl) kept
    with keep key value | kept
  ... | true | refl = here refl
  selectKeeps keep ((other , stored) ∷ rows) key value (there present) kept
    with keep other stored
  ... | true = there (selectKeeps keep rows key value present kept)
  ... | false = selectKeeps keep rows key value present kept

  selectedNeeded : ∀ keep rows key value → (key , value) ∈ select keep rows →
    keep key value ≡ true
  selectedNeeded keep ((other , stored) ∷ rows) key value present
    with keep other stored in decision
  ... | true with present
  ...   | here refl = decision
  ...   | there rest = selectedNeeded keep rows key value rest
  selectedNeeded keep ((other , stored) ∷ rows) key value present | false =
    selectedNeeded keep rows key value present

  -- All reads see the tentative transaction state. Only commit exposes writes;
  -- abort discards the complete tentative state, including earlier statements.
  data Transaction (A : Set) : Set where
    commit : A → Transaction A
    abort : A → Transaction A
    scan : (Rows → Transaction A) → Transaction A
    eraseRows : ℕ → Predicate → Transaction A → Transaction A
    read : Key → (Maybe Value → Transaction A) → Transaction A
    put : Key → Value → Transaction A → Transaction A
    remove : Key → Transaction A → Transaction A

  data Evaluation (A : Set) : Set where
    committed : A → Rows → Evaluation A
    aborted : A → Evaluation A

  evaluate : ∀ {A} → Transaction A → Rows → Evaluation A
  evaluate (commit result) rows = committed result rows
  evaluate (abort result) rows = aborted result
  evaluate (scan next) rows = evaluate (next rows) rows
  evaluate (eraseRows bound keep next) rows = evaluate next (erase bound keep rows)
  evaluate (read key next) rows = evaluate (next (lookup key rows)) rows
  evaluate (put key value next) rows = evaluate next (write key value rows)
  evaluate (remove key next) rows = evaluate next (delete key rows)

  reply : ∀ {A} → Evaluation A → A
  reply (committed result rows) = result
  reply (aborted result) = result

  publish : ∀ {A} → Rows → Evaluation A → Rows
  publish original (committed result rows) = rows
  publish original (aborted result) = original

  execute : ∀ {A} → Transaction A → Rows → A × Rows
  execute transaction original =
    reply (evaluate transaction original) , publish original (evaluate transaction original)

  abortKeepsStore : ∀ {A} (transaction : Transaction A) original result →
    evaluate transaction original ≡ aborted result →
    proj₂ (execute transaction original) ≡ original
  abortKeepsStore transaction original result abortedHere rewrite abortedHere = refl

  removeCommitDeletes : ∀ {A} key (result : A) rows →
    lookup key (proj₂ (execute (remove key (commit result)) rows)) ≡ nothing
  removeCommitDeletes key result rows = deleteAbsent key rows
