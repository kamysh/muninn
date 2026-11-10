{-# OPTIONS --safe #-}
-- Finite atomic row removal preserves receipts and has a fixed whole-world outcome.
module Muninn.KnowledgeErase where
import Muninn.OwnedState as O
import Muninn.ReceiptLedger as Ledger
import Muninn.CleanupObservations as Observations
import Muninn.CleanupOrder as Order
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
module DB = O.DB

subsetOne : ∀ keep rows row → row ∈ DB.eraseOne keep rows → row ∈ rows
subsetOne keep [] row ()
subsetOne keep ((key , value) ∷ rows) row present with keep key value
... | false = there present
... | true with present
...   | here refl = here refl
...   | there later = there (subsetOne keep rows row later)
subset : ∀ count keep rows row → row ∈ DB.erase count keep rows → row ∈ rows
subset zero keep rows row present = present
subset (suc count) keep rows row present = subsetOne keep rows row (subset count keep (DB.eraseOne keep rows) row present)

retains : ∀ count keep rows key value → DB.lookup key rows ≡ just value → keep key value ≡ true →
  DB.lookup key (DB.erase count keep rows) ≡ just value
retains zero keep rows key value found kept = found
retains (suc count) keep rows key value found kept =
  retains count keep (DB.eraseOne keep rows) key value (DB.eraseRetainsLookup keep rows key value found kept) kept

frame : ∀ count keep world → O.Unique world →
  (∀ key owner receipt → keep key (O.recordOf owner (O.receipt receipt)) ≡ true) →
  Ledger.ReceiptFrame world (DB.erase count keep world)
frame count keep world unique keepReceipts key owner receipt =
  (λ found → retains count keep world key _ found (keepReceipts key owner receipt)) , backward
  where
  backward : DB.lookup key (DB.erase count keep world) ≡ just (O.recordOf owner (O.receipt receipt)) →
    DB.lookup key world ≡ just (O.recordOf owner (O.receipt receipt))
  backward found = Order.memberLookup world key _ unique
    (subset count keep world _ (Observations.lookupMember (DB.erase count keep world) key _ found))

extra : ∀ count keep rows → DB.erase (suc count) keep rows ≡ DB.eraseOne keep (DB.erase count keep rows)
extra zero keep rows = refl
extra (suc count) keep rows = extra count keep (DB.eraseOne keep rows)

keptPrefix : ∀ count keep key value rows → keep key value ≡ true →
  DB.erase count keep ((key , value) ∷ rows) ≡ (key , value) ∷ DB.erase count keep rows
keptPrefix zero keep key value rows kept = refl
keptPrefix (suc count) keep key value rows kept rewrite DB.eraseOneKept keep key value rows kept =
  keptPrefix count keep key value (DB.eraseOne keep rows) kept

allRows : ∀ keep rows → DB.erase (length rows) keep rows ≡ DB.select keep rows
allRows keep [] = refl
allRows keep ((key , value) ∷ rows) with keep key value in chosen
... | false = allRows keep rows
... | true = trans (keptPrefix (length rows) keep key value (DB.eraseOne keep rows) chosen)
  (cong ((key , value) ∷_) (trans (extra (length rows) keep rows)
    (trans (cong (DB.eraseOne keep) (allRows keep rows)) (DB.eraseOneSelected keep rows))))

removed : ∀ keep world key value → O.Unique world → DB.lookup key world ≡ just value → keep key value ≡ false →
  DB.lookup key (DB.erase (length world) keep world) ≡ nothing
removed keep world key value unique original dropped with DB.lookup key (DB.erase (length world) keep world) in found
... | nothing = refl
... | just actual = ⊥-elim (impossible (subst (λ row → keep key row ≡ true) (sym sameValue) selected))
  where
  member : (key , actual) ∈ DB.erase (length world) keep world
  member = Observations.lookupMember _ key actual found
  originalMember : (key , actual) ∈ world
  originalMember = subset (length world) keep world (key , actual) member
  sameValue : value ≡ actual
  sameValue = just-injective (trans (sym original) (Order.memberLookup world key actual unique originalMember))
  selected : keep key actual ≡ true
  selected = DB.selectedNeeded keep world key actual (subst (λ rows → (key , actual) ∈ rows) (allRows keep world) member)
  impossible : keep key value ≡ true → ⊥
  impossible kept with trans (sym dropped) kept
  ... | ()

selectedSubset : ∀ keep rows row → row ∈ DB.select keep rows → row ∈ rows
selectedSubset keep ((key , value) ∷ rows) row present with keep key value
... | false = there (selectedSubset keep rows row present)
... | true with present
...   | here refl = here refl
...   | there later = there (selectedSubset keep rows row later)
selectedSubset keep [] row ()

selectedAbsent : ∀ keep rows key → O.Unique rows → DB.lookup key rows ≡ nothing → DB.lookup key (DB.select keep rows) ≡ nothing
selectedAbsent keep rows key unique absent with DB.lookup key (DB.select keep rows) in found
... | nothing = refl
... | just value with trans (sym absent) (Order.memberLookup rows key value unique
    (selectedSubset keep rows (key , value) (Observations.lookupMember (DB.select keep rows) key value found)))
...   | ()

selectedUnique : ∀ keep rows → O.Unique rows → O.Unique (DB.select keep rows)
selectedUnique keep [] unique = unique
selectedUnique keep ((key , value) ∷ rows) (absent , unique) with keep key value
... | false = selectedUnique keep rows unique
... | true = selectedAbsent keep rows key unique absent , selectedUnique keep rows unique

afterUnique : ∀ keep world → O.Unique world → O.Unique (DB.erase (length world) keep world)
afterUnique keep world unique = subst O.Unique (sym (allRows keep world)) (selectedUnique keep world unique)

record Source (keep : DB.Predicate) (before : O.World) (key : ℕ) (value : O.Record) : Set where
  field found : DB.lookup key before ≡ just value
        retained : keep key value ≡ true
source : ∀ keep before key value → O.Unique before →
  DB.lookup key (DB.erase (length before) keep before) ≡ just value → Source keep before key value
source keep before key value unique found = record
  { found = Order.memberLookup before key value unique (subset (length before) keep before (key , value) member)
  ; retained = DB.selectedNeeded keep before key value (subst (λ rows → (key , value) ∈ rows) (allRows keep before) member) }
  where member : (key , value) ∈ DB.erase (length before) keep before
        member = Observations.lookupMember _ key value found
