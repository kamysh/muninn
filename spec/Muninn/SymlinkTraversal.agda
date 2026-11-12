{-# OPTIONS --safe #-}
-- Resolve ordinary internal links from a finite filesystem observation.
-- Components denote normalized filesystem names. The adapter must establish
-- that path components and link targets match the filesystem observation.
module Muninn.SymlinkTraversal where

open import Data.Nat using (ℕ; _≟_; _<_)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

Path : Set
Path = List ℕ

path? : (first second : Path) → Dec (first ≡ second)
path? [] [] = yes refl
path? [] (_ ∷ _) = no λ ()
path? (_ ∷ _) [] = no λ ()
path? (first ∷ rest) (second ∷ later) with first ≟ second
... | no different = no λ { refl → different refl }
... | yes refl with path? rest later
...   | no different = no λ { refl → different refl }
...   | yes refl = yes refl

data Prefix : Path → Path → Set where
  empty : ∀ {path} → Prefix [] path
  next : ∀ {name prefix path} → Prefix prefix path → Prefix (name ∷ prefix) (name ∷ path)

prefix? : (prefix path : Path) → Dec (Prefix prefix path)
prefix? [] path = yes empty
prefix? (_ ∷ _) [] = no λ ()
prefix? (first ∷ rest) (second ∷ later) with first ≟ second
... | no different = no λ { (next proof) → different refl }
... | yes refl with prefix? rest later
...   | no absent = no λ { (next proof) → absent proof }
...   | yes proof = yes (next proof)

rooted : ∀ root suffix → Prefix root (root ++ suffix)
rooted [] suffix = empty
rooted (_ ∷ root) suffix = next (rooted root suffix)

-- Each observation associates a link with its normalized absolute target.
Link : Set
Link = Path × Path

findLink : Path → List Link → Maybe Path
findLink path [] = nothing
findLink path ((name , target) ∷ rest) with path? path name
... | yes _ = just target
... | no _ = findLink path rest

data Expansion : Set where
  unchanged : Expansion
  expanded : Path → Expansion

-- Check path components in order. Expanding an ancestor keeps the suffix.
firstLink : List Link → Path → Path → Expansion
firstLink links prefix [] with findLink prefix links
... | nothing = unchanged
... | just target = expanded target
firstLink links prefix (name ∷ rest) with findLink prefix links
... | just target = expanded (target ++ (name ∷ rest))
... | nothing = firstLink links (prefix ++ (name ∷ [])) rest

-- A finite resolution records the actual expansion at every step. Both the
-- displayed path and every intermediate target remain within the checkout.
data Resolution (root : Path) (links : List Link) : Path → Path → Set where
  done : ∀ {path} → Prefix root path → firstLink links [] path ≡ unchanged → Resolution root links path path
  step : ∀ {before after target} → Prefix root before →
    firstLink links [] before ≡ expanded after → Resolution root links after target → Resolution root links before target

-- Eligible observations provide a finite chain of ordinary expansions. Each
-- recursive step uses the next expansion from the same filesystem snapshot.
data Expands (root : Path) (links : List Link) : Path → Path → Set where
  expansion : ∀ {before after} → Prefix root before →
    firstLink links [] before ≡ expanded after → Prefix root after → Expands root links after before

-- A filesystem observation supplies link records and a decreasing measure
-- for ordinary internal expansions. The decrease is checked for every step;
-- correspondence to the actual filesystem is an adapter obligation.
record Snapshot (root : Path) : Set where
  field
    links : List Link
    remaining : Path → ℕ
    decreases : ∀ {before after} → Expands root links after before → remaining after < remaining before

accessible : ∀ {root} (snapshot : Snapshot root) path →
  Acc _<_ (Snapshot.remaining snapshot path) → Acc (Expands root (Snapshot.links snapshot)) path
accessible snapshot path (acc smaller) = acc λ transition →
  accessible snapshot _ (smaller (Snapshot.decreases snapshot transition))

finite : ∀ {root} (snapshot : Snapshot root) path → Acc (Expands root (Snapshot.links snapshot)) path
finite snapshot path = accessible snapshot path (<-wellFounded (Snapshot.remaining snapshot path))

-- Expanding the same path has one next path. This lets an excluded result
-- carry evidence that no valid in-root resolution was discarded.
unstep : ∀ {root links before after target} →
  firstLink links [] before ≡ expanded after → Resolution root links before target →
  Resolution root links after target
unstep expected (done inside unchangedPath) with trans (sym expected) unchangedPath
... | ()
unstep expected (step inside observed rest) with trans (sym expected) observed
... | refl = rest

startInside : ∀ {root links before target} → Resolution root links before target → Prefix root before
startInside (done inside unchangedPath) = inside
startInside (step inside expandedPath rest) = inside

insideRoot : ∀ {root links before target} → Resolution root links before target → Prefix root target
insideRoot (done inside unchangedPath) = inside
insideRoot (step inside expandedPath rest) = insideRoot rest

deterministic : ∀ {root links before first second} →
  Resolution root links before first → Resolution root links before second → first ≡ second
deterministic (done inside unchangedPath) (done inside₂ unchangedPath₂) = refl
deterministic (done inside unchangedPath) (step inside₂ observed rest) with trans (sym unchangedPath) observed
... | ()
deterministic (step inside observed rest) (done inside₂ unchangedPath) with trans (sym observed) unchangedPath
... | ()
deterministic (step inside observed rest) (step inside₂ observed₂ rest₂) with trans (sym observed) observed₂
... | refl = deterministic rest rest₂

data Result (root : Path) (links : List Link) (start : Path) : Set where
  selected : (target : Path) → Resolution root links start target → Result root links start
  excluded : (∀ target → ¬ Resolution root links start target) → Result root links start

resolve : ∀ root links start → Prefix root start → Acc (Expands root links) start → Result root links start
resolve root links start inside (acc smaller) with firstLink links [] start in observed
... | unchanged = selected start (done inside observed)
... | expanded after with prefix? root after
...   | no outside = excluded (λ target trace → outside (startInside (unstep {target = target} observed trace)))
...   | yes afterInside with resolve root links after afterInside (smaller (expansion inside observed afterInside))
...     | excluded noTarget = excluded (λ target trace → noTarget target (unstep {target = target} observed trace))
...     | selected target trace = selected target (step inside observed trace)

-- A supplied resolution is finite: recursion consumes one recorded step.
steps : ∀ {root links before target} → Resolution root links before target → ℕ
steps (done inside unchangedPath) = 0
steps (step inside expandedPath rest) = Data.Nat.suc (steps rest)

-- Every finite, in-root resolution is returned by the resolver.
complete : ∀ root links before target (inside : Prefix root before)
  (accessible : Acc (Expands root links) before) → Resolution root links before target →
  Σ (Resolution root links before target) (λ actual → resolve root links before inside accessible ≡ selected target actual)
complete root links before target inside accessible trace with resolve root links before inside accessible
... | excluded noTarget = ⊥-elim (noTarget target trace)
... | selected actual actualTrace with deterministic trace actualTrace
...   | refl = actualTrace , refl
