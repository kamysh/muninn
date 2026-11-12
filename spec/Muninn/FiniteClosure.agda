{-# OPTIONS --safe #-}
-- Exact finite saturation. The recursion budget is justified by the remaining
-- universe, not a cutoff at which reachable nodes may be reported absent.
module Muninn.FiniteClosure where

open import Data.Nat using (ℕ; zero; suc; _≟_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

member : ∀ key keys → Dec (key ∈ keys)
member key [] = no (λ ())
member key (first ∷ rest) with key ≟ first
... | yes same = yes (here same)
... | no different with member key rest
...   | yes later = yes (there later)
...   | no absent = no (λ { (here same) → different same; (there later) → absent later })

choose : ∀ {A : Set} (P : A → Set) → (∀ key → Dec (P key)) → (keys : List A) →
  Dec (Σ A (λ key → key ∈ keys × P key))
choose P decide [] = no (λ { (_ , () , _) })
choose P decide (key ∷ keys) with decide key
... | yes proof = yes (key , here refl , proof)
... | no denied with choose P decide keys
...   | yes (other , present , proof) = yes (other , there present , proof)
...   | no none = no (λ { (_ , here refl , proof) → denied proof
                       ; (other , there present , proof) → none (other , present , proof) })

drop : ℕ → List ℕ → List ℕ
drop key [] = []
drop key (first ∷ rest) with key ≟ first
... | yes _ = drop key rest
... | no _ = first ∷ drop key rest

dropBound : ∀ key keys → length (drop key keys) ≤ length keys
dropBound key [] = z≤n
dropBound key (first ∷ rest) with key ≟ first
... | yes _ = ≤-trans (dropBound key rest) (Data.Nat.Properties.n≤1+n (length rest))
... | no _ = s≤s (dropBound key rest)

dropStrict : ∀ key keys → key ∈ keys → suc (length (drop key keys)) ≤ length keys
dropStrict key (first ∷ rest) present with key ≟ first
... | yes _ = s≤s (dropBound key rest)
... | no different with present
...   | here same = ⊥-elim (different same)
...   | there later = s≤s (dropStrict key rest later)

dropCover : ∀ removed keys key → key ∈ keys → key ∈ drop removed keys ⊎ key ≡ removed
dropCover removed (first ∷ rest) key present with removed ≟ first
... | yes refl with present
...   | here refl = inj₂ refl
...   | there later = dropCover removed rest key later
dropCover removed (first ∷ rest) key present | no different with present
... | here refl = inj₁ (here refl)
... | there later with dropCover removed rest key later
...   | inj₁ retained = inj₁ (there retained)
...   | inj₂ same = inj₂ same

module Closure (Seed : ℕ → Set) (Edge : ℕ → ℕ → Set)
  (seed? : ∀ key → Dec (Seed key)) (edge? : ∀ source target → Dec (Edge source target))
  (universe : List ℕ)
  (seedIn : ∀ {key} → Seed key → key ∈ universe)
  (targetIn : ∀ {source target} → Edge source target → target ∈ universe) where

  data Reach : ℕ → Set where
    root : ∀ {key} → Seed key → Reach key
    step : ∀ {source target} → Reach source → Edge source target → Reach target

  Enabled : List ℕ → ℕ → Set
  Enabled known key = Seed key ⊎ Σ ℕ (λ source → source ∈ known × Edge source key)

  enabled? : ∀ known key → Dec (Enabled known key)
  enabled? known key with seed? key
  ... | yes seed = yes (inj₁ seed)
  ... | no notSeed with choose (λ source → Edge source key) (λ source → edge? source key) known
  ...   | yes incoming = yes (inj₂ incoming)
  ...   | no none = no (λ { (inj₁ seed) → notSeed seed; (inj₂ incoming) → none incoming })

  record Saturated : Set where
    field known : List ℕ
          sound : ∀ {key} → key ∈ known → Reach key
          seeds : ∀ {key} → Seed key → key ∈ known
          closed : ∀ {source target} → source ∈ known → Edge source target → target ∈ known

  Cover : List ℕ → List ℕ → Set
  Cover remaining known = ∀ {key} → key ∈ universe → key ∈ remaining ⊎ key ∈ known

  finish : ∀ remaining known → Cover remaining known →
    (∀ {key} → key ∈ known → Reach key) →
    ¬ (Σ ℕ (λ key → key ∈ remaining × Enabled known key)) → Saturated
  finish remaining known cover sound none = record
    { known = known; sound = sound
    ; seeds = λ seed → admitted (seedIn seed) (inj₁ seed)
    ; closed = λ present edge → admitted (targetIn edge) (inj₂ (_ , present , edge)) }
    where
    admitted : ∀ {key} → key ∈ universe → Enabled known key → key ∈ known
    admitted present enabled with cover present
    ... | inj₁ pending = ⊥-elim (none (_ , pending , enabled))
    ... | inj₂ included = included

  addCover : ∀ remaining known key → Cover remaining known → Cover (drop key remaining) (key ∷ known)
  addCover remaining known key cover present with cover present
  ... | inj₂ included = inj₂ (there included)
  ... | inj₁ pending with dropCover key remaining _ pending
  ...   | inj₁ retained = inj₁ retained
  ...   | inj₂ same = inj₂ (here same)

  enabledSound : ∀ known key → (∀ {k} → k ∈ known → Reach k) → Enabled known key → Reach key
  enabledSound known key sound (inj₁ seed) = root seed
  enabledSound known key sound (inj₂ (source , present , edge)) = step (sound present) edge

  -- Every successful recursive call removes at least one remaining identity.
  -- At zero, the size proof rules out any unexamined record.
  grow : ∀ capacity remaining known → length remaining ≤ capacity → Cover remaining known →
    (∀ {key} → key ∈ known → Reach key) → Saturated
  grow zero [] known bound cover sound = finish [] known cover sound (λ { (_ , () , _) })
  grow (suc capacity) remaining known bound cover sound with choose (Enabled known) (enabled? known) remaining
  ... | no none = finish remaining known cover sound none
  ... | yes (key , present , enabled) = grow capacity (drop key remaining) (key ∷ known)
    (shrink (≤-trans (dropStrict key remaining present) bound))
    (addCover remaining known key cover)
    (λ { (here refl) → enabledSound known key sound enabled; (there earlier) → sound earlier })
    where
    shrink : ∀ {a b} → suc a ≤ suc b → a ≤ b
    shrink (s≤s proof) = proof

  saturation : Saturated
  saturation = grow (length universe) universe [] ≤-refl (λ present → inj₁ present) (λ ())

  complete : ∀ {key} → Reach key → key ∈ Saturated.known saturation
  complete (root seed) = Saturated.seeds saturation seed
  complete (step previous edge) = Saturated.closed saturation (complete previous) edge

  decide : ∀ key → Dec (Reach key)
  decide key with member key (Saturated.known saturation)
  ... | yes present = yes (Saturated.sound saturation present)
  ... | no absent = no (λ reachable → absent (complete reachable))
