{-# OPTIONS --safe #-}
-- Logical file views read from actual owned binding rows, not handler goals.
module Muninn.ContentViews where

import Muninn.OwnedState as O
import Muninn.ExclusionOutcomes as E
import Muninn.GenericFileMap as Maps
import Muninn.GitIgnore as Git
import Muninn.Types as T
open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (Bool; true; false)
open import Data.String using (String)
import Data.String as String
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing; fromMaybe)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

-- These are the actual logical row addresses and saved Git defaults. Keeping
-- a version address also keeps the referenced immutable content/metadata.
record Entry : Set where
  constructor entry
  field version : ℕ
        gitDefault : Bool
module Files = Maps.For Entry

find : ∀ {A : Set} → (O.Record → Maybe A) → O.World → Maybe A
find select [] = nothing
find select ((key , value) ∷ rest) with select value
... | just chosen = just chosen
... | nothing = find select rest

findSound : ∀ {A : Set} (select : O.Record → Maybe A) world value → find select world ≡ just value →
  Σ (ℕ × O.Record) (λ row → row ∈ world × select (proj₂ row) ≡ just value)
findSound select [] value ()
findSound select ((key , stored) ∷ rest) value found with select stored in chosen
... | just result with just-injective found
...   | refl = (key , stored) , here refl , chosen
findSound select ((key , stored) ∷ rest) value found | nothing with findSound select rest value found
... | row , present , selected = row , there present , selected

findAbsent : ∀ {A : Set} (select : O.Record → Maybe A) world → find select world ≡ nothing →
  ∀ row → row ∈ world → select (proj₂ row) ≡ nothing
findAbsent select [] absent row ()
findAbsent select ((key , stored) ∷ rest) absent row present with select stored in chosen
... | just result with absent
...   | ()
findAbsent select ((key , stored) ∷ rest) absent .(key , stored) (here refl) | nothing = chosen
findAbsent select ((key , stored) ∷ rest) absent row (there present) | nothing = findAbsent select rest absent row present

Consistent : ∀ {A : Set} → (O.Record → Maybe A) → O.World → Set
Consistent select world = ∀ first second before after → first ∈ world → second ∈ world →
  select (proj₂ first) ≡ just before → select (proj₂ second) ≡ just after → before ≡ after

findComplete : ∀ {A : Set} (select : O.Record → Maybe A) world → Consistent select world →
  ∀ row value → row ∈ world → select (proj₂ row) ≡ just value → find select world ≡ just value
findComplete select world consistent row value present selected with find select world in found
... | nothing = ⊥-elim (impossible (trans (sym (findAbsent select world found row present)) selected))
  where impossible : nothing ≡ just value → ⊥
        impossible ()
... | just chosen with findSound select world chosen found
...   | other , included , same with consistent other row chosen value included present same selected
...     | refl = refl

module Family (selection : E.Rule) where
  module M = E.Model
  owner = E.targetOwner selection

  baseCell : T.FilePath → O.Record → Maybe Entry
  baseCell path (O.recordOf storedOwner (O.baseBinding version storedPath answer))
    with E.ownerEqual owner storedOwner | T.FilePath.value path String.≟ storedPath
  ... | yes same | yes refl = just (entry version (Git.ignored answer))
  ... | _ | _ = nothing
  baseCell path value = nothing

  deltaCell : ℕ → T.FilePath → O.Record → Maybe Files.Override
  deltaCell selected path (O.recordOf storedOwner (O.deltaBinding checkout version storedPath answer))
    with M.deltaValue owner selected (T.FilePath.value path) (O.recordOf storedOwner (O.deltaBinding checkout version storedPath answer))
  ... | false = nothing
  ... | true with version
  ...   | nothing = just Files.Deleted
  ...   | just version = just (Files.Changed (entry version (Git.ignored answer)))
  deltaCell selected path value = nothing

  base : O.World → Files.Manifest
  base world path = find (baseCell path) world

  overlay : O.World → ℕ → Files.Overlay
  overlay world selected path = fromMaybe Files.Inherit (find (deltaCell selected path) world)

  rawView : O.World → ℕ → Files.Manifest
  rawView world selected path = Files.applyOverride (base world path) (overlay world selected path)

  mask : T.FilePath → Maybe Entry → Maybe Entry
  mask path nothing = nothing
  mask path value@(just saved) with M.includedWithGit selection owner (Entry.gitDefault saved) (T.FilePath.value path)
  ... | true = value
  ... | false = nothing

  visible : O.World → ℕ → Files.Manifest
  visible world selected path = mask path (rawView world selected path)

  -- Every matching actual row agrees with the view; a projection cannot hide a
  -- second conflicting value. SQL key uniqueness is a stronger physical rule.
  record WellFormed (world : O.World) : Set where
    field bases : ∀ path → Consistent (baseCell path) world
          deltas : ∀ selected path → Consistent (deltaCell selected path) world

  baseSound : ∀ world path value → base world path ≡ just value →
    Σ (ℕ × O.Record) (λ row → row ∈ world × baseCell path (proj₂ row) ≡ just value)
  baseSound world path value = findSound (baseCell path) world value

  baseComplete : ∀ world → WellFormed world → ∀ path row value → row ∈ world →
    baseCell path (proj₂ row) ≡ just value → base world path ≡ just value
  baseComplete world valid path = findComplete (baseCell path) world (WellFormed.bases valid path)

  maskKeeps : ∀ path saved → M.includedWithGit selection owner (Entry.gitDefault saved) (T.FilePath.value path) ≡ true →
    mask path (just saved) ≡ just saved
  maskKeeps path saved included rewrite included = refl

  maskIdempotent : ∀ path value → mask path (mask path value) ≡ mask path value
  maskIdempotent path nothing = refl
  maskIdempotent path (just saved) with M.includedWithGit selection owner (Entry.gitDefault saved) (T.FilePath.value path) in included
  ... | true = maskKeeps path saved included
  ... | false = refl

  includedResult : ∀ path value saved → mask path value ≡ just saved →
    M.includedWithGit selection owner (Entry.gitDefault saved) (T.FilePath.value path) ≡ true
  includedResult path nothing saved ()
  includedResult path (just original) saved kept with M.includedWithGit selection owner (Entry.gitDefault original) (T.FilePath.value path) in included
  ... | true with just-injective kept
  ...   | refl = included
  includedResult path (just original) saved kept | false with kept
  ... | ()
