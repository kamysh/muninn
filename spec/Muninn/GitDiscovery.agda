{-# OPTIONS --safe #-}
-- Git enumerates tracked and ordinary untracked candidates; explicit inclusions
-- additionally drive the ignored-directory walk.
module Muninn.GitDiscovery where

import Muninn.GitIgnore as Git
import Muninn.InclusionTraversal as Walk
import Muninn.OrderedSelection as O
import Muninn.RulePatterns as R
open import Data.String using (String)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Complete provider result for the cached + others + exclude-standard listing.
-- Tracked files remain candidates even beneath ignored directory names.
record Candidates (at : Git.Context) : Set where
  constructor candidates
  field paths : List String
        unique : Unique paths

data Job : Set where
  inspectFile inspectDirectory : String → Job

initial : ∀ {at} → Candidates at → List Job
initial listing = map inspectFile (Candidates.paths listing) ++ (inspectDirectory "" ∷ [])

listedScheduled : ∀ {at} (listing : Candidates at) path → path ∈ Candidates.paths listing → inspectFile path ∈ initial listing
listedScheduled listing path listed = ∈-++⁺ˡ (∈-map⁺ inspectFile listed)

rootScheduled : ∀ {at} (listing : Candidates at) → inspectDirectory "" ∈ initial listing
rootScheduled listing = ∈-++⁺ʳ (map inspectFile (Candidates.paths listing)) (here refl)

-- Git-visible candidates take the direct listing route. A selected ignored
-- candidate takes a directory route that cannot prune any required ancestor.
ignoredRoute : ∀ {inputs word actualDirectory} (rules : O.Rules inputs) directory →
  Walk.Prefix (directory ++ ('/' ∷ [])) word → O.resolve true rules word actualDirectory ≡ false →
  Walk.descend true rules directory ≡ true
ignoredRoute = Walk.reachesIncluded
