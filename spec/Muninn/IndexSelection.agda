{-# OPTIONS --safe #-}
-- One concrete selection meaning builds index entries and gates saved bindings.
module Muninn.IndexSelection where

import Muninn.GitIgnore as Git
import Muninn.AdmittedSelection as A
import Muninn.OrderedSelection as Ordered
import Muninn.ExclusionOutcomes as E
import Muninn.OwnedState as O
import Muninn.Config as C
import Muninn.Worktree as W
open import Muninn.Types using (Tier; Tier1; Tier2)
open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (Σ; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
module M = E.Model

decision : Tier → C.Decision
decision Tier1 = C.T1
decision Tier2 = C.T2

keptTier : ∀ tier → Ordered.included (decision tier) ≡ true
keptTier Tier1 = refl
keptTier Tier2 = refl

agreement : ∀ family policy (valid : A.FamilyEntries policy) gitDefault path →
  M.includedWithGit (E.fromStoredPolicy family policy valid) (O.family family) gitDefault path ≡
  Ordered.included (A.classify policy valid gitDefault path false)
agreement family policy valid gitDefault path with E.ownerEqual (O.family family) (O.family family)
... | yes same = sym (Ordered.inclusion _ _)
... | no different = ⊥-elim (different refl)

module Checkout (family selected generation : ℕ) where
  current = Git.context family selected generation

  record File (policy : C.FamilyPolicy) (path : String) : Set where
    constructor file
    field validPolicy : A.FamilyEntries policy
          answer : Git.Answer path
          fresh : current ≡ Git.at answer
          tier : Tier
          selectedByPolicy : A.classify policy validPolicy (Git.ignored answer) path false ≡ decision tier

  data Choice (policy : C.FamilyPolicy) (valid : A.FamilyEntries policy) (path : String) (answer : Git.Answer path) : Set where
    omit : current ≡ Git.at answer → A.classify policy valid (Git.ignored answer) path false ≡ C.Drop → Choice policy valid path answer
    keep : (source : File policy path) → File.answer source ≡ answer → Choice policy valid path answer

  prepare : ∀ policy valid path answer → current ≡ Git.at answer → Choice policy valid path answer
  prepare policy valid path answer fresh with A.classify policy valid (Git.ignored answer) path false in observed
  ... | C.Drop = omit fresh observed
  ... | C.T1 = keep (file valid answer fresh Tier1 observed) refl
  ... | C.T2 = keep (file valid answer fresh Tier2 observed) refl

  fromReply : ∀ policy valid request → Git.Reply request → ∀ {path} → path ∈ Git.Query.paths request →
    Maybe (Σ (Git.Answer path) (Choice policy valid path))
  fromReply policy valid request response requested with Git.accept current request response requested in accepted
  ... | nothing = nothing
  ... | just answer = just (answer , prepare policy valid _ answer (Git.acceptedFresh current request response requested answer accepted))

  chosenFresh : ∀ {policy valid path answer} → Choice policy valid path answer → current ≡ Git.at answer
  chosenFresh (omit fresh omitted) = fresh
  chosenFresh (keep source refl) = File.fresh source

  entry : ∀ {policy path} → File policy path → (version : W.VersionRef) → W.VersionRef.family version ≡ C.FamilyPolicy.family policy → W.FileEntry
  entry source version belongs = record
    { version = version; tier = File.tier source; gitDefault = Git.ignored (File.answer source) }

  baseBody : ∀ {policy path} → ℕ → File policy path → O.Body
  baseBody {path = path} version source = O.baseBinding version path (File.answer source)

  deltaBody : ∀ {policy path} → ℕ → File policy path → O.Body
  deltaBody {path = path} version source = O.deltaBinding selected (just version) path (File.answer source)

  basePlaced : ∀ {policy path} version (source : File policy path) → O.Placed (O.recordOf (O.family family) (baseBody version source))
  basePlaced version source = O.local , cong Git.Context.family (sym (File.fresh source))

  deltaPlaced : ∀ {policy path} version (source : File policy path) → O.Placed (O.recordOf (O.family family) (deltaBody version source))
  deltaPlaced version source = O.local , cong Git.Context.family (sym (File.fresh source))

  -- Moving an existing base entry preserves its real Git observation.
  preservedDeltaPlaced : ∀ {path} owner selected version (answer : Git.Answer path) →
    O.Placed (O.recordOf owner (O.baseBinding version path answer)) →
    O.Placed (O.recordOf owner (O.deltaBinding selected (just version) path answer))
  preservedDeltaPlaced owner selected version answer placed = placed

  selectedGate : ∀ {policy path} (source : File policy path) →
    M.includedWithGit (E.fromStoredPolicy family policy (File.validPolicy source)) (O.family family)
      (Git.ignored (File.answer source)) path ≡ true
  selectedGate {policy} {path} source = trans
    (agreement family policy (File.validPolicy source) (Git.ignored (File.answer source)) path)
    (trans (cong Ordered.included (File.selectedByPolicy source)) (keptTier (File.tier source)))

  selectedBinding : ∀ {policy path} version (source : File policy path) →
    M.bindingSelected (E.fromStoredPolicy family policy (File.validPolicy source))
      (O.recordOf (O.family family) (deltaBody version source)) ≡ true
  selectedBinding version source = selectedGate source

  currentPolicy : ∀ {oldPolicy path} version (source : File oldPolicy path) policy (valid : A.FamilyEntries policy) →
    M.bindingSelected (E.fromStoredPolicy family policy valid) (O.recordOf (O.family family) (deltaBody version source)) ≡
      Ordered.included (A.classify policy valid (Git.ignored (File.answer source)) path false)
  currentPolicy {path = path} version source policy valid = agreement family policy valid (Git.ignored (File.answer source)) path
