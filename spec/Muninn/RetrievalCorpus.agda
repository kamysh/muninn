{-# OPTIONS --safe #-}
-- Complete eligible candidates and semantic coverage from the actual world.
module Muninn.RetrievalCorpus where
import Muninn.OwnedState as O
import Muninn.SearchView as View
import Muninn.StoredPolicy as Policy
import Muninn.ContentViews as Content
import Muninn.PublishedViews as Published
import Muninn.StagedVectors as Vectors
import Muninn.VectorData as V
import Muninn.Worktree as W
import Muninn.RetrievalNumerics as Numeric
import Muninn.Types as T
import Muninn.RepositoryProfile as Profile
import Muninn.Config as Config
open import Data.Nat using (ℕ; suc; _≤_; _≟_)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Bool using (Bool; true; false; _∧_)
import Data.String as String
open import Relation.Nullary using (does)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

module Family (family checkout pointer : ℕ) (world : O.World)
  (policy : Policy.Family.Saved family pointer world)
  (viewsValid : Published.Valid world)
  (filesValid : Content.Family.WellFormed (Policy.Family.rule family pointer policy) world)
  (view : View.Family.Stored family checkout world)
  (resolved : Profile.Resolved (Config.FamilyPolicy.embeddings (Policy.Family.policy family pointer policy))) where
  profile = Profile.Resolved.key resolved
  module Eligible = View.Family.ForPolicy.Current family checkout pointer world policy viewsValid filesValid view
  module Vector = Vectors.Family (Policy.Family.rule family pointer policy) profile
  Hit = Eligible.CodeHit
  Identity = T.FilePath × ℕ
  identity : Hit → Identity
  identity hit = Eligible.CodeHit.path hit , Eligible.CodeHit.key hit
  same : Hit → Hit → Bool
  same first second = does (Eligible.CodeHit.key first ≟ Eligible.CodeHit.key second) ∧
    does (T.FilePath.value (Eligible.CodeHit.path first) String.≟ T.FilePath.value (Eligible.CodeHit.path second))
  count : Hit → List Hit → ℕ
  count hit [] = 0
  count hit (first ∷ rest) with same hit first
  ... | true = suc (count hit rest)
  ... | false = count hit rest

  -- Source enumeration cannot be a top-N SQL result or handler-selected subset.
  -- Every actual eligible chunk/path pair must have a representative.
  record Inventory : Set where
    field items : List Hit
          complete : ∀ hit → Σ Hit (λ saved → saved ∈ items × identity saved ≡ identity hit)
          unique : ∀ hit → count hit items ≤ 1

  state : Hit → Vectors.Availability
  state hit = Vector.availability world (Eligible.CodeHit.key hit) (Eligible.CodeHit.text hit)
  report : Inventory → List (Identity × Vectors.Availability)
  report inventory = map (λ hit → identity hit , state hit) (Inventory.items inventory)

  countState : Vectors.Availability → List Hit → ℕ
  countState wanted [] = 0
  countState Vectors.usable (hit ∷ rest) with state hit
  ... | Vectors.usable = Data.Nat.suc (countState Vectors.usable rest)
  ... | _ = countState Vectors.usable rest
  countState Vectors.pending (hit ∷ rest) with state hit
  ... | Vectors.pending = Data.Nat.suc (countState Vectors.pending rest)
  ... | _ = countState Vectors.pending rest
  countState Vectors.waiting (hit ∷ rest) with state hit
  ... | Vectors.waiting = Data.Nat.suc (countState Vectors.waiting rest)
  ... | _ = countState Vectors.waiting rest
  allReady : List Hit → Bool
  allReady [] = true
  allReady (hit ∷ rest) with state hit
  ... | Vectors.usable = allReady rest
  ... | _ = false
  -- The wire response carries bounded-size counts, not the internal full list.
  record Summary (inventory : Inventory) : Set where
    field total usable pending waiting : ℕ
          complete : Bool
          totalCorrect : total ≡ length (Inventory.items inventory)
          usableCorrect : usable ≡ countState Vectors.usable (Inventory.items inventory)
          pendingCorrect : pending ≡ countState Vectors.pending (Inventory.items inventory)
          waitingCorrect : waiting ≡ countState Vectors.waiting (Inventory.items inventory)
          completenessCorrect : complete ≡ allReady (Inventory.items inventory)
  summary : (inventory : Inventory) → Summary inventory
  summary inventory = record
    { total = length (Inventory.items inventory); usable = countState Vectors.usable (Inventory.items inventory)
    ; pending = countState Vectors.pending (Inventory.items inventory); waiting = countState Vectors.waiting (Inventory.items inventory)
    ; complete = allReady (Inventory.items inventory)
    ; totalCorrect = refl; usableCorrect = refl; pendingCorrect = refl; waitingCorrect = refl; completenessCorrect = refl }
  allReadySound : ∀ rows hit → allReady rows ≡ true → hit ∈ rows → state hit ≡ Vectors.usable
  allReadySound (first ∷ rest) hit complete member with state first in observed
  ... | Vectors.usable with member
  ...   | here refl = observed
  ...   | there later = allReadySound rest hit complete later
  allReadySound (first ∷ rest) hit () member | Vectors.pending
  allReadySound (first ∷ rest) hit () member | Vectors.waiting
  completeMeansActualCoverage : ∀ inventory (saved : Summary inventory) → Summary.complete saved ≡ true →
    ∀ hit → hit ∈ Inventory.items inventory → state hit ≡ Vectors.usable
  completeMeansActualCoverage inventory saved claimed hit member = allReadySound (Inventory.items inventory) hit
    (trans (sym (Summary.completenessCorrect saved)) claimed) member

  mapMember : ∀ {A B : Set} (f : A → B) xs x → x ∈ xs → f x ∈ map f xs
  mapMember f (x ∷ xs) .x (here refl) = here refl
  mapMember f (first ∷ xs) x (there later) = there (mapMember f xs x later)
  everyEligibleIdentityReported : ∀ inventory hit →
    Σ Hit (λ saved → identity saved ≡ identity hit × (identity saved , state saved) ∈ report inventory)
  everyEligibleIdentityReported inventory hit with Inventory.complete inventory hit
  ... | saved , included , same = saved , same , mapMember (λ hit → identity hit , state hit) (Inventory.items inventory) saved included

  record Semantic (hit : Hit) : Set where
    field value : V.Value
          associated : Vector.linkedReady world (Eligible.CodeHit.key hit) (Eligible.CodeHit.text hit) ≡ just value
          stored32 : Numeric.Stored32 (V.Value.values value)
  validVector : ∀ hit → (ready : Semantic hit) → V.Valid (W.EmbeddingKey.dimension profile) (V.Value.values (Semantic.value ready))
  validVector hit ready = Vector.linkedReadyValid world (Eligible.CodeHit.key hit) (Eligible.CodeHit.text hit) (Semantic.value ready) (Semantic.associated ready)

  -- Missing vectors stay in the complete text inventory and coverage report.
  -- A successful semantic response must enumerate/classify the entire inventory.
  data Coverage (hit : Hit) : Set where
    ready : Semantic hit → Coverage hit
    unfinished : Vector.linkedReady world (Eligible.CodeHit.key hit) (Eligible.CodeHit.text hit) ≡ nothing → Coverage hit
  record SemanticInventory (inventory : Inventory) : Set where
    field classify : ∀ hit → hit ∈ Inventory.items inventory → Coverage hit
  unfinishedCannotHideUsable : ∀ hit → Vector.linkedReady world (Eligible.CodeHit.key hit) (Eligible.CodeHit.text hit) ≡ nothing → Semantic hit → ⊥
  unfinishedCannotHideUsable hit absent usable with trans (sym absent) (Semantic.associated usable)
  ... | ()
