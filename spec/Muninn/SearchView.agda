{-# OPTIONS --safe #-}
-- A search uses one actual published checkout view, filtered by stored policy.
module Muninn.SearchView where
import Muninn.OwnedState as O
import Muninn.StoredPolicy as Policy
import Muninn.ContentViews as Content
import Muninn.ExclusionOutcomes as E
import Muninn.Types as T
import Muninn.PublishedViews as Published
open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (Bool; true; false)
open import Data.String using (String)
import Data.String as String
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Membership.DecPropositional
module Member = Data.List.Membership.DecPropositional _≟_
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe.Properties using (just-injective)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
module DB = O.DB

module Family (family selected : ℕ) where
  owner = O.family family

  record Stored (world : O.World) : Set where
    constructor stored
    field pointer root : ℕ
          nodes edges : List ℕ
          payload : String
          pointerAt : DB.lookup pointer world ≡ just (O.recordOf owner (O.publishedView selected root))
          snapshotAt : DB.lookup root world ≡ just (O.recordOf owner (O.structuralSnapshot selected nodes edges payload))

  snapshotValue : ∀ world pointer root → DB.lookup pointer world ≡ just (O.recordOf owner (O.publishedView selected root)) →
    (value : Maybe O.Record) → DB.lookup root world ≡ value → Maybe (Stored world)
  snapshotValue world pointer root pointerAt (just (O.recordOf actualOwner (O.structuralSnapshot checkout nodes edges payload))) snapshotAt
    with E.ownerEqual actualOwner owner | checkout ≟ selected
  ... | yes refl | yes refl = just (stored pointer root nodes edges payload pointerAt snapshotAt)
  ... | _ | _ = nothing
  snapshotValue world pointer root pointerAt value snapshotAt = nothing

  pointerValue : ∀ world pointer → (value : Maybe O.Record) → DB.lookup pointer world ≡ value → Maybe (Stored world)
  pointerValue world pointer (just (O.recordOf actualOwner (O.publishedView checkout root))) pointerAt
    with E.ownerEqual actualOwner owner | checkout ≟ selected
  ... | yes refl | yes refl = snapshotValue world pointer root pointerAt (DB.lookup root world) refl
  ... | _ | _ = nothing
  pointerValue world pointer value pointerAt = nothing

  scan : (world : O.World) → O.World → Maybe (Stored world)
  scan world [] = nothing
  scan world ((pointer , ignored) ∷ rows) with pointerValue world pointer (DB.lookup pointer world) refl
  ... | just current = just current
  ... | nothing = scan world rows
  observe : (world : O.World) → Maybe (Stored world)
  observe world = scan world world

  module ForPolicy (policyPointer : ℕ) where
    module StoredPolicy = Policy.Family family policyPointer
    module Current (world : O.World) (currentPolicy : StoredPolicy.Saved world) (viewsValid : Published.Valid world)
      (filesValid : Content.Family.WellFormed (StoredPolicy.rule currentPolicy) world) (view : Stored world) where
      selection = StoredPolicy.rule currentPolicy
      module Files = Content.Family selection

      record CodeHit : Set where
        constructor codeHit
        field path : T.FilePath
              key version : ℕ
              text : String
              gitDefault : Bool
              chunkAt : DB.lookup key world ≡ just (O.recordOf owner (O.chunk version text))
              fileAt : Files.visible world selected path ≡ just (Content.entry version gitDefault)

      record SymbolHit : Set where
        constructor symbolHit
        field path : T.FilePath
              key version : ℕ
              text : String
              gitDefault : Bool
              symbolAt : DB.lookup key world ≡ just (O.recordOf owner (O.symbol version (T.FilePath.value path) text))
              fileAt : Files.visible world selected path ≡ just (Content.entry version gitDefault)
              inSnapshot : key ∈ Stored.nodes view

      codeRow : ∀ path key → (value : Maybe O.Record) → DB.lookup key world ≡ value → Maybe CodeHit
      codeRow path key (just (O.recordOf actualOwner (O.chunk version text))) chunkAt with E.ownerEqual actualOwner owner
      ... | no other = nothing
      ... | yes refl with Files.visible world selected path in fileAt
      ...   | nothing = nothing
      ...   | just cell with Content.Entry.version cell ≟ version
      ...     | no other = nothing
      ...     | yes refl = just (codeHit path key version text (Content.Entry.gitDefault cell) chunkAt fileAt)
      codeRow path key value found = nothing
      code : T.FilePath → ℕ → Maybe CodeHit
      code path key = codeRow path key (DB.lookup key world) refl

      symbolRow : ∀ path key → (value : Maybe O.Record) → DB.lookup key world ≡ value → Maybe SymbolHit
      symbolRow path key (just (O.recordOf actualOwner (O.symbol version source text))) symbolAt
        with E.ownerEqual actualOwner owner | source String.≟ T.FilePath.value path | key Member.∈? Stored.nodes view
      ... | yes refl | yes refl | yes included with Files.visible world selected path in fileAt
      ...   | nothing = nothing
      ...   | just cell with Content.Entry.version cell ≟ version
      ...     | no other = nothing
      ...     | yes refl = just (symbolHit path key version text (Content.Entry.gitDefault cell) symbolAt fileAt included)
      symbolRow path key (just (O.recordOf actualOwner (O.symbol version source text))) symbolAt | _ | _ | _ = nothing
      symbolRow path key value found = nothing
      symbol : T.FilePath → ℕ → Maybe SymbolHit
      symbol path key = symbolRow path key (DB.lookup key world) refl

      codes : List (T.FilePath × ℕ) → List CodeHit
      codes [] = []
      codes ((path , key) ∷ candidates) with code path key
      ... | nothing = codes candidates
      ... | just hit = hit ∷ codes candidates
      symbols : List (T.FilePath × ℕ) → List SymbolHit
      symbols [] = []
      symbols ((path , key) ∷ candidates) with symbol path key
      ... | nothing = symbols candidates
      ... | just hit = hit ∷ symbols candidates

      codeIsEligible : ∀ (hit : CodeHit) → DB.lookup (CodeHit.key hit) world ≡ just (O.recordOf owner (O.chunk (CodeHit.version hit) (CodeHit.text hit))) ×
        Files.visible world selected (CodeHit.path hit) ≡ just (Content.entry (CodeHit.version hit) (CodeHit.gitDefault hit))
      codeIsEligible hit = CodeHit.chunkAt hit , CodeHit.fileAt hit
      symbolIsCurrent : ∀ (hit : SymbolHit) → SymbolHit.key hit ∈ Stored.nodes view
      symbolIsCurrent = SymbolHit.inSnapshot

      otherVersionExcluded : ∀ path cell (hit : CodeHit) → Files.visible world selected path ≡ just cell →
        CodeHit.path hit ≡ path → CodeHit.version hit ≢ Content.Entry.version cell → Data.Empty.⊥
      otherVersionExcluded path cell hit actual samePath different =
        different (sym (cong Content.Entry.version (just-injective (trans (sym actual) atPath))))
        where
        atPath : Files.visible world selected path ≡ just (Content.entry (CodeHit.version hit) (CodeHit.gitDefault hit))
        atPath = subst (λ selectedPath → Files.visible world selected selectedPath ≡ just (Content.entry (CodeHit.version hit) (CodeHit.gitDefault hit)))
          samePath (CodeHit.fileAt hit)
