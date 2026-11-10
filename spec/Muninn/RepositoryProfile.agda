{-# OPTIONS --safe #-}
-- One resolved repository profile is used for both source and curated notes.
module Muninn.RepositoryProfile where
import Muninn.OwnedState as O
import Muninn.StoredPolicy as Policy
import Muninn.Config as C
import Muninn.Embeddings as B
import Muninn.Worktree as W
import Muninn.VectorData as V
import Muninn.ArtifactIdentity as Equal
import Muninn.ContentViews as Views
import Muninn.ExclusionOutcomes as E
open import Data.Nat using (ℕ)
open import Data.String using (String)
import Data.String as String
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
module DB = O.DB

backendName : B.EmbeddingBackend → String
backendName B.Voyage = "voyage"
backendName B.OpenAI = "openai"
backendName B.Local = "local"

-- Hosted providers require a named model. The local provider has a bundled
-- model, as in the existing provider/configuration contract.
Model : C.EmbeddingSelection → String → Set
Model selection actual with C.EmbeddingSelection.backend selection
... | B.Local = actual ≡ "minishlab/potion-base-32M"
... | B.Voyage with C.EmbeddingSelection.model selection
...   | nothing = ⊥
...   | just requested = actual ≡ requested
Model selection actual | B.OpenAI with C.EmbeddingSelection.model selection
... | nothing = ⊥
... | just requested = actual ≡ requested

-- The provider adapter resolves versioned normalization/task/configuration
-- fields, but cannot substitute a global backend/model/dimension.
record Resolved (selection : C.EmbeddingSelection) : Set where
  field key : W.EmbeddingKey
        backend : W.EmbeddingKey.backend key ≡ backendName (C.EmbeddingSelection.backend selection)
        model : Model selection (W.EmbeddingKey.model key)
        dimension : W.EmbeddingKey.dimension key ≡ B.EmbeddingDimension (C.EmbeddingSelection.backend selection)

module Family (family pointer : ℕ) where
  module Saved = Policy.Family family pointer
  owner = O.family family
  record Active (world : O.World) : Set where
    field current : Saved.Saved world
          resolved : Resolved (C.FamilyPolicy.embeddings (Saved.policy current))
  key : ∀ {world} → Active world → W.EmbeddingKey
  key active = Resolved.key (Active.resolved active)
  codeKey noteKey : ∀ {world} → Active world → W.EmbeddingKey
  codeKey = key
  noteKey = key
  notesUseRepositoryProfile : ∀ world (active : Active world) → noteKey active ≡ codeKey active
  notesUseRepositoryProfile world active = refl

  module Using (world : O.World) (active : Active world) where
    expected = key active
    matches : String → O.Owner → V.State → Maybe V.Value
    matches text actualOwner (V.usable saved) with E.ownerEqual actualOwner owner
    ... | no different = nothing
    ... | yes sameOwner with Equal.EmbeddingKey? (V.Value.profile saved) expected
    ...   | no different = nothing
    ...   | yes sameProfile with V.Value.source saved String.≟ text
    ...     | no different = nothing
    ...     | yes sameText = just saved
    matches text actualOwner state = nothing

    matchesSound : ∀ text actualOwner state saved → matches text actualOwner state ≡ just saved →
      V.Value.profile saved ≡ expected × V.Value.source saved ≡ text
    matchesSound text actualOwner (V.usable stored) saved found with E.ownerEqual actualOwner owner
    ... | no different with found
    ...   | ()
    matchesSound text actualOwner (V.usable stored) saved found | yes sameOwner with Equal.EmbeddingKey? (V.Value.profile stored) expected
    ... | no different with found
    ...   | ()
    matchesSound text actualOwner (V.usable stored) saved found | yes sameOwner | yes sameProfile with V.Value.source stored String.≟ text
    ... | no different with found
    ...   | ()
    matchesSound text actualOwner (V.usable stored) saved found | yes sameOwner | yes sameProfile | yes sameText with found
    ...   | refl = sameProfile , sameText

    -- Compatible values may be reused across code and note associations.
    completed : String → O.Record → Maybe V.Value
    completed text (O.recordOf actualOwner (O.vector chunk state)) = matches text actualOwner state
    completed text (O.recordOf actualOwner (O.noteVector note state)) = matches text actualOwner state
    completed text row = nothing
    completedSound : ∀ text row saved → completed text row ≡ just saved → V.Value.profile saved ≡ expected × V.Value.source saved ≡ text
    completedSound text (O.recordOf actualOwner (O.vector chunk state)) saved found = matchesSound text actualOwner state saved found
    completedSound text (O.recordOf actualOwner (O.noteVector note state)) saved found = matchesSound text actualOwner state saved found
    cache : String → Maybe V.Value
    cache text = Views.find (completed text) world
    cacheSound : ∀ text saved → cache text ≡ just saved → V.Value.profile saved ≡ expected × V.Value.source saved ≡ text
    cacheSound text saved found with Views.findSound (completed text) world saved found
    ... | row , present , selected = completedSound text (proj₂ row) saved selected

    data Action (text : String) : Set where
      reuse : (saved : V.Value) → cache text ≡ just saved → Action text
      embed : cache text ≡ nothing → Action text
    next : ∀ text → Action text
    next text with cache text in found
    ... | just saved = reuse saved found
    ... | nothing = embed found
    callsProvider : ∀ {text} → Action text → Bool
    callsProvider (reuse saved found) = false
    callsProvider (embed absent) = true
    noRepeatedCalculation : ∀ text saved → cache text ≡ just saved → (action : Action text) → callsProvider action ≡ false
    noRepeatedCalculation text saved found (reuse stored present) = refl
    noRepeatedCalculation text saved found (embed absent) with trans (sym found) absent
    ... | ()

    -- Semantic use requires a saved note association as well as the real note
    -- text and the actual current repository profile. Stale callbacks cannot
    -- manufacture this certificate merely from a provider response.
    record NoteUsable (note : ℕ) : Set where
      field text : String
            noteAt : DB.lookup note world ≡ just (O.recordOf owner (O.note text))
            slot : ℕ
            value : V.Value
            vectorAt : DB.lookup slot world ≡ just (O.recordOf owner (O.noteVector note (V.usable value)))
            compatible : V.Value.profile value ≡ expected
            source : V.Value.source value ≡ text
    noteValid : ∀ note → (usable : NoteUsable note) → V.Valid (W.EmbeddingKey.dimension expected) (V.Value.values (NoteUsable.value usable))
    noteValid note usable = subst (λ profile → V.Valid (W.EmbeddingKey.dimension profile) (V.Value.values (NoteUsable.value usable)))
      (NoteUsable.compatible usable) (V.Value.valid (NoteUsable.value usable))
    incompatibleNoteCannotBeUsed : ∀ note (usable : NoteUsable note) → V.Value.profile (NoteUsable.value usable) ≢ expected → ⊥
    incompatibleNoteCannotBeUsed note usable different = different (NoteUsable.compatible usable)
