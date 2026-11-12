{-# OPTIONS --safe #-}
-- Changing a family embedding profile recreates derived data atomically.
module Muninn.ProfileRecreation where

import Muninn.KnowledgeState as Knowledge
import Muninn.Worktree as W
import Muninn.Policy as Policy
import Muninn.Config as Config
open import Muninn.Knowledge using (KnowledgeId)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Empty using (⊥-elim)

-- Ordinary policy updates retain the backend and model; profile change uses
-- the explicit recreation operation below.
ordinaryPolicyKeepsModel : ∀ before after → Policy.AdmissiblePolicyChange before after →
  (Config.EmbeddingSelection.backend (Config.FamilyPolicy.embeddings after) ≡
    Config.EmbeddingSelection.backend (Config.FamilyPolicy.embeddings (Policy.PolicyState.current before))) ×
  (Config.EmbeddingSelection.model (Config.FamilyPolicy.embeddings after) ≡
    Config.EmbeddingSelection.model (Config.FamilyPolicy.embeddings (Policy.PolicyState.current before)))
ordinaryPolicyKeepsModel before after permission =
  Policy.AdmissiblePolicyChange.sameBackend permission , Policy.AdmissiblePolicyChange.sameModel permission

module Model (Identity Settings Index : Set)
  (sameFamily : (a b : W.FamilyId) → Dec (a ≡ b))
  (sameNote : (a b : KnowledgeId) → Dec (a ≡ b))
  (sameProfile : (a b : W.EmbeddingKey) → Dec (a ≡ b)) where
  module Notes = Knowledge.Operations sameFamily sameNote

  record World : Set where
    constructor world
    field identity : W.FamilyId → Identity
          settings : W.FamilyId → Settings
          knowledge : Knowledge.World
          codeIndex : W.FamilyId → Maybe Index
          codeVectorProfile : W.FamilyId → Maybe W.EmbeddingKey

  clearAt : ∀ {A : Set} → W.FamilyId → (W.FamilyId → Maybe A) → W.FamilyId → Maybe A
  clearAt family contents selected with sameFamily family selected
  ... | yes _ = nothing
  ... | no _ = contents selected

  replace : W.FamilyId → W.EmbeddingKey → World → World
  replace family profile before = world
    (World.identity before) (World.settings before)
    (Notes.recreateProfile family profile (World.knowledge before))
    (clearAt family (World.codeIndex before))
    (clearAt family (World.codeVectorProfile before))

  -- A repeat of a completed profile change leaves subsequently rebuilt data
  -- intact. No failure-specific record is needed for an interrupted attempt.
  recreate : W.FamilyId → W.EmbeddingKey → World → World
  recreate family profile before with Knowledge.World.profile (World.knowledge before) family
  ... | nothing = replace family profile before
  ... | just existing with sameProfile existing profile
  ...   | yes _ = before
  ...   | no _ = replace family profile before

  selectedProfile : ∀ family profile before →
    Knowledge.World.profile (World.knowledge (recreate family profile before)) family ≡ just profile
  selectedProfile family profile before with Knowledge.World.profile (World.knowledge before) family in observed
  ... | nothing = Notes.recreateSetsProfile family profile (World.knowledge before)
  ... | just existing with sameProfile existing profile
  ...   | yes refl = observed
  ...   | no different = Notes.recreateSetsProfile family profile (World.knowledge before)

  alreadyCurrent : ∀ family profile before →
    Knowledge.World.profile (World.knowledge before) family ≡ just profile →
    recreate family profile before ≡ before
  alreadyCurrent family profile before current rewrite current with sameProfile profile profile
  ... | yes _ = refl
  ... | no different = ⊥-elim (different refl)

  retryAfterCompletion : ∀ family profile before →
    recreate family profile (recreate family profile before) ≡ recreate family profile before
  retryAfterCompletion family profile before =
    alreadyCurrent family profile (recreate family profile before) (selectedProfile family profile before)

  identityPreserved : ∀ family profile before selected →
    World.identity (recreate family profile before) selected ≡ World.identity before selected
  identityPreserved family profile before selected with Knowledge.World.profile (World.knowledge before) family
  ... | nothing = refl
  ... | just existing with sameProfile existing profile
  ...   | yes _ = refl
  ...   | no _ = refl

  settingsPreserved : ∀ family profile before selected →
    World.settings (recreate family profile before) selected ≡ World.settings before selected
  settingsPreserved family profile before selected with Knowledge.World.profile (World.knowledge before) family
  ... | nothing = refl
  ... | just existing with sameProfile existing profile
  ...   | yes _ = refl
  ...   | no _ = refl

  notesPreserved : ∀ family profile before selected id →
    Knowledge.World.notes (World.knowledge (recreate family profile before)) selected id ≡
    Knowledge.World.notes (World.knowledge before) selected id
  notesPreserved family profile before selected id with Knowledge.World.profile (World.knowledge before) family
  ... | nothing = refl
  ... | just existing with sameProfile existing profile
  ...   | yes _ = refl
  ...   | no _ = refl

  clearKeepsOther : ∀ {A : Set} family selected (contents : W.FamilyId → Maybe A) →
    ¬ (family ≡ selected) → clearAt family contents selected ≡ contents selected
  clearKeepsOther family selected contents different with sameFamily family selected
  ... | yes same = ⊥-elim (different same)
  ... | no _ = refl

  otherIndexPreserved : ∀ family profile before selected → ¬ (family ≡ selected) →
    World.codeIndex (recreate family profile before) selected ≡ World.codeIndex before selected
  otherIndexPreserved family profile before selected different with Knowledge.World.profile (World.knowledge before) family
  ... | nothing = clearKeepsOther family selected (World.codeIndex before) different
  ... | just existing with sameProfile existing profile
  ...   | yes _ = refl
  ...   | no _ = clearKeepsOther family selected (World.codeIndex before) different

  otherVectorsPreserved : ∀ family profile before selected → ¬ (family ≡ selected) →
    World.codeVectorProfile (recreate family profile before) selected ≡ World.codeVectorProfile before selected
  otherVectorsPreserved family profile before selected different with Knowledge.World.profile (World.knowledge before) family
  ... | nothing = clearKeepsOther family selected (World.codeVectorProfile before) different
  ... | just existing with sameProfile existing profile
  ...   | yes _ = refl
  ...   | no _ = clearKeepsOther family selected (World.codeVectorProfile before) different

  -- A changed profile drops the old code index and its vectors.
  changedIndexCleared : ∀ family profile before →
    ¬ (Knowledge.World.profile (World.knowledge before) family ≡ just profile) →
    World.codeIndex (recreate family profile before) family ≡ nothing
  changedIndexCleared family profile before changed with Knowledge.World.profile (World.knowledge before) family
  ... | nothing with sameFamily family family
  ...   | yes _ = refl
  ...   | no unequal = ⊥-elim (unequal refl)
  changedIndexCleared family profile before changed | just existing with sameProfile existing profile
  ... | yes refl = ⊥-elim (changed refl)
  ... | no different with sameFamily family family
  ...   | yes _ = refl
  ...   | no unequal = ⊥-elim (unequal refl)

  changedCodeVectorsCleared : ∀ family profile before →
    ¬ (Knowledge.World.profile (World.knowledge before) family ≡ just profile) →
    World.codeVectorProfile (recreate family profile before) family ≡ nothing
  changedCodeVectorsCleared family profile before changed with Knowledge.World.profile (World.knowledge before) family
  ... | nothing with sameFamily family family
  ...   | yes _ = refl
  ...   | no unequal = ⊥-elim (unequal refl)
  changedCodeVectorsCleared family profile before changed | just existing with sameProfile existing profile
  ... | yes refl = ⊥-elim (changed refl)
  ... | no different with sameFamily family family
  ...   | yes _ = refl
  ...   | no unequal = ⊥-elim (unequal refl)

  changedNoteVectorsCleared : ∀ family profile before id →
    ¬ (Knowledge.World.profile (World.knowledge before) family ≡ just profile) →
    Knowledge.World.vectorProfile (World.knowledge (recreate family profile before)) family id ≡ nothing
  changedNoteVectorsCleared family profile before id changed with Knowledge.World.profile (World.knowledge before) family
  ... | nothing = Notes.recreateClearsVectors family profile (World.knowledge before) id
  ... | just existing with sameProfile existing profile
  ...   | yes refl = ⊥-elim (changed refl)
  ...   | no different = Notes.recreateClearsVectors family profile (World.knowledge before) id

  -- Interruption before the atomic replacement leaves the old world, so the
  -- same operation can be retried without persisting special failure state.
  attempt : Bool → W.FamilyId → W.EmbeddingKey → World → World
  attempt false family profile before = before
  attempt true family profile before = recreate family profile before

  retryAfterInterruption : ∀ family profile before →
    recreate family profile (attempt false family profile before) ≡ recreate family profile before
  retryAfterInterruption family profile before = refl
