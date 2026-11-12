{-# OPTIONS --safe #-}
-- Curated notes belong to a family; a note may be limited to one checkout.
module Muninn.KnowledgeState where

open import Muninn.Knowledge using (KnowledgeId; KnowledgeItem)
open import Muninn.Worktree using (FamilyId; CheckoutId; Checkout; EmbeddingKey)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Empty using (⊥-elim)

record Note (family : FamilyId) (id : KnowledgeId) : Set where
  field item : KnowledgeItem
        familyMatches : KnowledgeItem.family item ≡ family
        idMatches : KnowledgeItem.id item ≡ id
        scope : Maybe CheckoutId

Store : Set
Store = (family : FamilyId) → (id : KnowledgeId) → Maybe (Note family id)

-- Vector readiness is derived state. The profile belongs to the family.
record World : Set where
  field notes : Store
        profile : FamilyId → Maybe EmbeddingKey
        vectorProfile : FamilyId → KnowledgeId → Maybe EmbeddingKey

module Operations
  (sameFamily : (a b : FamilyId) → Dec (a ≡ b))
  (sameId : (a b : KnowledgeId) → Dec (a ≡ b)) where

  updatedProfile : FamilyId → EmbeddingKey → World → FamilyId → Maybe EmbeddingKey
  updatedProfile family new before selected with sameFamily family selected
  ... | yes _ = just new
  ... | no _ = World.profile before selected

  clearedVectors : FamilyId → World → FamilyId → KnowledgeId → Maybe EmbeddingKey
  clearedVectors family before selected id with sameFamily family selected
  ... | yes _ = nothing
  ... | no _ = World.vectorProfile before selected id

  recreateProfile : FamilyId → EmbeddingKey → World → World
  recreateProfile family new before = record
    { notes = World.notes before
    ; profile = updatedProfile family new before
    ; vectorProfile = clearedVectors family before }

  recreateSetsProfile : ∀ family new before →
    World.profile (recreateProfile family new before) family ≡ just new
  recreateSetsProfile family new before with sameFamily family family
  ... | yes _ = refl
  ... | no distinct = ⊥-elim (distinct refl)

  recreateKeepsOtherProfile : ∀ family new before selected → ¬ (family ≡ selected) →
    World.profile (recreateProfile family new before) selected ≡ World.profile before selected
  recreateKeepsOtherProfile family new before selected distinct with sameFamily family selected
  ... | yes same = ⊥-elim (distinct same)
  ... | no _ = refl

  recreateKeepsNotes : ∀ family new before selected id →
    World.notes (recreateProfile family new before) selected id ≡ World.notes before selected id
  recreateKeepsNotes family new before selected id = refl

  recreateClearsVectors : ∀ family new before id →
    World.vectorProfile (recreateProfile family new before) family id ≡ nothing
  recreateClearsVectors family new before id with sameFamily family family
  ... | yes _ = refl
  ... | no distinct = ⊥-elim (distinct refl)

  recreateKeepsOtherVectors : ∀ family new before selected id → ¬ (family ≡ selected) →
    World.vectorProfile (recreateProfile family new before) selected id ≡ World.vectorProfile before selected id
  recreateKeepsOtherVectors family new before selected id distinct with sameFamily family selected
  ... | yes same = ⊥-elim (distinct same)
  ... | no _ = refl

  updatedVector : FamilyId → KnowledgeId → EmbeddingKey → World → FamilyId → KnowledgeId → Maybe EmbeddingKey
  updatedVector family id source before selected key with sameFamily family selected | sameId id key
  ... | yes _ | yes _ = just source
  ... | _ | _ = World.vectorProfile before selected key

  -- A completed vector must match both the still-current note and profile.
  prepareVector : ∀ family id (before : World) (note : Note family id)
    (sourceProfile : EmbeddingKey) → World.notes before family id ≡ just note →
    World.profile before family ≡ just sourceProfile → World
  prepareVector family id before note sourceProfile present current = record
    { notes = World.notes before
    ; profile = World.profile before
    ; vectorProfile = updatedVector family id sourceProfile before }

  preparedUsesFamilyProfile : ∀ family id before note sourceProfile present current →
    World.vectorProfile (prepareVector family id before note sourceProfile present current) family id ≡ just sourceProfile
  preparedUsesFamilyProfile family id before note sourceProfile present current with sameFamily family family | sameId id id
  ... | yes _ | yes _ = refl
  ... | no distinct | _ = ⊥-elim (distinct refl)
  ... | _ | no distinct = ⊥-elim (distinct refl)

  put : ∀ family id → Note family id → Store → Store
  put family id note before selected key with sameFamily family selected | sameId id key
  ... | yes refl | yes refl = just note
  ... | _ | _ = before selected key

  remove : FamilyId → KnowledgeId → Store → Store
  remove family id before selected key with sameFamily family selected | sameId id key
  ... | yes refl | yes refl = nothing
  ... | _ | _ = before selected key

  clearNoteVector : FamilyId → KnowledgeId → World → FamilyId → KnowledgeId → Maybe EmbeddingKey
  clearNoteVector family id before selected key with sameFamily family selected | sameId id key
  ... | yes _ | yes _ = nothing
  ... | _ | _ = World.vectorProfile before selected key

  recordNote : ∀ family id → Note family id → World → World
  recordNote family id note before = record
    { notes = put family id note (World.notes before)
    ; profile = World.profile before
    ; vectorProfile = clearNoteVector family id before }

  deleteNote : FamilyId → KnowledgeId → World → World
  deleteNote family id before = record
    { notes = remove family id (World.notes before)
    ; profile = World.profile before
    ; vectorProfile = clearNoteVector family id before }

  changedNoteHasNoOldVector : ∀ family id before note →
    World.vectorProfile (recordNote family id note before) family id ≡ nothing
  changedNoteHasNoOldVector family id before note with sameFamily family family | sameId id id
  ... | yes _ | yes _ = refl
  ... | no distinct | _ = ⊥-elim (distinct refl)
  ... | _ | no distinct = ⊥-elim (distinct refl)

  deletedNoteHasNoVector : ∀ family id before →
    World.vectorProfile (deleteNote family id before) family id ≡ nothing
  deletedNoteHasNoVector family id before with sameFamily family family | sameId id id
  ... | yes _ | yes _ = refl
  ... | no distinct | _ = ⊥-elim (distinct refl)
  ... | _ | no distinct = ⊥-elim (distinct refl)

  changedNoteKeepsOtherFamilyVectors : ∀ family id before note other key → ¬ (family ≡ other) →
    World.vectorProfile (recordNote family id note before) other key ≡ World.vectorProfile before other key
  changedNoteKeepsOtherFamilyVectors family id before note other key distinct with sameFamily family other | sameId id key
  ... | yes same | _ = ⊥-elim (distinct same)
  ... | no _ | _ = refl

  deletedNoteKeepsOtherFamilyVectors : ∀ family id before other key → ¬ (family ≡ other) →
    World.vectorProfile (deleteNote family id before) other key ≡ World.vectorProfile before other key
  deletedNoteKeepsOtherFamilyVectors family id before other key distinct with sameFamily family other | sameId id key
  ... | yes same | _ = ⊥-elim (distinct same)
  ... | no _ | _ = refl

  changedNoteKeepsOtherVectors : ∀ family id before note other key → ¬ (id ≡ key) →
    World.vectorProfile (recordNote family id note before) other key ≡ World.vectorProfile before other key
  changedNoteKeepsOtherVectors family id before note other key distinct with sameFamily family other | sameId id key
  ... | _ | yes equal = ⊥-elim (distinct equal)
  ... | yes _ | no _ = refl
  ... | no _ | no _ = refl

  deletedNoteKeepsOtherVectors : ∀ family id before other key → ¬ (id ≡ key) →
    World.vectorProfile (deleteNote family id before) other key ≡ World.vectorProfile before other key
  deletedNoteKeepsOtherVectors family id before other key distinct with sameFamily family other | sameId id key
  ... | _ | yes equal = ⊥-elim (distinct equal)
  ... | yes _ | no _ = refl
  ... | no _ | no _ = refl

  putAt : ∀ family id note before → put family id note before family id ≡ just note
  putAt family id note before with sameFamily family family | sameId id id
  ... | yes refl | yes refl = refl
  ... | no different | _ = ⊥-elim (different refl)
  ... | _ | no different = ⊥-elim (different refl)

  removeAt : ∀ family id before → remove family id before family id ≡ nothing
  removeAt family id before with sameFamily family family | sameId id id
  ... | yes refl | yes refl = refl
  ... | no different | _ = ⊥-elim (different refl)
  ... | _ | no different = ⊥-elim (different refl)

  recordedNote : ∀ family id note before →
    World.notes (recordNote family id note before) family id ≡ just note
  recordedNote family id note before = putAt family id note (World.notes before)

  deletedNote : ∀ family id before →
    World.notes (deleteNote family id before) family id ≡ nothing
  deletedNote family id before = removeAt family id (World.notes before)

  putOtherFamily : ∀ family id note before other key → ¬ (family ≡ other) →
    put family id note before other key ≡ before other key
  putOtherFamily family id note before other key distinct with sameFamily family other | sameId id key
  ... | yes equal | _ = ⊥-elim (distinct equal)
  ... | no _ | _ = refl

  removeOtherFamily : ∀ family id before other key → ¬ (family ≡ other) →
    remove family id before other key ≡ before other key
  removeOtherFamily family id before other key distinct with sameFamily family other | sameId id key
  ... | yes equal | _ = ⊥-elim (distinct equal)
  ... | no _ | _ = refl

  putOtherNote : ∀ family id note before selected key → ¬ (id ≡ key) →
    put family id note before selected key ≡ before selected key
  putOtherNote family id note before selected key distinct with sameFamily family selected | sameId id key
  ... | _ | yes equal = ⊥-elim (distinct equal)
  ... | yes refl | no _ = refl
  ... | no _ | no _ = refl

  removeOtherNote : ∀ family id before selected key → ¬ (id ≡ key) →
    remove family id before selected key ≡ before selected key
  removeOtherNote family id before selected key distinct with sameFamily family selected | sameId id key
  ... | _ | yes equal = ⊥-elim (distinct equal)
  ... | yes refl | no _ = refl
  ... | no _ | no _ = refl

  putRetry : ∀ family id note before selected key →
    put family id note (put family id note before) selected key ≡
    put family id note before selected key
  putRetry family id note before selected key with sameFamily family selected in familyDecision | sameId id key in idDecision
  ... | yes refl | yes refl = refl
  ... | yes refl | no _ rewrite familyDecision | idDecision = refl
  ... | no _ | _ rewrite familyDecision = refl

  removeRetry : ∀ family id before selected key →
    remove family id (remove family id before) selected key ≡ remove family id before selected key
  removeRetry family id before selected key with sameFamily family selected in familyDecision | sameId id key in idDecision
  ... | yes refl | yes refl = refl
  ... | yes refl | no _ rewrite familyDecision | idDecision = refl
  ... | no _ | _ rewrite familyDecision = refl

-- Visibility requires the checkout and note to belong to the same family.
data Visible {family id} (note : Note family id) (checkout : Checkout) : Set where
  familyWide : Checkout.family checkout ≡ family → Note.scope note ≡ nothing → Visible note checkout
  oneCheckout : Checkout.family checkout ≡ family →
    Note.scope note ≡ just (Checkout.id checkout) → Visible note checkout

familyWideVisible : ∀ {family id} (note : Note family id) checkout →
  Checkout.family checkout ≡ family → Note.scope note ≡ nothing → Visible note checkout
familyWideVisible note checkout same scope = familyWide same scope

foreignCheckoutCannotSee : ∀ {family id} (note : Note family id) checkout →
  ¬ (Checkout.family checkout ≡ family) → ¬ Visible note checkout
foreignCheckoutCannotSee note checkout different (familyWide same scope) = different same
foreignCheckoutCannotSee note checkout different (oneCheckout same scope) = different same

justNotNothing : ∀ {A : Set} {value : A} → ¬ (just value ≡ nothing)
justNotNothing ()

scopedNoteNotVisibleElsewhere : ∀ {family id} (note : Note family id) checkout selected →
  Note.scope note ≡ just selected → ¬ (Checkout.id checkout ≡ selected) → ¬ Visible note checkout
scopedNoteNotVisibleElsewhere note checkout selected scoped distinct (familyWide sameFamily unrestricted) =
  justNotNothing (trans (sym scoped) unrestricted)
scopedNoteNotVisibleElsewhere note checkout selected scoped distinct (oneCheckout sameFamily selectedHere) =
  distinct (sym (just-injective (trans (sym scoped) selectedHere)))
