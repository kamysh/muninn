{-# OPTIONS --safe #-}
-- Coverage and mandatory compatible reuse are read from the actual owned world.
module Muninn.StagedVectors where
import Muninn.OwnedState as O
import Muninn.VectorData as V
import Muninn.Worktree as W
import Muninn.ArtifactIdentity as Equal
import Muninn.ContentViews as Views
import Muninn.ExclusionOutcomes as E
import Muninn.ExclusionClassifier as Classify
import Muninn.FiniteClosure as F
import Muninn.CleanupObservations as Observations
open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (Bool; true; false)
open import Data.String using (String)
import Data.String as String
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
module DB = O.DB

data Availability : Set where pending usable waiting : Availability

module Family (selection : E.Rule) (profile : W.EmbeddingKey) where
  owner = E.targetOwner selection

  -- A reusable completed vector can belong to another chunk in this family.
  -- Repeated text at different positions does not need another provider call.
  completed : String → O.Record → Maybe V.Value
  completed text (O.recordOf actualOwner (O.vector chunk (V.usable saved))) with
    E.ownerEqual actualOwner owner | Equal.EmbeddingKey? (V.Value.profile saved) profile | V.Value.source saved String.≟ text
  ... | yes sameOwner | yes sameProfile | yes sameText = just saved
  ... | _ | _ | _ = nothing
  completed text value = nothing

  ready : O.World → String → Maybe V.Value
  ready world text = Views.find (completed text) world

  readySound : ∀ world text saved → ready world text ≡ just saved →
    Σ (ℕ × O.Record) (λ row → row ∈ world × completed text (proj₂ row) ≡ just saved)
  readySound world text saved found = Views.findSound (completed text) world saved found

  completedMatches : ∀ text row saved → completed text row ≡ just saved →
    V.Value.profile saved ≡ profile × V.Value.source saved ≡ text
  completedMatches text (O.recordOf actualOwner (O.vector chunk (V.usable stored))) saved found with
    E.ownerEqual actualOwner owner | Equal.EmbeddingKey? (V.Value.profile stored) profile | V.Value.source stored String.≟ text
  ... | yes sameOwner | yes sameProfile | yes sameText with found
  ...   | refl = sameProfile , sameText
  completedMatches text (O.recordOf actualOwner (O.vector chunk (V.usable stored))) saved found | yes sameOwner | yes sameProfile | no different with found
  ...   | ()
  completedMatches text (O.recordOf actualOwner (O.vector chunk (V.usable stored))) saved found | yes sameOwner | no different | _ with found
  ...   | ()
  completedMatches text (O.recordOf actualOwner (O.vector chunk (V.usable stored))) saved found | no different | _ | _ with found
  ...   | ()

  readyValid : ∀ world text saved → ready world text ≡ just saved →
    V.Valid (W.EmbeddingKey.dimension profile) (V.Value.values saved)
  readyValid world text saved found with readySound world text saved found
  ... | row , present , chosen rewrite sym (proj₁ (completedMatches text (proj₂ row) saved chosen)) = V.Value.valid saved

  linkedCompleted : ℕ → String → O.Record → Maybe V.Value
  linkedCompleted selected text value@(O.recordOf actualOwner (O.vector chunk state)) with chunk ≟ selected
  ... | yes sameChunk = completed text value
  ... | no different = nothing
  linkedCompleted selected text value = nothing

  -- A cached vector on another chunk is reusable, but is not yet semantic
  -- coverage for this chunk. Its actual association must be published first.
  linkedReady : O.World → ℕ → String → Maybe V.Value
  linkedReady world chunk text = Views.find (linkedCompleted chunk text) world

  linkedImpliesCompleted : ∀ chunk text row saved → linkedCompleted chunk text row ≡ just saved → completed text row ≡ just saved
  linkedImpliesCompleted selected text (O.recordOf actualOwner (O.vector chunk state)) saved found with chunk ≟ selected
  ... | yes sameChunk = found
  ... | no different with found
  ...   | ()

  linkedReadyValid : ∀ world chunk text saved → linkedReady world chunk text ≡ just saved →
    V.Valid (W.EmbeddingKey.dimension profile) (V.Value.values saved)
  linkedReadyValid world chunk text saved found = let witness = Views.findSound (linkedCompleted chunk text) world saved found in let row = proj₁ witness in let evidence = linkedImpliesCompleted chunk text (proj₂ row) saved (proj₂ (proj₂ witness)) in subst (λ selected → V.Valid (W.EmbeddingKey.dimension selected) (V.Value.values saved)) (proj₁ (completedMatches text (proj₂ row) saved evidence)) (V.Value.valid saved)

  completedKnown : ∀ chunk text saved → V.Value.profile saved ≡ profile → V.Value.source saved ≡ text →
    completed text (O.recordOf owner (O.vector chunk (V.usable saved))) ≡ just saved
  completedKnown chunk text saved sameProfile sameText with E.ownerEqual owner owner
  ... | no different = ⊥-elim (different refl)
  ... | yes sameOwner with Equal.EmbeddingKey? (V.Value.profile saved) profile
  ...   | no different = ⊥-elim (different sameProfile)
  ...   | yes sameKey with V.Value.source saved String.≟ text
  ...     | no different = ⊥-elim (different sameText)
  ...     | yes sameContent = refl

  linkedKnown : ∀ chunk text saved → V.Value.profile saved ≡ profile → V.Value.source saved ≡ text →
    linkedCompleted chunk text (O.recordOf owner (O.vector chunk (V.usable saved))) ≡ just saved
  linkedKnown chunk text saved sameProfile sameText with chunk ≟ chunk
  ... | no different = ⊥-elim (different refl)
  ... | yes sameChunk = completedKnown chunk text saved sameProfile sameText

  -- A missing provider is normal unfinished vector preparation. Its saved
  -- explanation is relevant only to this exact chunk/text/profile.
  needsInput : ℕ → String → O.Record → Maybe V.Guidance
  needsInput selected text (O.recordOf actualOwner (O.vector chunk (V.waiting storedProfile storedText guidance))) with
    E.ownerEqual actualOwner owner | chunk ≟ selected | Equal.EmbeddingKey? storedProfile profile | storedText String.≟ text
  ... | yes sameOwner | yes sameChunk | yes sameProfile | yes sameText = just guidance
  ... | _ | _ | _ | _ = nothing
  needsInput selected text value = nothing

  guidance : O.World → ℕ → String → Maybe V.Guidance
  guidance world chunk text = Views.find (needsInput chunk text) world

  availability : O.World → ℕ → String → Availability
  availability world chunk text with linkedReady world chunk text
  ... | just saved = usable
  ... | nothing with guidance world chunk text
  ...   | just explanation = waiting
  ...   | nothing = pending

  storedVectorIsReported : ∀ world slot chunk text saved →
    DB.lookup slot world ≡ just (O.recordOf owner (O.vector chunk (V.usable saved))) →
    V.Value.profile saved ≡ profile → V.Value.source saved ≡ text → availability world chunk text ≡ usable
  storedVectorIsReported world slot chunk text saved located sameProfile sameText with linkedReady world chunk text in readyAt
  ... | just current = refl
  ... | nothing = ⊥-elim (impossible (trans (sym absent) (linkedKnown chunk text saved sameProfile sameText)))
    where
    absent : linkedCompleted chunk text (O.recordOf owner (O.vector chunk (V.usable saved))) ≡ nothing
    absent = Views.findAbsent (linkedCompleted chunk text) world readyAt _ (Observations.lookupMember world slot _ located)
    impossible : nothing ≢ just saved
    impossible ()

  usableRequiresStoredVector : ∀ world chunk text → availability world chunk text ≡ usable →
    Σ V.Value (λ saved → linkedReady world chunk text ≡ just saved)
  usableRequiresStoredVector world chunk text claimed with linkedReady world chunk text in found
  ... | just saved = saved , refl
  ... | nothing with guidance world chunk text
  ...   | just explanation = ⊥-elim (impossible claimed)
    where impossible : waiting ≢ usable
          impossible ()
  ...   | nothing = ⊥-elim (impossible claimed)
    where impossible : pending ≢ usable
          impossible ()

  waitingRequiresExplanation : ∀ world chunk text → availability world chunk text ≡ waiting →
    linkedReady world chunk text ≡ nothing × Σ V.Guidance (λ why → guidance world chunk text ≡ just why)
  waitingRequiresExplanation world chunk text claimed with linkedReady world chunk text in found
  ... | just saved with claimed
  ...   | ()
  waitingRequiresExplanation world chunk text claimed | nothing with guidance world chunk text in explained
  ... | just why = refl , why , refl
  ... | nothing with claimed
  ...   | ()

  data Action (world : O.World) (text : String) : Set where
    reuse : (saved : V.Value) → ready world text ≡ just saved → Action world text
    prepare : ready world text ≡ nothing → Action world text

  next : ∀ world text → Action world text
  next world text with ready world text in found
  ... | just saved = reuse saved found
  ... | nothing = prepare found

  callsProvider : ∀ {world text} → Action world text → Bool
  callsProvider (reuse saved found) = false
  callsProvider (prepare absent) = true

  completedCannotCallProvider : ∀ world text saved → ready world text ≡ just saved →
    (action : Action world text) → callsProvider action ≡ false
  completedCannotCallProvider world text saved found (reuse cached present) = refl
  completedCannotCallProvider world text saved found (prepare absent) with trans (sym found) absent
  ... | ()

  -- Full-text availability has no vector premise. Needed selects the current
  -- published family view, excluding content held only by old readers/jobs.
  postingPayload : ℕ → O.Record → Maybe String
  postingPayload selected (O.recordOf actualOwner (O.posting chunk payload)) with E.ownerEqual actualOwner owner | chunk ≟ selected
  ... | yes sameOwner | yes sameChunk = just payload
  ... | _ | _ = nothing
  postingPayload selected value = nothing

  posted : O.World → ℕ → Maybe String
  posted world chunk = Views.find (postingPayload chunk) world

  TextAt : O.World → ℕ → String → Set
  TextAt world chunk text = Σ ℕ (λ version →
    DB.lookup chunk world ≡ just (O.recordOf owner (O.chunk version text)) ×
    (E.Model.Needed selection world chunk × Σ String (λ payload → posted world chunk ≡ just payload)))

  rowAvailability : O.World → ℕ × O.Record → Maybe (ℕ × Availability)
  rowAvailability world (chunk , O.recordOf actualOwner (O.chunk version text)) with
    E.ownerEqual actualOwner owner | Classify.Model.Assessment.needed? selection world chunk | posted world chunk
  ... | yes sameOwner | yes included | just posting = just (chunk , availability world chunk text)
  ... | _ | _ | _ = nothing
  rowAvailability world row = nothing

  rows : O.World → O.World → List (ℕ × Availability)
  rows world [] = []
  rows world (row ∷ rest) with rowAvailability world row
  ... | nothing = rows world rest
  ... | just item = item ∷ rows world rest

  report : O.World → List (ℕ × Availability)
  report world = rows world world

  rowsSound : ∀ world scan item → item ∈ rows world scan →
    Σ (ℕ × O.Record) (λ row → row ∈ scan × rowAvailability world row ≡ just item)
  rowsSound world (row ∷ rest) item present with rowAvailability world row in classified
  ... | nothing with rowsSound world rest item present
  ...   | source , included , same = source , there included , same
  rowsSound world (row ∷ rest) item present | just selected with present
  ... | here refl = row , here refl , classified
  ... | there later with rowsSound world rest item later
  ...   | source , included , same = source , there included , same

  rowsComplete : ∀ world scan row item → row ∈ scan → rowAvailability world row ≡ just item → item ∈ rows world scan
  rowsComplete world (row ∷ rest) .row item (here refl) classified rewrite classified = here refl
  rowsComplete world (first ∷ rest) row item (there included) classified with rowAvailability world first
  ... | nothing = rowsComplete world rest row item included classified
  ... | just other = there (rowsComplete world rest row item included classified)

  reportUsesActualRows : ∀ world item → item ∈ report world →
    Σ (ℕ × O.Record) (λ row → row ∈ world × rowAvailability world row ≡ just item)
  reportUsesActualRows world item present = rowsSound world world item present

  everySearchableChunkReported : ∀ world chunk text → TextAt world chunk text →
    (chunk , availability world chunk text) ∈ report world
  everySearchableChunkReported world chunk text (version , located , included , payload , postingAt) =
    rowsComplete world world (chunk , O.recordOf owner (O.chunk version text)) _
      (Observations.lookupMember world chunk _ located) classified
    where
    classified : rowAvailability world (chunk , O.recordOf owner (O.chunk version text)) ≡ just (chunk , availability world chunk text)
    classified rewrite postingAt with E.ownerEqual owner owner | Classify.Model.Assessment.needed? selection world chunk
    ... | no different | _ = ⊥-elim (different refl)
    ... | _ | no missing = ⊥-elim (missing included)
    ... | yes sameOwner | yes selected = refl
