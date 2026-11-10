{-# OPTIONS --safe #-}
-- The independent analysis model is fixed once, not supplied by handlers.
-- Parser/chunker semantics are owned by #42; reuse is proved for every such model.
module Muninn.ArtifactReuse where

import Muninn.Worktree as W
import Muninn.ArtifactIdentity as Identity
import Muninn.CanonicalChunks as Chunks
import Muninn.CompletedWork as Completed
import Muninn.VectorData as Vector
import Muninn.Catalog as Catalog
import Muninn.CatalogInputs as Input
open import Muninn.Float using (Float)
import Data.Bool
open import Data.List using (List; length)
open import Data.Fin using (Fin)
import Data.List.Relation.Unary.All as All
open All using (All)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (map′; _×-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; cong; cong₂; trans)

record AnalysisInput : Set where
  constructor analysisInput
  field family : W.FamilyId
        meaning : W.AnalysisMeaning

analysisInput? : ∀ (first second : AnalysisInput) → Dec (first ≡ second)
analysisInput? first second = map′ (λ { (refl , refl) → refl }) (λ { refl → refl , refl })
  (Identity.FamilyId? (AnalysisInput.family first) (AnalysisInput.family second) ×-dec
   Identity.AnalysisMeaning? (AnalysisInput.meaning first) (AnalysisInput.meaning second))

record EmbeddingInput : Set where
  constructor embeddingInput
  field family : W.FamilyId
        profile : W.EmbeddingKey
        bytes : List (Fin 256)

embeddingInput? : ∀ (first second : EmbeddingInput) → Dec (first ≡ second)
embeddingInput? first second = map′ (λ { (refl , refl , refl) → refl }) (λ { refl → refl , refl , refl })
  (Identity.FamilyId? (EmbeddingInput.family first) (EmbeddingInput.family second) ×-dec
   (Identity.EmbeddingKey? (EmbeddingInput.profile first) (EmbeddingInput.profile second) ×-dec
    Identity.byteList? (EmbeddingInput.bytes first) (EmbeddingInput.bytes second)))

fromVersion : W.FileVersion → AnalysisInput
fromVersion version = analysisInput (W.FileVersion.family version) (W.analysisMeaning (W.FileVersion.analysisKey version))

compatibleAnalysisInput : ∀ first second → W.AnalysisCompatible first second → fromVersion first ≡ fromVersion second
compatibleAnalysisInput first second (sameFamily , sameMeaning) = cong₂ analysisInput sameFamily sameMeaning

fromEmbedding : W.EmbeddingArtifact → EmbeddingInput
fromEmbedding artifact = embeddingInput (W.VersionRef.family (W.EmbeddingArtifact.version artifact))
  (W.EmbeddingArtifact.key artifact) (W.EmbeddingArtifact.input artifact)

compatibleEmbeddingInput : ∀ first second → W.EmbeddingCompatible first second → fromEmbedding first ≡ fromEmbedding second
compatibleEmbeddingInput first second (sameFamily , sameBytes , sameProfile) = trans
  (cong₂ (λ family profile → embeddingInput family profile (W.EmbeddingArtifact.input first)) sameFamily sameProfile)
  (cong (embeddingInput (W.VersionRef.family (W.EmbeddingArtifact.version second)) (W.EmbeddingArtifact.key second)) sameBytes)

record AnalysisModel : Set₁ where
  field candidates : W.AnalysisMeaning → List W.AnalyzedChunk
        validCandidates : ∀ key → All (Chunks.ValidChunk key) (candidates key)

-- The complete output is fixed by the independent versioned model. The cache
-- cannot weaken its goal or substitute different text for equal input bytes.
module Analyses (model : AnalysisModel) (family : W.FamilyId) where
  expected : AnalysisInput → List W.AnalyzedChunk
  expected input = Chunks.canonical (AnalysisModel.candidates model (AnalysisInput.meaning input))

  Valid : AnalysisInput → List W.AnalyzedChunk → Set
  Valid input chunks = AnalysisInput.family input ≡ family ×
    (chunks ≡ expected input × (Chunks.UniqueSpans chunks × All (Chunks.ValidChunk (AnalysisInput.meaning input)) chunks))

  module Memo = Completed.For AnalysisInput (List W.AnalyzedChunk) analysisInput?
  module Saved = Memo.Certified Valid

  computedValid : ∀ input → AnalysisInput.family input ≡ family → Valid input (expected input)
  computedValid input owner = owner , refl , Chunks.unique raw ,
    Chunks.preserves (Chunks.ValidChunk key) raw (AnalysisModel.validCandidates model key)
    where
    key = AnalysisInput.meaning input
    raw = AnalysisModel.candidates model key

  -- Every computation or reuse action is indexed by the actual saved cache.
  next : ∀ input → AnalysisInput.family input ≡ family → ∀ before → Memo.Action input (Saved.Cache.rows before)
  next input owner = Saved.nextAction input

  checkpoint : (input : AnalysisInput) → (chunks : List W.AnalyzedChunk) → Valid input chunks → Saved.Cache → Saved.Cache
  checkpoint = Saved.checkpoint

  reusedContent : ∀ input before chunks → Memo.Store.lookup input (Saved.Cache.rows before) ≡ just chunks →
    chunks ≡ expected input
  reusedContent input before chunks found = proj₁ (proj₂ (Saved.reusedValueValid input before chunks found))

  reusedSpans : ∀ input before chunks → Memo.Store.lookup input (Saved.Cache.rows before) ≡ just chunks → Chunks.UniqueSpans chunks
  reusedSpans input before chunks found = proj₁ (proj₂ (proj₂ (Saved.reusedValueValid input before chunks found)))

  checkpointReuses : ∀ input chunks valid before →
    Memo.invokesProvider (next input (proj₁ valid) (checkpoint input chunks valid before)) ≡ Data.Bool.false
  checkpointReuses input chunks valid before = Memo.checkpointReuses input chunks (Saved.Cache.rows before)

module Embeddings (family : W.FamilyId) where
  Valid : EmbeddingInput → List Float → Set
  Valid input vector = EmbeddingInput.family input ≡ family ×
    Vector.Valid (W.EmbeddingKey.dimension (EmbeddingInput.profile input)) vector

  -- Reply association is with the exact submitted profile/input. The provider
  -- effect adapter must establish this indexed response (#37/#52).
  record Reply (input : EmbeddingInput) : Set where
    constructor reply
    field vector : List Float
          dimension : Valid input vector

  module Memo = Completed.For EmbeddingInput (List Float) embeddingInput?
  module Saved = Memo.Certified Valid

  next : ∀ input → EmbeddingInput.family input ≡ family → ∀ before → Memo.Action input (Saved.Cache.rows before)
  next input owner = Saved.nextAction input

  checkpoint : (input : EmbeddingInput) → Reply input → Saved.Cache → Saved.Cache
  checkpoint input received = Saved.checkpoint input (Reply.vector received) (Reply.dimension received)

  reusedValid : ∀ input before vector → Memo.Store.lookup input (Saved.Cache.rows before) ≡ just vector → Valid input vector
  reusedValid = Saved.reusedValueValid

  checkpointReuses : ∀ input (received : Reply input) before →
    Memo.invokesProvider (next input (proj₁ (Reply.dimension received)) (checkpoint input received before)) ≡ Data.Bool.false
  checkpointReuses input received before = Memo.checkpointReuses input (Reply.vector received) (Saved.Cache.rows before)

-- Only the explicit closed-catalog recreation intent permits a clean start.
Recreation : Catalog.Request → Set
Recreation (Catalog.user adapter input) = Catalog.canonicalIntent adapter ≡ Input.recreateIndex
Recreation (Catalog.background job input) = ⊥
Recreation (Catalog.control event input) = ⊥
Recreation (Catalog.localUi input) = ⊥

recreationFamily : ∀ request → Recreation request → W.FamilyId
recreationFamily (Catalog.user adapter input) permitted = Input.FamilyTarget.expectedFamily
  (proj₁ (Input.Mutation.input (subst Input.IntentInput permitted input)))
recreationFamily (Catalog.background job input) ()
recreationFamily (Catalog.control event input) ()
recreationFamily (Catalog.localUi input) ()

module State (model : AnalysisModel) where
  record FamilyCache (family : W.FamilyId) : Set where
    constructor familyCache
    module A = Analyses model family
    module E = Embeddings family
    field analysis : A.Saved.Cache
          embedding : E.Saved.Cache

  Cache : Set
  Cache = (family : W.FamilyId) → FamilyCache family

  emptyFor : ∀ family → FamilyCache family
  emptyFor family = familyCache (Analyses.Saved.empty model family) (Embeddings.Saved.empty family)

  -- A clean restart updates only the explicitly targeted family. Existing
  -- namespaces continue to use their saved work and mandatory next actions.
  recreate : ∀ request → Recreation request → Cache → Cache
  recreate request permitted before family with Identity.FamilyId? family (recreationFamily request permitted)
  ... | yes same = emptyFor family
  ... | no different = before family

  recreateIsolates : ∀ request permitted before family → family ≢ recreationFamily request permitted →
    recreate request permitted before family ≡ before family
  recreateIsolates request permitted before family distinct with Identity.FamilyId? family (recreationFamily request permitted)
  ... | yes same = ⊥-elim (distinct same)
  ... | no different = refl

ordinaryReindexCannotRecreate : ∀ adapter input → Catalog.canonicalIntent adapter ≡ Input.reindex →
  Recreation (Catalog.user adapter input) → ⊥
ordinaryReindexCannotRecreate adapter input ordinary permitted with trans (Relation.Binary.PropositionalEquality.sym ordinary) permitted
... | ()
