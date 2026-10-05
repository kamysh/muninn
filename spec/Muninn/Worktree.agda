{-# OPTIONS --safe #-}
-- A family application schema contains shared file versions and a current base.
-- Each checkout has its own AGE graph and path-specific differences.
-- Baseline IDs below name logical states, not separately retained SQL snapshots;
-- FileMap.moveBase proves preservation when the current base is replaced.
module Muninn.Worktree where

open import Muninn.Types
open import Data.List using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.String using (String; _++_)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤)
open import Data.Product using (Σ; _×_; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim)

record FamilyId : Set where
  field value : UUID
record SchemaId : Set where
  field value : UUID
record CheckoutId : Set where
  field value : UUID
record SnapshotId : Set where
  field value : UUID
record VersionId : Set where
  field value : UUID

-- Family-qualified logical address; versions never belong to one worktree.
record VersionRef : Set where
  field family : FamilyId
        version : VersionId

record AnalysisKey : Set where
  field bytes : List (Fin 256) -- exact full bytes; hashes are lookup aids
        contentHash : String
        parserVersion chunkerVersion analysisConfig language : String

record EmbeddingKey : Set where
  field backend model configuration : String
        dimension : ℕ

record AnalyzedChunk : Set where
  field range : LineRange
        content : String

record FileVersion : Set where
  field id : VersionId
        family : FamilyId
        analysisKey : AnalysisKey
        chunks : List AnalyzedChunk

record EmbeddingArtifact : Set where
  field version : VersionRef
        key : EmbeddingKey

record Checkout : Set where
  field id : CheckoutId
        family : FamilyId
        root : FilePath

record FileEntry : Set where
  field version : VersionRef
        tier : Tier

-- Extensional meaning of a finite path map, not a requirement to materialize
-- one SQL row per inherited path. Paths must be validated by the implementation.
Manifest : Set
Manifest = FilePath → Maybe FileEntry

-- Baselines are addressed by stable IDs, never by a moving branch name.
-- This total environment models available snapshots; retention is in Storage.
Baselines : Set
Baselines = SnapshotId → Manifest

data Override : Set where
  Inherit : Override
  Deleted : Override
  Changed : FileEntry → Override

Overlay : Set
Overlay = FilePath → Override

record WorktreeView : Set where
  field baseline : SnapshotId
        overlay : Overlay

applyOverride : Maybe FileEntry → Override → Maybe FileEntry
applyOverride base Inherit = base
applyOverride base Deleted = nothing
applyOverride base (Changed entry) = just entry

resolveView : Baselines → WorktreeView → Manifest
resolveView baselines view path =
  applyOverride (baselines (WorktreeView.baseline view) path)
                (WorktreeView.overlay view path)

-- An override must represent a real difference; unchanged entries are inherited.
DeltaRequired : Maybe FileEntry → Override → Set
DeltaRequired base Inherit = ⊤
DeltaRequired base Deleted = Σ FileEntry (λ entry → base ≡ just entry)
DeltaRequired base (Changed entry) = ¬ (base ≡ just entry)

MinimalOverlay : Manifest → Overlay → Set
MinimalOverlay base overlay = ∀ path → DeltaRequired (base path) (overlay path)

unchangedHasNoOverride : ∀ base delta → DeltaRequired base delta →
  applyOverride base delta ≡ base → delta ≡ Inherit
unchangedHasNoOverride base Inherit needed same = refl
unchangedHasNoOverride .(just entry) Deleted (entry , refl) ()
unchangedHasNoOverride base (Changed entry) needed same = ⊥-elim (needed (sym same))

deletionMasksBaseline : ∀ base → applyOverride base Deleted ≡ nothing
deletionMasksBaseline base = refl

inheritUsesBaseline : ∀ base → applyOverride base Inherit ≡ base
inheritUsesBaseline base = refl

-- Keeping a worktree's baseline fixed keeps its whole file view fixed, even
-- while new baselines are added or a different checkout advances to one.
pinnedBaselinePreservesView : ∀ before after view →
  (∀ path → before (WorktreeView.baseline view) path ≡
            after (WorktreeView.baseline view) path) →
  ∀ path → resolveView before view path ≡ resolveView after view path
pinnedBaselinePreservesView before after view stable path =
  cong (λ base → applyOverride base (WorktreeView.overlay view path)) (stable path)

Views : Set
Views = CheckoutId → Manifest

VisibleVersion : Views → CheckoutId → FilePath → VersionRef → Set
VisibleVersion views checkout path version = Σ FileEntry (λ entry →
  views checkout path ≡ just entry × FileEntry.version entry ≡ version)

record CheckoutResult (views : Views) (checkout : Checkout) : Set where
  field path : FilePath -- validated relative path
        version : VersionRef
        versionFamily : VersionRef.family version ≡ Checkout.family checkout
        analysis : FileVersion
        versionMatches : FileVersion.id analysis ≡ VersionRef.version version
        analysisFamily : FileVersion.family analysis ≡ Checkout.family checkout
        chunk : AnalyzedChunk
        chunkInVersion : chunk ∈ FileVersion.chunks analysis
        visible : VisibleVersion views (Checkout.id checkout) path version

resultPath : ∀ {views checkout} → CheckoutResult views checkout → FilePath
resultPath {checkout = checkout} result = record
  { value = FilePath.value (Checkout.root checkout) ++ "/" ++
            FilePath.value (CheckoutResult.path result) }

resultUsesSelectedManifest : ∀ views checkout (r : CheckoutResult views checkout) →
  VisibleVersion views (Checkout.id checkout)
    (CheckoutResult.path r) (CheckoutResult.version r)
resultUsesSelectedManifest views checkout r = CheckoutResult.visible r

record CheckoutEdge (views : Views) (checkout : Checkout) : Set where
  field sourcePath targetPath : FilePath
        sourceVersion targetVersion : VersionRef
        sourceVisible : VisibleVersion views (Checkout.id checkout) sourcePath sourceVersion
        targetVisible : VisibleVersion views (Checkout.id checkout) targetPath targetVersion

AnalysisCompatible : FileVersion → FileVersion → Set
AnalysisCompatible a b =
  FileVersion.family a ≡ FileVersion.family b ×
  FileVersion.analysisKey a ≡ FileVersion.analysisKey b

EmbeddingCompatible : EmbeddingArtifact → EmbeddingArtifact → Set
EmbeddingCompatible a b =
  EmbeddingArtifact.version a ≡ EmbeddingArtifact.version b ×
  EmbeddingArtifact.key a ≡ EmbeddingArtifact.key b

reuseKeepsBytes : ∀ a b → AnalysisCompatible a b →
  AnalysisKey.bytes (FileVersion.analysisKey a) ≡
  AnalysisKey.bytes (FileVersion.analysisKey b)
reuseKeepsBytes a b same = cong AnalysisKey.bytes (proj₂ same)
