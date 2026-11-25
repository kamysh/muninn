# What a worktree view identifies

A repository family can share immutable file and analysis records across its
checkouts. Each checkout has its own map from relative paths to visible
versions. This separation allows two checkouts to share unchanged work while
reporting different content at the same path.

See [checkout publication](CheckoutPublication.lagda.md) for how one view
advances and [prepared file versions](../../crates/core/src/worktrees/prepared.rs)
for the runtime lookup and reuse path.

```agda
{-# OPTIONS --safe #-}
-- A family shares immutable file versions and stable baseline manifests.
-- Each checkout selects its own view, with differences relative to a stable
-- baseline. The model gives no mandatory physical representation.
module Muninn.Worktree where

open import Data.Bool using (Bool)

open import Muninn.Types
open import Data.List using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.String using (String; _++_)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim)

```

## Separate owners, views, and stored versions

Each identifier has a distinct job. A version reference carries its family
as well as its version ID because a shared file version belongs to the
family. A checkout can refer to the version without becoming its owner.

```agda
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

-- Exact semantic input, separate from acceleration metadata.
```

## Record what makes reuse valid

Analysis depends on exact source bytes and the parser and chunking settings.
A content hash helps find candidates. Changing that hash leaves the semantic
input unchanged, which is why matching a hash alone cannot certify reuse.
Chunks carry byte positions as identities and line ranges for display.
The normalized chunk text may differ from the raw source slice. Vector reuse
therefore checks the exact normalized bytes sent to the provider and the
full profile used to interpret the vector.

```agda
record AnalysisMeaning : Set where
  field bytes : List (Fin 256)
        parserVersion grammarVersion extractorVersion : String
        chunkerVersion normalizationVersion analysisConfig language : String
        maxChunkBytes : ℕ

record AnalysisKey : Set where
  field meaning : AnalysisMeaning
        contentHash : String -- lookup aid; never proof of byte equality

analysisMeaning : AnalysisKey → AnalysisMeaning
analysisMeaning = AnalysisKey.meaning

withLookupHash : String → AnalysisKey → AnalysisKey
withLookupHash hash key = record { meaning = AnalysisKey.meaning key; contentHash = hash }

lookupHashDoesNotChangeMeaning : ∀ hash key → analysisMeaning (withLookupHash hash key) ≡ analysisMeaning key
lookupHashDoesNotChangeMeaning hash key = refl

record ByteSpan : Set where
  constructor byteSpan
  field start end : ℕ -- half-open source-byte positions [start, end)

record EmbeddingKey : Set where
  field backend model configuration : String
        profileRevision normalizationVersion task : String
        dimension : ℕ

record AnalyzedChunk : Set where
  field span : ByteSpan
        range : LineRange -- display metadata; never the identity
        content : String -- versioned normalized payload, not necessarily a raw slice

record FileVersion : Set where
  field id : VersionId
        family : FamilyId
        analysisKey : AnalysisKey
        chunks : List AnalyzedChunk

record EmbeddingArtifact : Set where
  field version : VersionRef
        span : ByteSpan
        key : EmbeddingKey
        input : List (Fin 256) -- exact normalized bytes submitted to the provider

```

## Give each checkout its own path map

The checkout has a stable ID and a root for displaying paths. Its manifest
stores the version and selection information at each visible path. A view
can be described as a stable baseline plus a small set of local changes.
An inherited path reads from that specific baseline, a deletion masks it,
and a changed entry supplies a replacement. The proofs describe the answers
that this representation must give. They allow the runtime to use direct
membership references.

```agda
record Checkout : Set where
  field id : CheckoutId
        family : FamilyId
        root : FilePath

record FileEntry : Set where
  field version : VersionRef
        tier : Tier
        gitDefault : Bool -- semantic selection metadata; receipt provenance is separate

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
```

## Record only differences from the chosen baseline

A missing baseline path needs no deletion, and an unchanged path needs no
replacement. A retained baseline is stable under updates elsewhere. The
preservation proof takes that stability as a premise and establishes that
every path in the view resolves the same way.

```agda
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

```

## Explain where a result comes from

A result must point to a chunk in the exact version selected at that path.
Its displayed path is built using the selected checkout's root. A structural
edge supplies visible versions for both endpoints. These requirements
prevent a result backed only by a retained version in another checkout from
appearing in this one.

```agda
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

```

## Share only compatible work

Analysis is reusable within the same family when its exact inputs match.
Embeddings also need equal normalized input bytes and an equal profile.
Those checks let two genuinely equivalent files reuse work while keeping a
different source version or embedding configuration out of the result.

```agda
AnalysisCompatible : FileVersion → FileVersion → Set
AnalysisCompatible a b =
  FileVersion.family a ≡ FileVersion.family b ×
  analysisMeaning (FileVersion.analysisKey a) ≡ analysisMeaning (FileVersion.analysisKey b)

EmbeddingCompatible : EmbeddingArtifact → EmbeddingArtifact → Set
EmbeddingCompatible a b =
  VersionRef.family (EmbeddingArtifact.version a) ≡ VersionRef.family (EmbeddingArtifact.version b) ×
  (EmbeddingArtifact.input a ≡ EmbeddingArtifact.input b × EmbeddingArtifact.key a ≡ EmbeddingArtifact.key b)

reuseKeepsBytes : ∀ a b → AnalysisCompatible a b →
  AnalysisMeaning.bytes (analysisMeaning (FileVersion.analysisKey a)) ≡
  AnalysisMeaning.bytes (analysisMeaning (FileVersion.analysisKey b))
reuseKeepsBytes a b same = cong AnalysisMeaning.bytes (proj₂ same)
```
