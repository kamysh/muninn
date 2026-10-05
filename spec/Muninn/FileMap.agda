{-# OPTIONS --safe #-}
-- Extensional file-map operations over mathematical lookup functions.
-- These laws prescribe no physical storage representation.
module Muninn.FileMap where

open import Muninn.Types using (FilePath)
open import Muninn.Worktree using
  (FileEntry; Manifest; Overlay; Override; Inherit; Deleted; Changed;
   applyOverride; DeltaRequired; MinimalOverlay)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

writeFile : ((a b : FilePath) → Dec (a ≡ b)) →
  FilePath → Maybe FileEntry → Manifest → Manifest
writeFile eq target value files path with eq target path
... | yes _ = value
... | no _ = files path

writeFileAtTarget : ∀ eq target value files →
  writeFile eq target value files target ≡ value
writeFileAtTarget eq target value files with eq target target
... | yes _ = refl
... | no distinct = ⊥-elim (distinct refl)

writeFileElsewhere : ∀ eq target other value files →
  ¬ (target ≡ other) → writeFile eq target value files other ≡ files other
writeFileElsewhere eq target other value files distinct with eq target other
... | yes same = ⊥-elim (distinct same)
... | no _ = refl

-- Equality is decided on the complete entry (family/version AND tier).
-- Absence/inheritance is distinct from an explicit deletion of a baseline file.
fileDifference : ((a b : Maybe FileEntry) → Dec (a ≡ b)) →
  Maybe FileEntry → Maybe FileEntry → Override
fileDifference eq base desired with eq base desired
... | yes _ = Inherit
... | no _ with desired
...   | nothing = Deleted
...   | just entry = Changed entry

fileDifferenceResolves : ∀ eq base desired →
  applyOverride base (fileDifference eq base desired) ≡ desired
fileDifferenceResolves eq base desired with eq base desired
... | yes same = same
... | no _ with desired
...   | nothing = refl
...   | just entry = refl

fileDifferenceMinimal : ∀ eq base desired →
  DeltaRequired base (fileDifference eq base desired)
fileDifferenceMinimal eq base desired with eq base desired
... | yes _ = tt
... | no different with base | desired
...   | nothing | nothing = ⊥-elim (different refl)
...   | just entry | nothing = entry , refl
...   | base | just entry = different

normalizeFileOverlay : ((a b : Maybe FileEntry) → Dec (a ≡ b)) →
  Manifest → Overlay → Overlay
normalizeFileOverlay eq base overlay path =
  fileDifference eq (base path) (applyOverride (base path) (overlay path))

normalizationPreservesFileView : ∀ eq base overlay path →
  applyOverride (base path) (normalizeFileOverlay eq base overlay path) ≡
  applyOverride (base path) (overlay path)
normalizationPreservesFileView eq base overlay path =
  fileDifferenceResolves eq (base path) (applyOverride (base path) (overlay path))

normalizedFileOverlayIsMinimal : ∀ eq base overlay →
  MinimalOverlay base (normalizeFileOverlay eq base overlay)
normalizedFileOverlayIsMinimal eq base overlay path =
  fileDifferenceMinimal eq (base path) (applyOverride (base path) (overlay path))

normalizationIsIdempotent : ∀ eq base overlay path →
  normalizeFileOverlay eq base (normalizeFileOverlay eq base overlay) path ≡
  normalizeFileOverlay eq base overlay path
normalizationIsIdempotent eq base overlay path =
  cong (fileDifference eq (base path))
    (normalizationPreservesFileView eq base overlay path)

-- Build differences against one fixed baseline, for any effective file map.
overlayForFiles : ((a b : Maybe FileEntry) → Dec (a ≡ b)) →
  Manifest → Manifest → Overlay
overlayForFiles eq base files path = fileDifference eq (base path) (files path)

fileEditResolvesAtTarget : ∀ pathEq entryEq base files target desired →
  applyOverride (base target)
    (overlayForFiles entryEq base (writeFile pathEq target desired files) target) ≡ desired
fileEditResolvesAtTarget pathEq entryEq base files target desired =
  trans (fileDifferenceResolves entryEq (base target)
          (writeFile pathEq target desired files target))
        (writeFileAtTarget pathEq target desired files)

fileEditRetainsOtherPaths : ∀ pathEq entryEq base files target other desired →
  ¬ (target ≡ other) →
  applyOverride (base other)
    (overlayForFiles entryEq base (writeFile pathEq target desired files) other) ≡ files other
fileEditRetainsOtherPaths pathEq entryEq base files target other desired distinct =
  trans (fileDifferenceResolves entryEq (base other)
          (writeFile pathEq target desired files other))
        (writeFileElsewhere pathEq target other desired files distinct)

-- A retained baseline/view has the same meaning after another baseline is
-- extended elsewhere. Equality of the referenced entries, not a branch name,
-- supplies the premise. The whole overlay remains fixed.
retainedFileMapView : ∀ (before after : Manifest) (overlay : Overlay) →
  (∀ path → before path ≡ after path) → ∀ path →
  applyOverride (before path) (overlay path) ≡ applyOverride (after path) (overlay path)
retainedFileMapView before after overlay same path =
  cong (λ entry → applyOverride entry (overlay path)) (same path)

-- Current runtime: move the single base and recalculate file differences.
-- This changes representation while retaining each checkout's effective view.
moveBase : ((a b : Maybe FileEntry) → Dec (a ≡ b)) →
  Manifest → Manifest → Overlay → Overlay
moveBase eq before after overlay path =
  fileDifference eq (after path) (applyOverride (before path) (overlay path))

movingBasePreservesWorktree : ∀ eq before after overlay path →
  applyOverride (after path) (moveBase eq before after overlay path) ≡
  applyOverride (before path) (overlay path)
movingBasePreservesWorktree eq before after overlay path =
  fileDifferenceResolves eq (after path) (applyOverride (before path) (overlay path))

movingBaseKeepsMinimalDelta : ∀ eq before after overlay →
  MinimalOverlay after (moveBase eq before after overlay)
movingBaseKeepsMinimalDelta eq before after overlay path =
  fileDifferenceMinimal eq (after path) (applyOverride (before path) (overlay path))
