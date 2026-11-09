{-# OPTIONS --safe #-}
-- The public-entry specialization uses the same algebra as owned-row views.
module Muninn.FileMap where

import Muninn.Worktree as W
open W.FileEntries public using
  (writeFile; writeFileAtTarget; writeFileElsewhere; fileDifference; fileDifferenceResolves; fileDifferenceMinimal; normalizeFileOverlay; normalizationPreservesFileView; normalizedFileOverlayIsMinimal; normalizationIsIdempotent; overlayForFiles; fileEditResolvesAtTarget; fileEditRetainsOtherPaths; retainedFileMapView; moveBase; movingBasePreservesWorktree; movingBaseKeepsMinimalDelta)
