{-# OPTIONS --safe #-}
-- Incremental file observation with an explicit event-coverage boundary.
module Muninn.IncrementalObservation where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.List using (List; []; _∷_)
open import Data.Fin using (Fin)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)

-- Device and inode identify an observed filesystem object, not its bytes.
-- Epoch timestamps are explicitly unavailable as change hints.
record Metadata : Set where
  constructor meta
  field device inode size mtime : ℕ

record File : Set where
  constructor file
  field metadata : Metadata
        bytes : List (Fin 256)

Path : Set
Path = ℕ

-- Missing and unreadable are distinct: the latter remains pending and its
-- previous content must be hidden rather than treated as a successful delete.
data FileState : Set where
  absent unreadable : FileState
  present : File → FileState

Snapshot : Set
Snapshot = Path → FileState

different : ℕ → ℕ → Bool
different first second with first ≟ second
... | yes _ = false
... | no _ = true

or : Bool → Bool → Bool
or true _ = true
or false other = other

-- An epoch timestamp is ignored. Other timestamps may trigger a content
-- read; matching metadata never proves that contents match.
timestampChanged : ℕ → ℕ → Bool
timestampChanged zero _ = false
timestampChanged (suc _) zero = false
timestampChanged (suc first) (suc second) = different first second

metadataChanged : Metadata → Metadata → Bool
metadataChanged (meta d i s t) (meta d′ i′ s′ t′) =
  or (different d d′) (or (different i i′) (or (different s s′) (timestampChanged t t′)))

metadataHint : FileState → FileState → Bool
metadataHint absent absent = false
metadataHint (present first) (present second) = metadataChanged (File.metadata first) (File.metadata second)
metadataHint _ _ = true

-- This certificate is supplied by the filesystem/watcher adapter: every
-- path outside the reported change set really is unchanged. The model does
-- not claim that operating-system event delivery supplies such evidence.
record Covers (before after : Snapshot) (changed : Path → Bool) : Set where
  field unchangedOutside : ∀ path → changed path ≡ false → before path ≡ after path

-- A complete ordered event trace connects actual observations. Each step
-- identifies the path it can affect; a rename can contribute multiple steps.
-- The filesystem adapter must establish that the trace is complete and that
-- directory, rename, symlink, and hard-link effects have been expanded to
-- all affected selected paths.
record SingleChange (before after : Snapshot) (changed : Path) : Set where
  field unchangedOther : ∀ path → path ≢ changed → before path ≡ after path

data Trace : Snapshot → Snapshot → List Path → Set where
  finished : ∀ {snapshot} → Trace snapshot snapshot []
  step : ∀ {before middle after path rest} → SingleChange before middle path →
    Trace middle after rest → Trace before after (path ∷ rest)

reported : Path → List Path → Bool
reported path [] = false
reported path (first ∷ rest) with path ≟ first
... | yes _ = true
... | no _ = reported path rest

trueNotFalse : true ≢ false
trueNotFalse ()

unreportedUnchanged : ∀ {before after paths} → Trace before after paths → ∀ path →
  reported path paths ≡ false → before path ≡ after path
unreportedUnchanged finished path notReported = refl
unreportedUnchanged (step {path = first} {rest = rest} change trace) path notReported with path ≟ first
... | yes same = ⊥-elim (trueNotFalse notReported)
... | no different = trans (SingleChange.unchangedOther change path different)
    (unreportedUnchanged trace path notReported)

traceCovers : ∀ {before after paths} → Trace before after paths → Covers before after (λ path → reported path paths)
traceCovers trace = record { unchangedOutside = unreportedUnchanged trace }

data Observation (before after : Snapshot) : Set where
  complete : (changed : Path → Bool) → Covers before after changed → Observation before after
  uncertain : Observation before after

fromTrace : ∀ {before after paths} → Trace before after paths → Observation before after
fromTrace {paths = paths} trace = complete (λ path → reported path paths) (traceCovers trace)

needsRead : ∀ {before after} → Observation before after → Path → Bool
needsRead {before} {after} (complete changed _) path = or (changed path) (metadataHint (before path) (after path))
needsRead uncertain path = true

observed : ∀ {before after} → Observation before after → Path → FileState
observed {before} {after} observation path = if needsRead observation path then after path else before path

-- Incremental observation yields exactly the current file at every path,
-- provided the coverage certificate reflects the actual filesystem.
observationCorrect : ∀ {before after} (observation : Observation before after) path →
  observed observation path ≡ after path
observationCorrect uncertain path = refl
observationCorrect {before} {after} (complete changed coverage) path with changed path in change
... | true = refl
... | false with metadataHint (before path) (after path)
...   | true = refl
...   | false = Covers.unchangedOutside coverage path change

uncertaintyReadsAll : ∀ {before after} path → needsRead (uncertain {before} {after}) path ≡ true
uncertaintyReadsAll path = refl

reportedChangeReads : ∀ {before after} changed coverage path → changed path ≡ true →
  needsRead (complete {before} {after} changed coverage) path ≡ true
reportedChangeReads changed coverage path changedHere rewrite changedHere = refl

unchangedHintAvoidsRead : ∀ {before after : Snapshot} (changed : Path → Bool)
  (coverage : Covers before after changed) path → changed path ≡ false →
  metadataHint (before path) (after path) ≡ false →
  needsRead (complete changed coverage) path ≡ false
unchangedHintAvoidsRead changed coverage path notChanged noHint rewrite notChanged | noHint = refl

traceObservationCorrect : ∀ {before after paths} (trace : Trace before after paths) path →
  observed (fromTrace trace) path ≡ after path
traceObservationCorrect trace path = observationCorrect (fromTrace trace) path

epochNeverSignals : ∀ time → timestampChanged zero time ≡ false × timestampChanged time zero ≡ false
epochNeverSignals zero = refl , refl
epochNeverSignals (suc time) = refl , refl

-- Equal-size and equal-object changes cannot be skipped under a truthful
-- coverage certificate: differing actual files force the path to be reported.
differentFileMustBeReported : ∀ {before after} changed (coverage : Covers before after changed) path →
  before path ≢ after path → changed path ≡ true
differentFileMustBeReported changed coverage path differentFile with changed path in change
... | true = refl
... | false = ⊥-elim (differentFile (Covers.unchangedOutside coverage path change))

presentInjective : ∀ {first second} → present first ≡ present second → first ≡ second
presentInjective refl = refl

-- This applies even if device, inode, size, and timestamp are all equal.
changedBytesMustBeReported : ∀ {before after} changed (coverage : Covers before after changed)
  path first second → before path ≡ present first → after path ≡ present second →
  File.bytes first ≢ File.bytes second → changed path ≡ true
changedBytesMustBeReported changed coverage path first second was now differentBytes =
  differentFileMustBeReported changed coverage path λ same →
    differentBytes (cong File.bytes (presentInjective (trans (sym was) (trans same now))))

presentNotAbsent : ∀ value → present value ≢ absent
presentNotAbsent value ()

absentNotPresent : ∀ value → absent ≢ present value
absentNotPresent value ()

-- Renames require both affected paths to be accounted for. This applies
-- regardless of whether the underlying device/inode is preserved or replaced.
renameSourceReported : ∀ {before after} changed (coverage : Covers before after changed) path value →
  before path ≡ present value → after path ≡ absent → changed path ≡ true
renameSourceReported changed coverage path value was now =
  differentFileMustBeReported changed coverage path λ same →
    presentNotAbsent value (trans (sym was) (trans same now))

renameDestinationReported : ∀ {before after} changed (coverage : Covers before after changed) path value →
  before path ≡ absent → after path ≡ present value → changed path ≡ true
renameDestinationReported changed coverage path value was now =
  differentFileMustBeReported changed coverage path λ same →
    absentNotPresent value (trans (sym was) (trans same now))
