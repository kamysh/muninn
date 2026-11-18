{-# OPTIONS --safe #-}
-- Publish a selected checkout only with current-observation evidence.
module Muninn.IncrementalPublication where

import Muninn.IncrementalObservation as Observation
open import Muninn.IndexFsm using (GitState; Settled; Operating; Conflicted)
open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)

open Observation using (Path; File; FileState; Snapshot; absent; unreadable; present)

Checkout : Set
Checkout = ℕ
Views : Set
Views = Checkout → Path → Maybe File

View : Set
View = Path → Maybe File

content : FileState → Maybe File
content absent = nothing
content unreadable = nothing
content (present value) = just value

pending : FileState → Bool
pending unreadable = true
pending _ = false

pendingAt : (Path → Bool) → Snapshot → Path → Bool
pendingAt included snapshot path = if included path then pending (snapshot path) else false

mask : Bool → Maybe File → Maybe File
mask true value = value
mask false value = nothing

-- Visibility applies both the current selection and unreadability even when
-- an old published view is retained after an invalidated attempt.
visible : (Path → Bool) → (Checkout → Path → Bool) → Views → Checkout → Path → Maybe File
visible included blocked views checkout path =
  if blocked checkout path then nothing else mask (included path) (views checkout path)

isUnreadable : FileState → Bool
isUnreadable unreadable = true
isUnreadable _ = false

-- Derive the visibility guard from the observed state rather than allowing
-- an implementation to choose a convenient independent blocked flag.
visibleFrom : (Path → Bool) → (Checkout → Snapshot) → Views → Checkout → Path → Maybe File
visibleFrom included actual views checkout path =
  visible included (λ owner p → isUnreadable (actual owner p)) views checkout path

-- The observation adapter must establish this against the actual filesystem
-- at the publication boundary. A watcher, hash, or metadata alone is not a
-- proof of stability. An unavailable or invalidated check cannot publish.
record Stable (prepared atCommit : Snapshot) : Set where
  constructor stable
  field unchanged : ∀ path → prepared path ≡ atCommit path

-- A complete, quiet event trace supplies stability; the proof does not infer
-- that a missing event stream is complete. Lost or unobserved events must be
-- handled by the external observation adapter instead.
quietTraceStable : ∀ {prepared atCommit paths} →
  (trace : Observation.Trace prepared atCommit paths) →
  (∀ path → Observation.reported path paths ≡ false) → Stable prepared atCommit
quietTraceStable trace quiet = stable (λ path → Observation.unreportedUnchanged trace path (quiet path))

data Validation (prepared atCommit : Snapshot) : Set where
  verified : Stable prepared atCommit → Validation prepared atCommit
  invalidated : Validation prepared atCommit

replace : Views → Checkout → View → Views
replace before selected value checkout with checkout ≟ selected
... | yes _ = value
... | no _ = before checkout

selectedReplaced : ∀ before selected value path → replace before selected value selected path ≡ value path
selectedReplaced before selected value path with selected ≟ selected
... | yes _ = refl
... | no different = ⊥-elim (different refl)

otherPreserved : ∀ before selected value other → other ≢ selected → ∀ path →
  replace before selected value other path ≡ before other path
otherPreserved before selected value other distinct path with other ≟ selected
... | yes same = ⊥-elim (distinct same)
... | no _ = refl

publish : ∀ {baseline prepared atCommit} → Views → Checkout → (Path → Bool) → GitState →
  Observation.Observation baseline prepared → Validation prepared atCommit → Views
publish before selected included Settled observation (verified _) =
  replace before selected (λ path → mask (included path) (content (Observation.observed observation path)))
publish before selected included Settled observation invalidated = before
publish before selected included Operating observation validation = before
publish before selected included Conflicted observation validation = before

-- The current revision must be read from the authoritative policy pointer
-- inside the publication transaction. A stale plan retains the existing view.
guardedPublish : ∀ {baseline prepared atCommit} → Views → Checkout → (Path → Bool) →
  ℕ → ℕ → GitState → Observation.Observation baseline prepared → Validation prepared atCommit → Views
guardedPublish before selected included expected current git observation validation with expected ≟ current
... | yes _ = publish before selected included git observation validation
... | no _ = before

stalePolicyRetainsAll : ∀ {baseline prepared atCommit} before selected included expected current git
  (observation : Observation.Observation baseline prepared) (validation : Validation prepared atCommit) →
  expected ≢ current → ∀ checkout path →
  guardedPublish before selected included expected current git observation validation checkout path ≡ before checkout path
stalePolicyRetainsAll before selected included expected current git observation validation different checkout path with expected ≟ current
... | yes same = ⊥-elim (different same)
... | no _ = refl

currentPolicyUsesPublication : ∀ {baseline prepared atCommit} before selected included revision git
  (observation : Observation.Observation baseline prepared) (validation : Validation prepared atCommit) checkout path →
  guardedPublish before selected included revision revision git observation validation checkout path ≡
  publish before selected included git observation validation checkout path
currentPolicyUsesPublication before selected included revision git observation validation checkout path with revision ≟ revision
... | yes _ = refl
... | no different = ⊥-elim (different refl)

-- Successful publication reflects current bytes and selection for every path,
-- including when only some paths were read. The stability evidence is explicit.
publishedCurrent : ∀ {baseline prepared atCommit} before selected included
  (observation : Observation.Observation baseline prepared) (stableNow : Stable prepared atCommit) path →
  publish before selected included Settled observation (verified stableNow) selected path ≡
    mask (included path) (content (atCommit path))
publishedCurrent before selected included observation stableNow path =
  trans (selectedReplaced before selected _ path)
    (cong (λ state → mask (included path) (content state))
      (trans (Observation.observationCorrect observation path) (Stable.unchanged stableNow path)))

guardedPublishedCurrent : ∀ {baseline prepared atCommit} before selected included revision
  (observation : Observation.Observation baseline prepared) (stableNow : Stable prepared atCommit) path →
  guardedPublish before selected included revision revision Settled observation (verified stableNow) selected path ≡
    mask (included path) (content (atCommit path))
guardedPublishedCurrent before selected included revision observation stableNow path =
  trans (currentPolicyUsesPublication before selected included revision Settled observation (verified stableNow) selected path)
    (publishedCurrent before selected included observation stableNow path)

excludedAbsent : ∀ {baseline prepared atCommit} before selected included
  (observation : Observation.Observation baseline prepared) (stableNow : Stable prepared atCommit) path →
  included path ≡ false → publish before selected included Settled observation (verified stableNow) selected path ≡ nothing
excludedAbsent before selected included observation stableNow path excluded
  rewrite publishedCurrent before selected included observation stableNow path | excluded = refl

otherCheckoutPreserved : ∀ {baseline prepared atCommit} before selected included git
  (observation : Observation.Observation baseline prepared) (validation : Validation prepared atCommit)
  other → other ≢ selected → ∀ path →
  publish before selected included git observation validation other path ≡ before other path
otherCheckoutPreserved before selected included Settled observation (verified stableNow) other distinct path =
  otherPreserved before selected _ other distinct path
otherCheckoutPreserved before selected included Settled observation invalidated other distinct path = refl
otherCheckoutPreserved before selected included Operating observation validation other distinct path = refl
otherCheckoutPreserved before selected included Conflicted observation validation other distinct path = refl

invalidatedRetainsAll : ∀ {baseline prepared atCommit : Snapshot} before selected included git
  (observation : Observation.Observation baseline prepared) checkout path →
  publish {baseline} {prepared} {atCommit} before selected included git observation invalidated checkout path ≡ before checkout path
invalidatedRetainsAll before selected included Settled observation checkout path = refl
invalidatedRetainsAll before selected included Operating observation checkout path = refl
invalidatedRetainsAll before selected included Conflicted observation checkout path = refl

gitOperationRetainsView : ∀ {baseline prepared atCommit} before selected included
  (observation : Observation.Observation baseline prepared) (validation : Validation prepared atCommit) checkout path →
  publish before selected included Operating observation validation checkout path ≡ before checkout path
gitOperationRetainsView before selected included observation validation checkout path = refl

gitConflictRetainsView : ∀ {baseline prepared atCommit} before selected included
  (observation : Observation.Observation baseline prepared) (validation : Validation prepared atCommit) checkout path →
  publish before selected included Conflicted observation validation checkout path ≡ before checkout path
gitConflictRetainsView before selected included observation validation checkout path = refl

unreadableHidden : ∀ included blocked views checkout path → blocked checkout path ≡ true →
  visible included blocked views checkout path ≡ nothing
unreadableHidden included blocked views checkout path isBlocked rewrite isBlocked = refl

observedUnreadableHidden : ∀ included actual views checkout path → actual checkout path ≡ unreadable →
  visibleFrom included actual views checkout path ≡ nothing
observedUnreadableHidden included actual views checkout path unreadableAt rewrite unreadableAt = refl

excludedHidden : ∀ included blocked views checkout path → included path ≡ false →
  visible included blocked views checkout path ≡ nothing
excludedHidden included blocked views checkout path excluded with blocked checkout path
... | true = refl
... | false rewrite excluded = refl

unreadableRemainsPending : ∀ included snapshot path → included path ≡ true →
  snapshot path ≡ unreadable → pendingAt included snapshot path ≡ true
unreadableRemainsPending included snapshot path selected blocked rewrite selected | blocked = refl

excludedNotPending : ∀ included snapshot path → included path ≡ false →
  pendingAt included snapshot path ≡ false
excludedNotPending included snapshot path excluded rewrite excluded = refl

-- A lost event forces complete observation; publishing still requires the
-- separate stability certificate at the commit boundary.
lostEventsReadAll : ∀ {baseline prepared : Snapshot} path →
  Observation.needsRead (Observation.uncertain {baseline} {prepared}) path ≡ true
lostEventsReadAll {baseline} {prepared} path = Observation.uncertaintyReadsAll {baseline} {prepared} path
