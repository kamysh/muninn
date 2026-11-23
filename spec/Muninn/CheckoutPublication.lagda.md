# How worktrees publish and share indexes

A repository family shares file versions and analysis. Each Git checkout
publishes its own view of that shared data. If the primary checkout edits a
file and publishes a new version, a linked worktree can keep returning its
earlier version until its own files change and its next view is published.

[Publication requirements](../CHECKOUT-PUBLICATION.md) · [Rust reconciliation](../../crates/core/src/worktrees/mod.rs) · [Persistence tests](../../crates/core/tests/family_persistence/worktrees.rs)

## Shared versions and separate views

A checkout slot holds its published snapshot and a generation number used to
detect intervening publications. A snapshot describes the files and
structural relationships a reader can see together. A family supplies a slot
for each checkout and keeps the active selection policy. `commit` replaces
just the target slot, and `siblingUntouched` preserves the entire slot for
every other checkout. The storage model supplies the validity laws for the
versions referenced by those slots.

```agda
{-# OPTIONS --safe #-}
module Muninn.CheckoutPublication where

import Muninn.ArtifactIdentity as Identity
import Muninn.ReusePolicy as Reuse
import Muninn.Storage as Storage
import Muninn.Worktree as W
open import Muninn.IndexFsm using (GitState; Settled; Operating; Conflicted)
open import Muninn.Types using (FilePath)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open import Relation.Nullary using (yes; no)

-- An ordinary search or publication never owns this barrier. It is reserved
-- for replacement or removal of the storage on which checkout views depend.
data StorageTransition : Set where
  replaceStorage removeStorage : StorageTransition

data Availability : Set where
  online : Availability
  quiescing : StorageTransition → Availability

record Policy : Set where
  constructor policy
  field revision : ℕ
        admits : W.CheckoutId → FilePath → W.FileEntry → Bool

record Slot (baselines : W.Baselines) : Set where
  constructor slot
  field generation : ℕ
        snapshot : Maybe (Storage.PublishedSnapshot baselines)

record Family (baselines : W.Baselines) : Set where
  constructor family
  field availability : Availability
        storageGeneration : ℕ
        selection : Policy
        current : W.CheckoutId → Slot baselines

-- Slot replacement never writes the immutable baseline or file-version stores.
-- The existing Storage validity laws govern all referenced objects.
commit : ∀ {baselines} → Family baselines → W.CheckoutId →
  Storage.PublishedSnapshot baselines → Family baselines
commit {baselines} (family state storage rules slots) target next = family state storage rules replace
  where
  replace : W.CheckoutId → Slot baselines
  replace checkout with Identity.CheckoutId? target checkout
  ... | yes _ = slot (suc (Slot.generation (slots target))) (just next)
  ... | no _ = slots checkout

targetAdvanced : ∀ {baselines} (before : Family baselines) target next →
  Family.current (commit before target next) target ≡
    slot (suc (Slot.generation (Family.current before target))) (just next)
targetAdvanced (family state storage rules slots) target next with Identity.CheckoutId? target target
... | yes _ = refl
... | no different = ⊥-elim (different refl)

siblingUntouched : ∀ {baselines} (before : Family baselines) target next sibling →
  target ≢ sibling → Family.current (commit before target next) sibling ≡ Family.current before sibling
siblingUntouched (family state storage rules slots) target next sibling different
  with Identity.CheckoutId? target sibling
... | yes same = ⊥-elim (different same)
... | no _ = refl

```

## When a new view can publish

Preparation observes the checkout generation, policy revision and storage
generation. Publication compares those observations with the current state
and requires settled Git state. A merge or rebase in progress, a conflict, or
a stale observation prevents the proposed view from replacing the last
published view. The caller also supplies evidence that the new snapshot and
its references are valid.

An intervening publication in a different checkout preserves admission when
these premises still hold. `independentCommitsCommute` compares the final
slot for every checkout after two distinct commits in either order.

```agda
record Observation : Set where
  constructor observed
  field generation policyRevision storageGeneration : ℕ
        git : GitState

-- These equalities are checked inside the atomic selector update, against the
-- actual checkout slot and family policy. File/graph correctness and reference
-- readiness are independent obligations of the existing publication models.
record CanPublish {baselines} (before : Family baselines) (target : W.CheckoutId)
  (evidence : Observation) : Set where
  constructor canPublish
  field storageOnline : Family.availability before ≡ online
        sameStorage : Family.storageGeneration before ≡ Observation.storageGeneration evidence
        sameGeneration : Slot.generation (Family.current before target) ≡ Observation.generation evidence
        samePolicy : Policy.revision (Family.selection before) ≡ Observation.policyRevision evidence
        gitSettled : Observation.git evidence ≡ Settled

data PublicationDecision {baselines} (before : Family baselines) target evidence : Set where
  ready : CanPublish before target evidence → PublicationDecision before target evidence
  storageChanging : ∀ reason → Family.availability before ≡ quiescing reason →
    PublicationDecision before target evidence
  refreshStorage : Family.storageGeneration before ≢ Observation.storageGeneration evidence →
    PublicationDecision before target evidence
  retainDuringGit : Observation.git evidence ≢ Settled → PublicationDecision before target evidence
  refreshPolicy : Policy.revision (Family.selection before) ≢ Observation.policyRevision evidence →
    PublicationDecision before target evidence
  refreshCheckout : Slot.generation (Family.current before target) ≢ Observation.generation evidence →
    PublicationDecision before target evidence

decide : ∀ {baselines} (before : Family baselines) target evidence → PublicationDecision before target evidence
decide (family (quiescing reason) storage rules slots) target evidence = storageChanging reason refl
decide (family online storage rules slots) target (observed generation revision expectedStorage Operating) =
  retainDuringGit (λ ())
decide (family online storage rules slots) target (observed generation revision expectedStorage Conflicted) =
  retainDuringGit (λ ())
decide (family online storage rules slots) target (observed generation revision expectedStorage Settled)
  with storage ≟ expectedStorage | Policy.revision rules ≟ revision | Slot.generation (slots target) ≟ generation
... | no stale | _ | _ = refreshStorage stale
... | yes _ | no stale | _ = refreshPolicy stale
... | yes _ | yes _ | no stale = refreshCheckout stale
... | yes storageCurrent | yes policyCurrent | yes checkoutCurrent =
  ready (canPublish refl storageCurrent checkoutCurrent policyCurrent refl)

publish : ∀ {baselines} (before : Family baselines) target evidence →
  CanPublish before target evidence → ∀ artifacts owner (next : Storage.PublishedSnapshot baselines) →
  Storage.ValidSnapshot artifacts owner baselines next → Family baselines
publish before target evidence admitted artifacts owner next valid = commit before target next

staleCheckoutRefuses : ∀ {baselines} (before : Family baselines) target evidence →
  Slot.generation (Family.current before target) ≢ Observation.generation evidence →
  CanPublish before target evidence → ⊥
staleCheckoutRefuses before target evidence stale admitted = stale (CanPublish.sameGeneration admitted)

stalePolicyRefuses : ∀ {baselines} (before : Family baselines) target evidence →
  Policy.revision (Family.selection before) ≢ Observation.policyRevision evidence →
  CanPublish before target evidence → ⊥
stalePolicyRefuses before target evidence stale admitted = stale (CanPublish.samePolicy admitted)

staleStorageRefuses : ∀ {baselines} (before : Family baselines) target evidence →
  Family.storageGeneration before ≢ Observation.storageGeneration evidence →
  CanPublish before target evidence → ⊥
staleStorageRefuses before target evidence stale admitted = stale (CanPublish.sameStorage admitted)

blockedGitRefuses : ∀ {baselines} (before : Family baselines) target evidence →
  Observation.git evidence ≢ Settled → CanPublish before target evidence → ⊥
blockedGitRefuses before target evidence blocked admitted = blocked (CanPublish.gitSettled admitted)

admissionSurvivesSibling : ∀ {baselines} (before : Family baselines) target sibling next evidence →
  sibling ≢ target → CanPublish before target evidence →
  CanPublish (commit before sibling next) target evidence
admissionSurvivesSibling before@(family state storage rules slots) target sibling next evidence different admitted =
  canPublish (CanPublish.storageOnline admitted)
    (CanPublish.sameStorage admitted)
    (trans (cong Slot.generation (siblingUntouched before sibling next target different))
      (CanPublish.sameGeneration admitted))
    (CanPublish.samePolicy admitted) (CanPublish.gitSettled admitted)

-- Pointwise equality states independence without assuming function extensionality.
byCheckoutEquality : ∀ {Result : Set} first second →
  (first ≡ second → Result) → (first ≢ second → Result) → Result
byCheckoutEquality first second same different with Identity.CheckoutId? first second
... | yes equal = same equal
... | no unequal = different unequal

independentCommitsCommute : ∀ {baselines} (before : Family baselines) first second firstView secondView →
  first ≢ second → ∀ checkout →
  Family.current (commit (commit before first firstView) second secondView) checkout ≡
  Family.current (commit (commit before second secondView) first firstView) checkout
independentCommitsCommute before first second firstView secondView different checkout =
  byCheckoutEquality first checkout onFirst
    (λ notFirst → byCheckoutEquality second checkout (onSecond notFirst) (onNeither notFirst))
  where
  afterFirst = commit before first firstView
  afterSecond = commit before second secondView
  Result : W.CheckoutId → Set
  Result selected = Family.current (commit afterFirst second secondView) selected ≡
    Family.current (commit afterSecond first firstView) selected

  onFirst : first ≡ checkout → Result checkout
  onFirst refl =
    trans (siblingUntouched afterFirst second secondView first (λ same → different (sym same)))
      (trans (targetAdvanced before first firstView)
        (sym (trans (targetAdvanced afterSecond first firstView)
          (cong (λ prior → slot (suc (Slot.generation prior)) (just firstView))
            (siblingUntouched before second secondView first (λ same → different (sym same)))))))

  onSecond : first ≢ checkout → second ≡ checkout → Result checkout
  onSecond notFirst refl =
    trans (targetAdvanced afterFirst second secondView)
      (trans (cong (λ prior → slot (suc (Slot.generation prior)) (just secondView))
          (siblingUntouched before first firstView second notFirst))
        (sym (trans (siblingUntouched afterSecond first firstView second notFirst)
          (targetAdvanced before second secondView))))

  onNeither : first ≢ checkout → second ≢ checkout → Result checkout
  onNeither notFirst notSecond =
    trans (siblingUntouched afterFirst second secondView checkout notSecond)
      (trans (siblingUntouched before first firstView checkout notFirst)
        (sym (trans (siblingUntouched afterSecond first firstView checkout notFirst)
          (siblingUntouched before second secondView checkout notSecond))))

```

## Searches while indexing continues

An online family serves the selected checkout's published snapshot even if
other work is preparing a replacement. If the checkout has yet to publish,
the search follows the [first-search contract](FirstSearch.lagda.md).
`searchSurvivesSiblingCommit` preserves the search admission decision when
a sibling publishes. Storage replacement and destructive removal have a
separate transition that can temporarily suspend access.

```agda
data SearchStart (baselines : W.Baselines) : Set where
  usePublished : Storage.PublishedSnapshot baselines → SearchStart baselines
  needsFirstView : SearchStart baselines
  storageTransition : StorageTransition → SearchStart baselines

startSearch : ∀ {baselines} → Family baselines → W.CheckoutId → SearchStart baselines
startSearch (family (quiescing reason) storage rules slots) checkout = storageTransition reason
startSearch (family online storage rules slots) checkout with Slot.snapshot (slots checkout)
... | just snapshot = usePublished snapshot
... | nothing = needsFirstView

onlineSearchUsesPublished : ∀ {baselines} (before : Family baselines) checkout snapshot →
  Family.availability before ≡ online →
  Slot.snapshot (Family.current before checkout) ≡ just snapshot →
  startSearch before checkout ≡ usePublished snapshot
onlineSearchUsesPublished (family online storage rules slots) checkout snapshot refl stored
  rewrite stored = refl

onlineSearchKeepsFirstViewIntent : ∀ {baselines} (before : Family baselines) checkout →
  Family.availability before ≡ online →
  Slot.snapshot (Family.current before checkout) ≡ nothing →
  startSearch before checkout ≡ needsFirstView
onlineSearchKeepsFirstViewIntent (family online storage rules slots) checkout refl missing
  rewrite missing = refl

searchSurvivesSiblingCommit : ∀ {baselines} (before : Family baselines) target next checkout →
  target ≢ checkout → startSearch (commit before target next) checkout ≡ startSearch before checkout
searchSurvivesSiblingCommit (family (quiescing reason) storage rules slots) target next checkout different = refl
searchSurvivesSiblingCommit before@(family online storage rules slots) target next checkout different
  with Family.current (commit before target next) checkout
     | siblingUntouched before target next checkout different
... | .(slots checkout) | refl = refl

```

## Apply selection to search results

A query can hold a previously selected snapshot. Results must still satisfy
the current selection policy when they are materialized. For example, a new
exclusion hides the file as soon as the policy takes effect, even while
cleanup still has to reclaim the older data.

The checked laws preserve snapshot references across policy acceptance and
show that `visible` filters an excluded file. The runtime must establish
which rules apply and make the corresponding observations consistently.

```agda
-- Re-authorize a pinned snapshot against current selection when materializing
-- results. A cleanup or policy update cannot leak an excluded saved entry.
visible : ∀ {baselines} → Family baselines → W.CheckoutId →
  Storage.PublishedSnapshot baselines → W.Manifest
visible {baselines} before checkout snapshot path with W.resolveView baselines (Storage.PublishedSnapshot.view snapshot) path
... | nothing = nothing
... | just entry with Policy.admits (Family.selection before) checkout path entry
...   | true = just entry
...   | false = nothing

excludedFromPinnedView : ∀ {baselines} (before : Family baselines) checkout snapshot path →
  (∀ entry → Policy.admits (Family.selection before) checkout path entry ≡ false) →
  visible before checkout snapshot path ≡ nothing
excludedFromPinnedView {baselines} before checkout snapshot path excluded
  with W.resolveView baselines (Storage.PublishedSnapshot.view snapshot) path
... | nothing = refl
... | just entry rewrite excluded entry = refl

acceptPolicy : ∀ {baselines} → Family baselines → (W.CheckoutId → FilePath → W.FileEntry → Bool) → Family baselines
acceptPolicy (family state storage rules slots) admits =
  family state storage (policy (suc (Policy.revision rules)) admits) slots

policyAcceptanceKeepsReferences : ∀ {baselines} (before : Family baselines) admits checkout →
  Family.current (acceptPolicy before admits) checkout ≡ Family.current before checkout
policyAcceptanceKeepsReferences (family state storage rules slots) admits checkout = refl

policyAcceptanceKeepsAdmission : ∀ {baselines} (before : Family baselines) admits checkout →
  startSearch (acceptPolicy before admits) checkout ≡ startSearch before checkout
policyAcceptanceKeepsAdmission (family (quiescing reason) storage rules slots) admits checkout = refl
policyAcceptanceKeepsAdmission (family online storage rules slots) admits checkout
  with Slot.snapshot (slots checkout)
... | nothing = refl
... | just snapshot = refl

```

## Resume from completed file work

For each path, the model compares the saved file version's analysis input
with a fresh observation, including compatibility of analysis settings.
Matching input keeps the saved version. Changed or missing input invalidates
the saved preparation for that path. This is a per-path decision, so an edit
to one file leaves compatible work from other files available.

The file and Git observations, the atomic publication transaction and the
lifetime of referenced storage are runtime obligations. The propositions
below establish when prepared work is reusable. They supply no bound on
when indexing finishes.

```agda
-- The checkout observation supplies new exact analysis inputs. Git evidence,
-- checked against the current worktree, and verified bytes can supply that
-- observation. A commit ID or matching metadata alone cannot certify bytes.
Prepared : Set
Prepared = FilePath → Maybe W.FileVersion

continueFile : Maybe W.FileVersion → Maybe Reuse.AnalysisInput → Maybe W.FileVersion
continueFile (just saved) (just current) with Reuse.analysisInput? (Reuse.analysisOf saved) current
... | yes _ = just saved
... | no _ = nothing
continueFile _ _ = nothing

continue : Prepared → (FilePath → Maybe Reuse.AnalysisInput) → Prepared
continue prepared current path = continueFile (prepared path) (current path)

compatiblePreparationSurvives : ∀ prepared current path saved →
  prepared path ≡ just saved → current path ≡ just (Reuse.analysisOf saved) →
  continue prepared current path ≡ just saved
compatiblePreparationSurvives prepared current path saved recorded inputFound
  rewrite recorded | inputFound with Reuse.analysisInput? (Reuse.analysisOf saved) (Reuse.analysisOf saved)
... | yes _ = refl
... | no unequal = ⊥-elim (unequal refl)

changedInputReopensOnlyThatPath : ∀ prepared current path saved input →
  prepared path ≡ just saved → current path ≡ just input → Reuse.analysisOf saved ≢ input →
  continue prepared current path ≡ nothing
changedInputReopensOnlyThatPath prepared current path saved input recorded inputFound distinct
  rewrite recorded | inputFound with Reuse.analysisInput? (Reuse.analysisOf saved) input
... | yes same = ⊥-elim (distinct same)
... | no _ = refl

missingInputCannotPublishSaved : ∀ prepared current path →
  current path ≡ nothing → continue prepared current path ≡ nothing
missingInputCannotPublishSaved prepared current path missing rewrite missing with prepared path
... | just saved = refl
... | nothing = refl
```
