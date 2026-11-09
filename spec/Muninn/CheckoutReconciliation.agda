{-# OPTIONS --safe #-}
-- A total publication transition. Unreadable files do not become job failures;
-- their data is hidden, work stays visible, and independent files advance.
module Muninn.CheckoutReconciliation where

import Muninn.ContentViews as Content
import Muninn.ExclusionOutcomes as E
import Muninn.IndexFsm as F
import Muninn.Dialogue as D
open import Muninn.Types using (FilePath)
open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true; false)
open import Data.String using (String; _++_)
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Maybe.Properties using (just-injective)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

-- Content and structural results belong to the same completed file version.
-- Removing this one value hides BOTH; no structural-only stale entry remains.
record Artifact : Set where
  constructor artifact
  field file : Content.Entry
        symbols edges : List ℕ

View : Set
View = FilePath → Maybe Artifact

record ReadProblem : Set where
  constructor unreadableBecause
  field gitDefault : Bool
        reason : D.Text

Waiting : Set
Waiting = FilePath → Maybe ReadProblem

data Change : Set where
  unchanged removed : Change
  indexed : Artifact → Change
  unreadable : ReadProblem → Change

-- A path has one observation in the completed inventory. This is an
-- extensional logical map, not an instruction to traverse infinitely many paths.
Changes : Set
Changes = FilePath → Change

record State : Set where
  constructor state
  field published : Maybe View
        waiting : Waiting
        git : F.GitState

initial : F.GitState → State
initial git = state nothing (λ path → nothing) git

previousFiles : Maybe View → View
previousFiles nothing path = nothing
previousFiles (just files) path = files path

fileChange : Change → Maybe Artifact → Maybe Artifact
fileChange unchanged previous = previous
fileChange removed previous = nothing
fileChange (indexed ready) previous = just ready
fileChange (unreadable problem) previous = nothing

workChange : Change → Maybe ReadProblem → Maybe ReadProblem
workChange unchanged previous = previous
workChange removed previous = nothing
workChange (indexed ready) previous = nothing
workChange (unreadable problem) previous = just problem

fileQuestion : FilePath → ReadProblem → D.Question
fileQuestion path problem = D.prerequisite
  (D.text 'I' (" cannot read " ++ FilePath.value path ++ ": " ++ D.render (ReadProblem.reason problem) ++
    ". Its old indexed contents and relationships are hidden. Other readable files continue indexing."))
  (D.text 'C' "heck access permissions or restore the file, then let indexing retry. If the file should not be indexed, explicitly exclude it in the family policy. This work remains pending until it is readable, removed, or excluded.")

module Family (selection : E.Rule) where
  module M = E.Model
  owner = E.targetOwner selection

  included : Bool → FilePath → Bool
  included ignored path = M.includedWithGit selection owner ignored (FilePath.value path)

  keepFile : FilePath → Maybe Artifact → Maybe Artifact
  keepFile path nothing = nothing
  keepFile path value@(just saved) with included (Content.Entry.gitDefault (Artifact.file saved)) path
  ... | true = value
  ... | false = nothing

  keepWork : FilePath → Maybe ReadProblem → Maybe ReadProblem
  keepWork path nothing = nothing
  keepWork path value@(just problem) with included (ReadProblem.gitDefault problem) path
  ... | true = value
  ... | false = nothing

  filterView : Maybe View → Maybe View
  filterView nothing = nothing
  filterView (just files) = just (λ path → keepFile path (files path))

  filterWaiting : Waiting → Waiting
  filterWaiting waiting path = keepWork path (waiting path)

  -- Policy-only refresh needs neither an indexing pass nor settled Git, so it
  -- also applies to paused checkouts without creating an initial publication.
  refreshPolicy : State → State
  refreshPolicy before = state (filterView (State.published before)) (filterWaiting (State.waiting before)) (State.git before)

  refreshFleet : (ℕ → State) → ℕ → State
  refreshFleet fleet checkout = refreshPolicy (fleet checkout)

  policyKeepsGit : ∀ before → State.git (refreshPolicy before) ≡ State.git before
  policyKeepsGit before = refl

  policyCannotInitialize : ∀ before → State.published before ≡ nothing → State.published (refreshPolicy before) ≡ nothing
  policyCannotInitialize before absent rewrite absent = refl

  settledFiles : State → Changes → View
  settledFiles before changes path = keepFile path
    (fileChange (changes path) (previousFiles (State.published before) path))

  settledWork : State → Changes → Waiting
  settledWork before changes path = keepWork path (workChange (changes path) (State.waiting before path))

  reconcile : F.GitState → State → Changes → State
  reconcile F.Settled before changes = state (just (settledFiles before changes)) (settledWork before changes) F.Settled
  reconcile F.Operating before changes = state (filterView (State.published before)) (filterWaiting (State.waiting before)) F.Operating
  reconcile F.Conflicted before changes = state (filterView (State.published before)) (filterWaiting (State.waiting before)) F.Conflicted

  files : State → View
  files current = previousFiles (State.published current)

  notice : State → FilePath → Maybe D.Question
  notice current path with State.waiting current path
  ... | nothing = nothing
  ... | just problem = just (fileQuestion path problem)

  keepIncluded : ∀ path saved → included (Content.Entry.gitDefault (Artifact.file saved)) path ≡ true →
    keepFile path (just saved) ≡ just saved
  keepIncluded path saved allowed rewrite allowed = refl

  keepExcluded : ∀ path saved → included (Content.Entry.gitDefault (Artifact.file saved)) path ≡ false →
    keepFile path (just saved) ≡ nothing
  keepExcluded path saved excluded rewrite excluded = refl

  workIncluded : ∀ path problem → included (ReadProblem.gitDefault problem) path ≡ true →
    keepWork path (just problem) ≡ just problem
  workIncluded path problem allowed rewrite allowed = refl

  -- There is no condition on any peer file. Each ready path advances even if
  -- every other selected path has unresolved read work.
  readableAdvances : ∀ before changes path ready → changes path ≡ indexed ready →
    included (Content.Entry.gitDefault (Artifact.file ready)) path ≡ true →
    files (reconcile F.Settled before changes) path ≡ just ready
  readableAdvances before changes path ready observed allowed rewrite observed = keepIncluded path ready allowed

  unreadableHidden : ∀ before changes path problem → changes path ≡ unreadable problem →
    files (reconcile F.Settled before changes) path ≡ nothing
  unreadableHidden before changes path problem observed rewrite observed = refl

  unreadablePending : ∀ before changes path problem → changes path ≡ unreadable problem →
    included (ReadProblem.gitDefault problem) path ≡ true →
    State.waiting (reconcile F.Settled before changes) path ≡ just problem
  unreadablePending before changes path problem observed allowed rewrite observed = workIncluded path problem allowed

  unreadableExplained : ∀ before changes path problem → changes path ≡ unreadable problem →
    included (ReadProblem.gitDefault problem) path ≡ true →
    notice (reconcile F.Settled before changes) path ≡ just (fileQuestion path problem)
  unreadableExplained before changes path problem observed allowed
    rewrite unreadablePending before changes path problem observed allowed = refl

  repairedClearsWork : ∀ before changes path ready → changes path ≡ indexed ready →
    State.waiting (reconcile F.Settled before changes) path ≡ nothing
  repairedClearsWork before changes path ready observed rewrite observed = refl

  removedHidden : ∀ before changes path → changes path ≡ removed →
    files (reconcile F.Settled before changes) path ≡ nothing × State.waiting (reconcile F.Settled before changes) path ≡ nothing
  removedHidden before changes path observed rewrite observed = refl , refl

  unchangedRetained : ∀ before changes path → changes path ≡ unchanged →
    files (reconcile F.Settled before changes) path ≡ keepFile path (files before path)
  unchangedRetained before changes path observed rewrite observed = refl

  blockedRetainsWhole : ∀ git before changes → F.GitBlocked git →
    State.published (reconcile git before changes) ≡ filterView (State.published before)
  blockedRetainsWhole .F.Operating before changes F.operationBlocked = refl
  blockedRetainsWhole .F.Conflicted before changes F.conflictBlocked = refl

  blockedIgnoresCandidate : ∀ git before first second → F.GitBlocked git →
    reconcile git before first ≡ reconcile git before second
  blockedIgnoresCandidate .F.Operating before first second F.operationBlocked = refl
  blockedIgnoresCandidate .F.Conflicted before first second F.conflictBlocked = refl

  uninitializedStaysAbsent : ∀ git before changes → F.GitBlocked git → State.published before ≡ nothing →
    State.published (reconcile git before changes) ≡ nothing
  uninitializedStaysAbsent git before changes blocked absent rewrite blockedRetainsWhole git before changes blocked | absent = refl

  -- The selected file map is the SAME content map used by issue #30. Hiding a
  -- full Artifact removes its content reference and structural contribution.
  content : View → Content.Files.Manifest
  content view path with view path
  ... | nothing = nothing
  ... | just saved = just (Artifact.file saved)

  structural : View → FilePath → Maybe (List ℕ × List ℕ)
  structural view path with view path
  ... | nothing = nothing
  ... | just saved = just (Artifact.symbols saved , Artifact.edges saved)

  hiddenContent : ∀ view path → view path ≡ nothing → content view path ≡ nothing
  hiddenContent view path hidden rewrite hidden = refl

  hiddenStructure : ∀ view path → view path ≡ nothing → structural view path ≡ nothing
  hiddenStructure view path hidden rewrite hidden = refl

  unreadableHidesBoth : ∀ before changes path problem → changes path ≡ unreadable problem →
    content (files (reconcile F.Settled before changes)) path ≡ nothing ×
    structural (files (reconcile F.Settled before changes)) path ≡ nothing
  unreadableHidesBoth before changes path problem observed =
    hiddenContent (files (reconcile F.Settled before changes)) path (unreadableHidden before changes path problem observed) ,
    hiddenStructure (files (reconcile F.Settled before changes)) path (unreadableHidden before changes path problem observed)

  NoFreshArtifact : Change → Set
  NoFreshArtifact unchanged = ⊤
  NoFreshArtifact removed = ⊤
  NoFreshArtifact (unreadable problem) = ⊤
  NoFreshArtifact (indexed ready) = ⊥

  absentStaysAbsent : ∀ change → NoFreshArtifact change → fileChange change nothing ≡ nothing
  absentStaysAbsent unchanged notReady = refl
  absentStaysAbsent removed notReady = refl
  absentStaysAbsent (unreadable problem) notReady = refl
  absentStaysAbsent (indexed ready) ()

  hiddenUntilReindexed : ∀ before changes path → files before path ≡ nothing → NoFreshArtifact (changes path) →
    files (reconcile F.Settled before changes) path ≡ nothing
  hiddenUntilReindexed before changes path hidden notReady rewrite hidden | absentStaysAbsent (changes path) notReady = refl

  filterLookup : ∀ previous path → previousFiles (filterView previous) path ≡ keepFile path (previousFiles previous path)
  filterLookup nothing path = refl
  filterLookup (just view) path = refl

  rawFiles : F.GitState → State → Changes → View
  rawFiles F.Settled before changes path = fileChange (changes path) (files before path)
  rawFiles F.Operating before changes = files before
  rawFiles F.Conflicted before changes = files before

  appliesCurrentPolicy : ∀ git before changes path → files (reconcile git before changes) path ≡
    keepFile path (rawFiles git before changes path)
  appliesCurrentPolicy F.Settled before changes path = refl
  appliesCurrentPolicy F.Operating before changes path = filterLookup (State.published before) path
  appliesCurrentPolicy F.Conflicted before changes path = filterLookup (State.published before) path

  keptIsIncluded : ∀ path value saved → keepFile path value ≡ just saved →
    included (Content.Entry.gitDefault (Artifact.file saved)) path ≡ true
  keptIsIncluded path nothing saved ()
  keptIsIncluded path (just original) saved found with included (Content.Entry.gitDefault (Artifact.file original)) path in selected
  ... | true with just-injective found
  ...   | refl = selected
  keptIsIncluded path (just original) saved found | false with found
  ... | ()

  noExcludedResults : ∀ git before changes path saved → files (reconcile git before changes) path ≡ just saved →
    included (Content.Entry.gitDefault (Artifact.file saved)) path ≡ true
  noExcludedResults git before changes path saved found = keptIsIncluded path (rawFiles git before changes path) saved
    (trans (sym (appliesCurrentPolicy git before changes path)) found)

  exclusionsDuringSuspension : ∀ git before changes path saved → F.GitBlocked git →
    files before path ≡ just saved → included (Content.Entry.gitDefault (Artifact.file saved)) path ≡ false →
    files (reconcile git before changes) path ≡ nothing
  exclusionsDuringSuspension .F.Operating before changes path saved F.operationBlocked found excluded =
    trans (filterLookup (State.published before) path) (trans (cong (keepFile path) found) (keepExcluded path saved excluded))
  exclusionsDuringSuspension .F.Conflicted before changes path saved F.conflictBlocked found excluded =
    trans (filterLookup (State.published before) path) (trans (cong (keepFile path) found) (keepExcluded path saved excluded))

  blockedRetainsIncluded : ∀ git before changes path saved → F.GitBlocked git →
    files before path ≡ just saved → included (Content.Entry.gitDefault (Artifact.file saved)) path ≡ true →
    files (reconcile git before changes) path ≡ just saved
  blockedRetainsIncluded .F.Operating before changes path saved F.operationBlocked found allowed =
    trans (filterLookup (State.published before) path) (trans (cong (keepFile path) found) (keepIncluded path saved allowed))
  blockedRetainsIncluded .F.Conflicted before changes path saved F.conflictBlocked found allowed =
    trans (filterLookup (State.published before) path) (trans (cong (keepFile path) found) (keepIncluded path saved allowed))

  workExcluded : ∀ path problem → included (ReadProblem.gitDefault problem) path ≡ false →
    keepWork path (just problem) ≡ nothing
  workExcluded path problem excluded rewrite excluded = refl

  excludedUnreadableIsResolved : ∀ before changes path problem → changes path ≡ unreadable problem →
    included (ReadProblem.gitDefault problem) path ≡ false → State.waiting (reconcile F.Settled before changes) path ≡ nothing
  excludedUnreadableIsResolved before changes path problem observed excluded rewrite observed = workExcluded path problem excluded

  blockedExclusionClearsWork : ∀ git before changes path problem → F.GitBlocked git →
    State.waiting before path ≡ just problem → included (ReadProblem.gitDefault problem) path ≡ false →
    State.waiting (reconcile git before changes) path ≡ nothing
  blockedExclusionClearsWork .F.Operating before changes path problem F.operationBlocked found excluded =
    trans (cong (keepWork path) found) (workExcluded path problem excluded)
  blockedExclusionClearsWork .F.Conflicted before changes path problem F.conflictBlocked found excluded =
    trans (cong (keepWork path) found) (workExcluded path problem excluded)

  -- No new admission rule: reconcile is consumed only after the existing
  -- family/start/schema/lock gates. Git here is re-observed at publication.
  Step : State → F.GitState → Changes → State → Set
  Step before git changes after = after ≡ reconcile git before changes

  transition : ∀ before git changes → Step before git changes (reconcile git before changes)
  transition before git changes = refl

availability : Maybe View → String
availability nothing = "No completed index is available yet. "
availability (just view) = "Searches retain the last completed index, with current family exclusions applied. "

operationQuestion : Maybe View → D.Question
operationQuestion previous = D.prerequisite
  (D.text 'G' ("it is in the middle of a merge or rebase. " ++ availability previous))
  (D.text 'F' "inish or abort the Git operation. Muninn will continue indexing afterward; partial files from the operation will not replace the saved view.")

conflictQuestion : Maybe View → D.Question
conflictQuestion previous = D.prerequisite
  (D.text 'G' ("it reports unresolved file conflicts. " ++ availability previous))
  (D.text 'R' "esolve the conflicts, or abort the operation that created them. Muninn will continue indexing afterward.")

gitNotice : State → Maybe D.Question
gitNotice current with State.git current
... | F.Settled = nothing
... | F.Operating = just (operationQuestion (State.published current))
... | F.Conflicted = just (conflictQuestion (State.published current))

module Reports (selection : E.Rule) where
  module Reconcile = Family selection

  blockedExplained : ∀ git before changes → F.GitBlocked git →
    Σ D.Question (λ question → gitNotice (Reconcile.reconcile git before changes) ≡ just question)
  blockedExplained .F.Operating before changes F.operationBlocked = operationQuestion (Reconcile.filterView (State.published before)) , refl
  blockedExplained .F.Conflicted before changes F.conflictBlocked = conflictQuestion (Reconcile.filterView (State.published before)) , refl

  pendingIsNotCompleted : ∀ git before changes current → F.GitBlocked git → State.published before ≡ nothing →
    F.snapshotStatus git (State.published (Reconcile.reconcile git before changes)) current ≡ F.SuspendedPending
  pendingIsNotCompleted .F.Operating before changes current F.operationBlocked absent rewrite absent = refl
  pendingIsNotCompleted .F.Conflicted before changes current F.conflictBlocked absent rewrite absent = refl
