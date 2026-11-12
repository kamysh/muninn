{-# OPTIONS --safe #-}
-- A search retains its intent while the selected checkout is made ready.
module Muninn.FirstSearch where

import Muninn.Worktree as W
import Muninn.Storage as Storage
import Muninn.IndexFsm as Index
import Muninn.IndexWorkControl as Work
import Muninn.AdmittedSelection as Selection
import Muninn.OrderedSelection as Ordered
import Muninn.Config as Config
import Muninn.Dialogue as Dialogue
open import Muninn.Types using (FilePath)
open import Data.Bool using (Bool; true; false; not)
open import Data.String using (String)
open import Data.List using ([])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- The locator adapter resolves the selected checkout; when it cannot, the
-- request retains its query and asks the agent for enough context.
record Intent : Set where
  constructor intent
  field query : String
        checkout : Maybe W.Checkout
        authorized : Bool

record Session : Set where
  constructor session
  field request : Intent

-- The checkout observation supplies freshness and pending-file facts; report
-- all of them, including a stale or partial view during a Git operation.
-- A current report requires an observed inventory matching the published view.
record ObservedInventory {baselines : W.Baselines} (world : Storage.World baselines) (selected : W.Checkout) : Set where
  field observed : FilePath → Maybe W.FileEntry
        matches : ∀ path → observed path ≡ Storage.viewsOf world (W.Checkout.id selected) path

data Freshness {baselines : W.Baselines} (world : Storage.World baselines) (selected : W.Checkout) : Set where
  unverified observedStale : Freshness world selected
  observedCurrent : ObservedInventory world selected → Freshness world selected

record Coverage {baselines : W.Baselines} (world : Storage.World baselines) (selected : W.Checkout) : Set where
  constructor coverage
  field available : Bool
        freshness : Freshness world selected
        partial gitSuspended : Bool

gitBlocked : Index.GitState → Bool
gitBlocked Index.Settled = false
gitBlocked Index.Operating = true
gitBlocked Index.Conflicted = true

report : ∀ {baselines} {world : Storage.World baselines} {selected} →
  Bool → Freshness world selected → Bool → Index.GitState → Coverage world selected
report false freshness pending git = coverage false unverified pending (gitBlocked git)
report true freshness pending git = coverage true freshness pending (gitBlocked git)

availability : ∀ {baselines} → Storage.World baselines → W.Checkout → Bool
availability world selected with world (W.Checkout.id selected)
... | nothing = false
... | just snapshot = true

coverageFor : ∀ {baselines} (world : Storage.World baselines) (selected : W.Checkout) →
  Freshness world selected → Bool → Index.GitState → Coverage world selected
coverageFor world selected freshness pending git = report (availability world selected) freshness pending git

reportedAvailability : ∀ {baselines} {world : Storage.World baselines} {selected}
  available (freshness : Freshness world selected) pending git →
  Coverage.available (report available freshness pending git) ≡ available
reportedAvailability false freshness pending git = refl
reportedAvailability true freshness pending git = refl

resolveCheckout : W.Checkout → Intent → Intent
resolveCheckout selected (intent query previous authorized) = intent query (just selected) authorized

resolutionKeepsQuery : ∀ selected before → Intent.query (resolveCheckout selected before) ≡ Intent.query before
resolutionKeepsQuery selected (intent query previous authorized) = refl

-- Ordinary reconnection preserves the active query and selected checkout.
disconnect : Session → Session
disconnect before = before

queryPreserved : ∀ before → Intent.query (Session.request (disconnect before)) ≡ Intent.query (Session.request before)
queryPreserved before = refl

targetPreserved : ∀ before → Intent.checkout (Session.request (disconnect before)) ≡ Intent.checkout (Session.request before)
targetPreserved before = refl

contextPrompt : Dialogue.Prompt
contextPrompt = Dialogue.prompt
  (Dialogue.text 'I' " cannot tell which checkout you want to search.")
  (Dialogue.text 'P' "rovide the repository or working directory, and I will continue your search.") []

startPrompt : Dialogue.Prompt
startPrompt = Dialogue.prompt
  (Dialogue.text 'T' "his repository has not been started for indexing yet.")
  (Dialogue.text 'S' "tart indexing for this repository, then I will continue your search.") []

-- Missing context or first-start authority is communicated; an authorized
-- checkout with no view arranges indexing rather than ending at "pending".
data Action : Set where
  askContext askFirstStart arrangeIndex serveView : Action

next : ∀ {baselines} → Storage.World baselines → Session → Action
next world (session (intent query nothing authorized)) = askContext
next world (session (intent query (just selected) authorized)) with world (W.Checkout.id selected)
... | just snapshot = serveView
... | nothing with authorized
...   | false = askFirstStart
...   | true = arrangeIndex

firstSearchArrangesWork : ∀ {baselines} (world : Storage.World baselines) query selected →
  world (W.Checkout.id selected) ≡ nothing →
  next world (session (intent query (just selected) true)) ≡ arrangeIndex
firstSearchArrangesWork world query selected absent rewrite absent = refl

unauthorizedDoesNotArrange : ∀ {baselines} (world : Storage.World baselines) query selected →
  world (W.Checkout.id selected) ≡ nothing →
  next world (session (intent query (just selected) false)) ≡ askFirstStart
unauthorizedDoesNotArrange world query selected absent rewrite absent = refl

continuesWhenReady : ∀ {baselines} (world : Storage.World baselines) query selected authorized snapshot →
  world (W.Checkout.id selected) ≡ just snapshot →
  next world (session (intent query (just selected) authorized)) ≡ serveView
continuesWhenReady world query selected authorized snapshot present rewrite present = refl

module Preparation (Results Temporary : Set) where
  module Indexing = Work.Model Intent Results Temporary

  -- Newly accepted indexing work carries the complete search intent. Existing
  -- work is retained, while the session keeps the search intent separately.
  arrange : ∀ {baselines} → Storage.World baselines → Session → Indexing.State → Indexing.State
  arrange world (session request@(intent query nothing authorized)) before = before
  arrange world (session request@(intent query (just selected) false)) before = before
  arrange world (session request@(intent query (just selected) true)) before with world (W.Checkout.id selected)
  ... | just snapshot = before
  ... | nothing with before
  ...   | Indexing.state false current results temporary = Indexing.state false current results temporary
  ...   | before@(Indexing.state true current results temporary) = Indexing.start request before

  noAuthorityNoWork : ∀ {baselines} (world : Storage.World baselines) request current results temporary →
    arrange world request (Indexing.state false current results temporary) ≡
      Indexing.state false current results temporary
  noAuthorityNoWork world (session (intent query nothing authorized)) current results temporary = refl
  noAuthorityNoWork world (session (intent query (just selected) false)) current results temporary = refl
  noAuthorityNoWork world (session (intent query (just selected) true)) current results temporary
    with world (W.Checkout.id selected)
  ... | nothing = refl
  ... | just snapshot = refl

  acceptedSearchArrangesWork : ∀ {baselines} (world : Storage.World baselines) query selected results temporary →
    world (W.Checkout.id selected) ≡ nothing →
    Indexing.State.current (arrange world (session (intent query (just selected) true))
      (Indexing.state true nothing results temporary)) ≡ just (Indexing.work Indexing.running (intent query (just selected) true))
  acceptedSearchArrangesWork world query selected results temporary absent rewrite absent = refl

  acceptedWorkIsReused : ∀ {baselines} (world : Storage.World baselines) query selected existing results temporary →
    world (W.Checkout.id selected) ≡ nothing →
    Indexing.State.current (arrange world (session (intent query (just selected) true))
      (Indexing.state true (just existing) results temporary)) ≡ just existing
  acceptedWorkIsReused world query selected existing results temporary absent rewrite absent = refl

  reconnectKeepsPreparation : ∀ {baselines} (world : Storage.World baselines) request before →
    arrange world (disconnect request) before ≡ arrange world request before
  reconnectKeepsPreparation world request before = refl

-- Results can only cite files visible in the selected checkout under the
-- current selection. Query matching and ranking are not modeled here.
record Result {baselines : W.Baselines} (world : Storage.World baselines)
  (selected : W.Checkout) (policy : Config.FamilyPolicy)
  (entries : Selection.FamilyEntries policy) (gitIgnored : FilePath → Bool) : Set where
  constructor result
  field path : FilePath
        entry : W.FileEntry
        selectedView : Storage.viewsOf world (W.Checkout.id selected) path ≡ just entry
        familyMatches : W.Checkout.family selected ≡ Config.FamilyPolicy.family policy
        allowed : Ordered.included (Selection.classify policy entries (gitIgnored path) (FilePath.value path) false) ≡ true

resultBelongsToSelectedView : ∀ {baselines} {world : Storage.World baselines} {selected policy entries gitIgnored}
  (found : Result world selected policy entries gitIgnored) →
  Storage.viewsOf world (W.Checkout.id selected) (Result.path found) ≡ just (Result.entry found)
resultBelongsToSelectedView found = Result.selectedView found

resultIsIncluded : ∀ {baselines} {world : Storage.World baselines} {selected policy entries gitIgnored}
  (found : Result world selected policy entries gitIgnored) →
  Ordered.included (Selection.classify policy entries (gitIgnored (Result.path found)) (FilePath.value (Result.path found)) false) ≡ true
resultIsIncluded found = Result.allowed found
