# What happens on the first search of a worktree

A search is for one checkout. In MCP, an explicit `repo` takes precedence
over `cwd`. If an enabled family has a worktree with no published view yet,
its first search can arrange indexing for that checkout and use the view
when it is ready. A checkout with a published view can answer while another
checkout is still indexing.

[Checkout publication](CheckoutPublication.lagda.md) · [Rust search entry point](../../crates/mcp/src/tools.rs) · [On-demand structural search test](../../crates/mcp/src/worktree_tests.rs)

## What the request carries

The intent contains the original query, the checkout once it has been
resolved, and authorization for first indexing. The session carries that
intent while work is pending.

```agda
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

```

## What a coverage report can say

The model tracks whether a published view exists, whether its freshness was
verified, whether files are still pending, and whether Git operations have
suspended updates. A current report requires an observed file inventory
matching the selected checkout's published view. The filesystem and Git
adapter must justify that observation.

```agda
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

```

## Keep the query and checkout across interruptions

Resolving the checkout preserves the original query. In the model, ordinary
reconnection preserves both the query and the selected checkout. The linked
Rust path can index an authorized worktree on demand and reuse committed file
work. Supply a caller-generated `operation_id` for recovery across MCP connections.
The server saves the request before indexing. After reconnecting, call
`continue_request` with that ID to execute the saved search or retrieve its
finished result. The saved request cannot be rebound to a different query or
checkout. The active request still depends on its checkout being available.

```agda
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

```

## Choose the next action

| Situation | Model action |
| --- | --- |
| The checkout is unresolved | Ask for checkout context |
| The selected checkout has a published view | Serve that view |
| The selected checkout has no view and indexing is authorized | Arrange indexing |
| The selected checkout has no view and indexing is unauthorized | Ask for first start |

These cases determine the next action. `continuesWhenReady` applies once a
published snapshot exists. Eventual publication also depends on the
availability and scheduling of the underlying work.

```agda
-- Missing context or first-start authority is communicated; an authorized
-- checkout with no view arranges indexing rather than ending at "pending".
```

### Distinguish an unfinished index from an empty result

A completed search can legitimately find no matching files. A checkout
without a published view has yet to search its files, so the request
remains unresolved until the view exists or the caller supplies a missing
prerequisite. The query is still available when that prerequisite is met.

```agda
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

```

## Reuse indexing already accepted

When the system can accept work, a first search can give the indexing job
its complete search intent. If there is already accepted work, the model
keeps that work and carries the search intent separately. Resolving and
reconnecting a search must preserve these inputs.

```agda
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

```

## Which files a result may cite

Each modeled result carries evidence that its file belongs to the selected
checkout's view, is in the policy's family, and passes selection. This
excludes a result found only in a sibling checkout or from a file ruled
out by selection. The module covers eligibility. Query matching and
ranking are outside this contract.

```agda
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
```
