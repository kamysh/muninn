# Unreadable files and Git suspension

This issue #31 slice specifies publication behavior, not new indexing
permission. Existing family-start, schema, pause and lock admission gates
remain in force.

## State and observations

`CheckoutReconciliation.State` holds an optional saved view, unresolved read
work by path, and the observed Git state. A file artifact groups its content
entry with structural contributions from the same completed file analysis.
Removing that one artifact removes both kinds of visibility.

One completed inventory supplies one observation per path: unchanged, removed,
newly indexed, or unreadable with a nonempty explanation and saved Git default.
The function-valued maps express logical meaning, not an infinite traversal or
a required physical layout. Runtime inventories and work queues are finite.

The Git observation used by `reconcile` is rechecked at publication. A merge,
rebase or unresolved conflict that begins after scanning prevents publication
of those file observations.

## Total transitions

For settled Git state, each path advances independently:

- Newly indexed content replaces the old artifact and clears pending read work.
- An unreadable file is hidden, and its reason remains pending and actionable.
- A removed file is absent and clears pending read work.
- An unchanged file retains its saved artifact and pending work.

Current family selection is then applied to both visible artifacts and pending
work. Excluding an unreadable file resolves that particular indexing request;
it does not leave a permanent warning about a deliberately excluded path.
A saved view can contain completed progress while other paths remain pending;
publication completion is distinct from full checkout coverage.

During a Git operation or unresolved conflict, the transition ignores ALL new
file observations. It retains the whole prior saved view and pending work,
subject only to current family exclusions. In particular, a transient unreadable
file during a merge does not remove one piece of that retained view. If no view
was ever published, suspension leaves it absent rather than manufacturing an
empty completed index.

`refreshPolicy` applies exclusions independently of an indexing pass or Git
readiness; `refreshFleet` lifts it to every checkout. It preserves Git status
and cannot initialize an unpublished checkout. Paused checkouts therefore do
not need to resume indexing before exclusions take effect.

Once Git settles, the same ordinary transition resumes per-file progress.
There is no failure terminal state, retry count or new timeout mechanism.

## General laws

The safe module proves universally quantified laws, including:

- `readableAdvances`: every ready included path becomes visible without any
  assumption about the other paths.
- `unreadableHidden`, `unreadableHidesBoth`: unreadable old text and structural
  results disappear together.
- `unreadablePending`, `unreadableExplained`: an included unreadable path keeps
  explicit work and an actionable shared-protocol question.
- `hiddenUntilReindexed`: unchanged or unresolved work cannot resurrect a hidden
  artifact; publishing a fresh indexed artifact is required.
- `repairedClearsWork`, `removedHidden`: resolved paths do not retain obsolete
  read questions.
- `blockedIgnoresCandidate`, `blockedRetainsWhole`, `blockedRetainsIncluded`:
  Git suspension retains the prior view rather than partially applying scans.
- `noExcludedResults`, `exclusionsDuringSuspension`,
  `blockedExclusionClearsWork`: latest selection still governs suspended views
  and pending work.
- `uninitializedStaysAbsent`, `pendingIsNotCompleted`: a checkout with no saved
  view stays unavailable during suspension and is reported as pending.

File and Git prerequisites use `Dialogue.Question`; they explain what is
available and how to continue. No LLM call or automatic external edit is added.

## Publication and implementation boundary

`Family.content` produces the exact `Content.Files.Manifest` type accepted by
issue #30 publication planning. `Family.structural` exposes contributions from
the same artifacts; an absent artifact supplies neither content nor structure.
Structural edge endpoint filtering and canonical selected snapshots remain the
existing graph/publication obligations.

The adapter must capture this logical state from the actual selected view and
publish its resulting content/structure through the guarded, receipt-sealed
world contract from #30. This module does not prove filesystem observations,
SQL encoding or Rust correspondence; #52 covers those adapter obligations.
Closed-dispatch enforcement remains #51. The old `IndexFsm.chooseSnapshot`
helper is a Git-only gate and cannot substitute for per-file reconciliation.
