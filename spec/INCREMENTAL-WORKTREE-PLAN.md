# Plan: incremental worktree reconciliation

## Objective

For an established checkout with a small set of reported changes, avoid reading
and reanalysing unchanged files on the event-driven fast path. The user has
accepted that an unreported change may remain stale until a full audit, which
is due every five minutes. Reuse family-owned compatible
file versions, chunks and embeddings. Maintain the selected checkout's text,
vector and structural views without changing another checkout's published view.

## Sequence

1. Trace the existing watcher, selection rules, file-version identity,
   base/delta publication and structural search. Use the existing approved
   Agda models and distinguish their external-observation assumptions from
   guarantees of the Rust runtime.
2. Specify change discovery, affected-path processing and cross-file
   relationship updates, including initialization, deletions, renames,
   excluded and untracked files, unreliable timestamps, lost or incomplete
   change information, and edits concurrent with publication. Quantify the
   reuse and isolation laws over arbitrary checkouts and paths. State the
   filesystem adapter obligations and the circumstances requiring full work.
3. Implement the user-approved eventual-consistency tradeoff: the watcher
   supplies reported paths for the fast path, and a five-minute full audit
   recovers missed events. Unknown baselines, explicit event loss and changes
   that cannot safely be narrowed require a full audit. Do not describe hints
   as complete evidence or change Muninn's configured file selection.
4. Implement only behavior defined in the specification. Reassess the prior
   uncommitted experiment, including cache-discard advice and source storage,
   against the objective and measurements. Preserve applied migration blocks;
   introduce persistent storage only where a specified requirement needs it.
5. Verify the formal model, representative text/vector/structural results,
   base movement and checkout isolation, unreliable timestamps and recovery.
   Measure application file reads and indexing work for small edits as the
   file and worktree counts grow, against the existing implementation. State
   separately the initial-discovery cost and any fallback scan cost.

No live database, installed executable, service, or GitHub change is included.
