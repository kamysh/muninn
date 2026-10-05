> **Historical design/stage record.** This document preserves proposals and
> progress reports from its date, including superseded decisions. It is not
> a current installation procedure or completion report. For implemented 1.0 behavior,
> see [Development](../../docs/development.md); for installation, see
> [Getting started](../../docs/get-started.md) and [AGENTS.md](../../AGENTS.md).

# Muninn core worktree runtime

The approved replacement for the withdrawn tree/snapshot implementation uses
one current base and ordinary relational file deltas. Configuration improvements
and installation are separate stages. No custom storage trees are used.

## Runtime behavior

- The primary Git checkout is the base. Linked worktrees are discovered through
  Git, inherit the existing family configuration, and receive independent AGE
  graphs. Application tables remain together in the family schema.
- `file_versions` identifies reusable versions by relative path, content hash and
  tier. `base_files` selects current versions. `file_deltas` contains only changed
  paths; a NULL version represents deletion. Chunks/embeddings are stored once
  per version. Matching existing chunk embeddings are reused on first indexing.
- Moving the base preserves other initialized worktrees by inserting references
  to formerly inherited versions, then removing redundant overrides. Base,
  deltas and the updated checkout graph commit in one transaction. A family
  advisory lock serializes publication and cleanup on the writing connection.
- Semantic search uses the base's partial HNSW index with excluded paths and an
  exact search over the selected worktree's delta. Text search follows the same
  split. Hybrid ranking is merged by modality before RRF, in one SQL snapshot.
- The watcher observes linked roots and Git metadata. Its fallback poll discovers
  new/removed worktrees and retries failures; unchanged initialized worktrees do
  not have their source files scanned on every discovery poll. Overflowing event
  queues trigger a complete reconciliation.
- **Merge/rebase/conflicts suspend publication.** The last completed index remains
  searchable, and the daemon logs the suspension and retries. A checkout without
  a completed index reports pending. An unavailable directory which remains in
  Git's worktree registry retains its data. Only removal from a successfully read
  registry retires it and drops its AGE graph.
- Parser, chunking, embedding backends, existing exclusions and ranking remain
  the existing application's mechanisms. Non-Git/independent-directory indexing
  retains its existing path.

## Verification and limits

The guarded disposable PostgreSQL harness exercises old-index embedding reuse,
worktree reuse, independent edits/additions/deletions, moving main, automatic
new-worktree discovery, semantic/text/hybrid/structural search, Git suspension,
rollback after concurrent file edits, unavailable roots and removal/graph cleanup.
Agda `FileMap.movingBasePreservesWorktree` and `movingBaseKeepsMinimalDelta`
establish the general representation laws, not database implementation correctness.

Large-delta latency/recall and a 100-worktree load test remain unmeasured. Delta
search is exact and its cost grows with that worktree's changed chunks. Graph
reconstruction parses eligible files when a checkout's visible file map changes.
Filesystem scanning checks the selection/hashes twice and Git state before/after;
it cannot provide an atomic filesystem snapshot against uncooperative writers.
Legacy model/configuration changes, live migration/cutover, installation and
service restarts are outside this stage. Existing migration blocks are immutable;
`repo/worktrees.sql` appends a new migration chain, including base-only indexes.

## Configuration/runtime integration

Stored family policy now supplies selection rules, embedding backend/batch size
and watcher debounce. Preflight and runtime share the strict rule compiler.
`add` and policy saves leave an unstarted family idle; `start` or the TUI's
separate Start confirmation enables foreground indexing and subsequent daemon
retries. Policy notifications and the fallback poll restart affected watchers;
selection changes request reconciliation across the family. A concurrent policy
save cannot be followed by publication from an older policy transaction.

Independent configured directories use their existing chunking pipeline inside
a transaction and reconcile on watcher events. Legacy registrations retain file
configuration. The primary Git checkout is resolved from family identity even
when the originally selected linked worktree has been removed. Code search
uses the family's saved embedding profile; global knowledge embeddings retain
the existing global profile. No migration block changed in this stage.
