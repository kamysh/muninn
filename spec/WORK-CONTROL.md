# Durable indexing work and controls

This is an authoritative product contract, not a claim that the current Rust
implements durable indexing jobs or the agreed administration tools. No new
CLI command or MCP wire name is introduced by these modules.

## Agreed behavior

Registration and configuration do not authorize the first index. An explicit
start names the actual family and inspected policy revision. Preparation must
be complete, the family active and unpaused, and removal must not be pending.
`FirstStart` checks the saved policy and registration in its database transaction,
then saves authorization and accepted work together with the original request
checkpoint. Existing work or cleanup for the same request prevents another
queue entry. Compatible artifact reuse remains governed by `CompletedWork`.

Accepted work belongs to its durable request, not to an MCP connection.
Disconnecting leaves that work and its progress unchanged. Reconnecting uses
the existing request identity and receipt protocol to find the saved work.

Ctrl-C in foreground indexing pauses the current request and its child work.
It preserves unfinished versions and previously published results. It does not
silently cancel the request. The CLI must explain that work is paused and show
the existing command `muninn resume <registered-path>`. The path is the registered
locator displayed by `muninn status`.

The existing family pause command stops indexing for the family. Resume clears
the family pause and queues paused work while preserving its saved inputs and
versions. Neither command grants first-start authorization. A paused request
cannot publish through the indexing worker gate, including a provider call that
returns after the pause was committed.

Cancellation removes the target queue entries and saved continuations. It
releases unfinished-version holds from the target and child receipts, stops
child work, and captures cleanup in the same transaction. It does not change
the family's indexing authorization or pause setting. Cancelled work cannot be
resumed. Another, distinct request remains possible under the existing policy.

Cancellation retains the original request while its cleanup tasks run. It
reports that previously published results remain available; it does not claim
that cancelling rolls them back. The existing bounded cleanup worker reclaims
unneeded records. Its last-task finalizer verifies completion, removes private
cleanup tasks and finishes the original receipt. The existing request-ID history
prevents an old retry from becoming a new write.

## Enforced model boundaries

- `WorkQueue` supplies typed job identity, parent, input, phase and generation.
  Saved continuations also identify their parent request.
- `IndexControl.Worker` checks the actual registration, queued job generation,
  active receipt and removal state inside the committing transaction.
  `ContentPublication.Prepared` must provide this permission; its execution
  rechecks the worker gate as well as the current policy pointer.
- `WorkControlStore.Edit` requires owner/kind preservation, valid placement and
  reference preservation for replacements. Deletion requires private bookkeeping.
  The general `finalValid` theorem proves admissibility of the concrete edits.
- The concrete cancellation transaction saves cleanup and the active original
  checkpoint together. Its interruption/retry theorem proves convergence after
  any transaction boundary or lost reply, without duplicating cleanup work.
- `IndexFsm.interrupt` now reaches `Paused`; resumption is explicit and still
  requires authorization, ready schema and settled Git state.

These modules use the existing shared database semantics, receipts and cleanup
worker. They do not prescribe new SQL tables. Rust correspondence, complete
pipeline assembly and the final proof-requiring dispatcher remain the existing
implementation/dispatcher obligations in the specification series. In
particular, current Rust Ctrl-C exits instead of saving a durable pause, and
the current MCP tool list has no administration adapter yet.
