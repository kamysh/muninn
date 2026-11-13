# Cleanup batches use the actual current policy

`PolicyCleanupBatch` resolves the current family policy and verifies the saved
cleanup task inside the same shared transaction as its bounded cleanup effect.
It then calls the existing `CleanupEffects.Core.transaction`; the caller cannot
substitute a deletion script or supply a weaker outcome.

## The capture stays fixed

The original accepted world and complete captured incarnation list remain the
operation's input. `Selected.intent` carries the same IDs and original coverage
proof into the current family rule. This changes the policy used to assess
current need, not the workset. The actual task check verifies owner, typed request
ID and that exact list before any cleanup effect runs.

Each batch resolves policy again. A policy change therefore changes subsequent
need/projection decisions without recapturing the task or reusing a stale rule.
Missing policy/task context uses the existing abort continuation and preserves
the complete store.

## Actual effect and preservation laws

The transaction has at most one data mutation. The shared `MutationBound`
includes rollback as a zero-mutation endpoint; no separate per-operation counter
is introduced.

For an actual current observation and verified task, `Current` proves:

- Execution equals the existing cleanup effect under the stored current rule.
- Safety and shared-store admissibility hold for that actual result.
- An eligible captured record strictly decreases the existing finite work mass.
- The saved task retains its original request ID and complete capture.
- Active receipts, other receipts, protected data and records outside the capture
  remain unchanged.
- The batch's actual trace preserves current-view uniqueness/checkout agreement.
- Current pointer, typed policy version and frozen defaults survive, so the same
  effective policy is still observable after the batch itself.

The next transaction will read any intervening policy change from its new world.
The batch does not complete or discard the original request. An unchanged result
is not task completion; finalization still requires the actual cleanup-completion
check and all sibling tasks to finish.

## Boundary

This is #122 under #84 and #25. Complete policy acceptance/supersession reporting,
automatic follow-up choice, holder lifecycle, fair scheduling and assembled
original-request convergence remain integration work. Selection now uses the
actual admitted stored rules and saved Git defaults through #26; the batch no
longer accepts a matcher parameter.
This bounded single-edit building block does not prescribe a new physical SQL
layout or establish a runtime throughput measurement.

Agda and documentation only. Rust correspondence, live data, installed binaries,
system configuration and deployment are unchanged.
