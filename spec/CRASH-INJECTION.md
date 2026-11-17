# Generic crash injection for the exclusion operation

The Rust implementation must be checked against the same interruption/retry
property as the formal operation, including the orphan-record cleanup problem.
This contract defines the reusable harness slice and the commit-boundary
registration the adapter owes.

## Boundaries

`CRASH-BOUNDARIES.json` names every commit boundary the exclusion operation
crosses, each tied to its spec module: reader admission, each bounded
deletion/projection batch, the receipt progress checkpoint, the follow-up
capture and the finalization commit. A crash can lose the acknowledgement at
any of these; the retry must reach the independently specified world outcome
across every owned record category.

The adapter registers the boundaries it commits through in a
`pub const CRASH_BOUNDARIES: &[&str]` table
(`crates/core/src/cleanup/mod.rs`).

## Harness

`muninn-setup/crash-injection-check.sh` runs inside the guarded disposable
fixture (as the payload of `muninn-setup/test-persistence.sh`). It enumerates
the registered boundaries against the manifest and fails while any boundary
is unregistered — a crash at an unregistered boundary cannot be retried
against the world outcome. The check reports; it never substitutes a
happy-path test for the missing retry assertion.

## Current status

The exclusion adapter is absent: no Rust cleanup module exists, no boundary is
registered, and the check fails by design. Retry-through-the-real-adapter
assertions land together with the adapter; this slice authorizes no runtime
repair or deployment. Observed results must be real; the model's outcome is
the assertion target, not the implementation's current behavior.
