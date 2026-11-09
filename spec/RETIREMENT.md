# Retirement, verified return and prompt reclamation

This issue #33 slice specifies lifecycle and concrete owned-world control
updates. It does not modify Rust, schema migrations, the installed service or
live registrations.

## Absence is evidence, not a permission error

`Retirement.inspect` consumes an inspection result for the registered identity:
verified same repository, confirmed absence, or an inconclusive inspection with
an explanation. A path string or a matching branch/commit is not proof of
identity. The evidence source belongs to #32, whose agreed policy keeps IDs in
the database and clarifies uncertain moves through dialogue.

The first confirmed absence starts a 60-second grace. Further confirmed
absence retires the registration only once that whole grace has elapsed. An
inconclusive inspection preserves the current registration phase and clears
the absence timer; uncertainty cannot count as a confirmed-absence interval.
A verified return reactivates automatically and clears the timer. Explicit
unregistration removes registry membership rather than changing this retained
registration to the same retired state. It does not wait for the absence
grace and cannot be undone by an ordinary presence observation. Its
remove-index/forget-all scope is specified under #34.

The safe laws prove that every new retirement requires confirmed absence, a
recorded start and the elapsed grace. They also prove early absence waits,
inconclusive inspection cannot retire, verified identity reactivates and an
already-retired missing registration remains stable.

## Durable state and concrete transaction

The family and checkout control records now expose `missingSince` explicitly.
Saving and recovering the lifecycle state round-trips exactly; metadata,
indexing-related controls and the Git/pause flags are preserved.

`RetirementControl` reads the actual family-owned control record inside the
shared database transaction, computes the total lifecycle update and writes
that record. Only a newly retired registration creates cleanup work. The
creation uses the existing allocator and bounded cleanup-task protocol; no
second task store or cursor is introduced.

The original request checkpoint is sealed into the same commit. It remains
active while cleanup runs and releases derived-version holds that cleanup
itself does not need. Other readers and accepted work keep their protections.
General laws prove world admissibility, control and cleanup-task visibility,
notes/settings and other-family preservation, atomic interruption boundaries,
local completion and interruption/retry convergence.

## Availability and cleanup

`RetirementCleanup.available` requires both a live family registration and a
live checkout. A retired/unregistered family or retired checkout cannot admit
new searches merely because old derived rows have not yet been reclaimed.
Already-running readers use the existing retained-view contract.

The current registry uniqueness invariant supplies one family registration;
this is consumed independently of how #32 establishes repository identity.
Actual final-world lookup evidence establishes the retired family flag and
its loss of availability.

Retirement adds no cache-retention duration. The same existing cleanup worker
must reclaim unused captured derived records as soon as actual readers,
accepted work and shared references allow. Its fixed complete-world contract
preserves still-needed shared data, readers, curated notes/settings and other
families. A returning repository can require index rebuilding if its derived
records were already reclaimed. There is no promise to restore deleted data
from an identity match.

## Verification boundary

The clock and filesystem/Git inspections are environment observations. The
adapter must supply reliable elapsed-time and identity evidence and use the
registered identity being inspected, with revalidation before committing a
retirement. Rust/SQL and filesystem correspondence remain #52; closed catalog
execution and scheduling remain #51 and the existing scheduling issues.
No new cache expiry service, failure registry, retry deadline or Git metadata
identity marker is introduced.
