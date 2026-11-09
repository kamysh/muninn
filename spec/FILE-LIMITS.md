# File and structural-analysis limits

The family-shared limits default to 10 MiB (10485760 bytes) for a selected
file and 1 MiB (1048576 bytes) for structural analysis. Admission measures the
actual raw bytes before text decoding or normalization. Equality is allowed.
Filesystem metadata is only an early estimate; a size question needs actual
byte evidence, and an admission needs the bytes subsequently read to fit. The logical byte sequence
is not a requirement to allocate the whole file in Rust.

`FileLimits` defines the independent text and structural eligibility predicates
and computes a total assessment against them. Every runnable job carries a proof
that its file fits the overall cap. Full structural work additionally requires
both the structural bound and parser availability. Files between the bounds,
or without a supported parser, have explicit text-only coverage and a reason;
they are not silently reported as structurally covered. The overall file cap
still applies even if the structural cap is configured higher.

`Config.captureDefaults` materializes global scalar limits as explicit numbers
when a family registers. `OwnedState.DefaultsInfo` requires those numbers in the
saved defaults row. An absent family override inherits that captured pair;
an explicit override replaces it. Later global edits do not reinterpret saved
families. Both the override and cap values are part of normalized request
identity, including the distinction between inheritance and an explicit value.
`StoredPolicy` proves the exact inherited/explicit values and proves that writes
outside the current pointer, version and defaults rows preserve selected limits.

`IndexFileLimits` combines actual selected-file evidence with these assessments.
Its executable batch returns every runnable job and every unresolved size
question. General membership laws prove that an allowed file is scheduled
regardless of other files awaiting a decision, and that no oversized selected
file disappears from the returned questions. Binding constructors at this
admission boundary require a runnable job. Coverage messages state the scope
and reason for text-only work.

Oversized files use the existing corrective dialogue. The question gives the
path, measured byte count and family cap, then explains the choices: increase
the family cap, exclude the file through selection policy, or reduce/split it
outside Muninn. Other ready files proceed. An agent can update policy or content
and obtain a new assessment; the server does not generate an agent reply or
spin an internal retry loop. These questions do not claim task completion.

This is the cap-admission contract for #28. Whole-checkout publication and fair
execution belong to #30/#44; parser semantics belong to #42. Text work being
scheduled does not claim its index is already published or its embeddings ready.
The authoritative model and request encoding change here; Rust adapters, runtime
verification, installation, deployment and live data are separate work.
