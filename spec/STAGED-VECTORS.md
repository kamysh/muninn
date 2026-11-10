# Staged text and vector publication

Text and symbols become available without waiting for an embedding provider.
This applies equally to first-party and vendor content. Tier still controls
classification and ranking; it no longer requires eager first-party vectors.
The old `Tier1NeverPending` restriction is intentionally removed, following the
approved product decision rather than the current Rust behavior.

## Data and normal preparation

`VectorData` replaces the opaque logical vector payload with pending, waiting
and usable data. Pending means that usable vectors are still needed. It does
not assert that a worker is currently running; accepted-job liveness belongs to
`WorkQueue`. Waiting retains a nonempty explanation and next action. Neither
condition makes the indexed text unavailable or turns refinement into a failed
indexing task.

A usable value carries its exact normalized source text, full embedding key
and validated coordinates. The dimension is positive and matches the key;
coordinates must be finite and the vector nonzero. `Embeddings` also requires
stored state and vector presence to agree. The certified byte-keyed reuse cache
uses the same stronger coordinate validity requirement.

The configured family profile is the expected key for these operations. Exact
key equality includes backend, model, configuration, profile revision,
normalization version, task and dimension. Family configuration/profile
admission is owned by the existing configuration issue; provider adapters must
associate actual results with the exact submitted text/bytes and profile.
The Float/f32 boundary remains documented in `Muninn.Float`.

## Reuse and coverage are different facts

`StagedVectors` reads the actual owned world. A compatible completed vector
anywhere in the same family prevents another provider calculation. A vector
from another family, source text or profile is not a compatible hit.

Coverage additionally requires a published association with the specific chunk.
For example, identical text in chunks A and B can share a completed calculation,
but B is not reported usable merely because A has a vector. The association for
B must first be saved. This distinction prevents a cache hit from overstating
semantic coverage.

The family report covers currently selected chunks with actual text postings.
It derives pending, usable or waiting from their stored data, and records the
source row for every reported entry. Every searchable chunk is included. The
per-chunk classifier is also available to the selected-checkout search contract;
the family report must not be labelled as a selected-checkout report.

## Concrete publication and preservation

`TextPublication` constructively saves admitted chunk text, its posting and an
extracted source symbol in one shared database transaction. It checks that the
source version still exists. No embedding state or provider availability is a
precondition. The existing view-publication contract then makes the prepared
content visible without requiring vectors.

`VectorPublication` rechecks the actual source chunk and saves a vector
association or preparation guidance. It reuses completed compatible data first,
updates existing pending data rather than appending it on every retry, and
retains existing usable data. Its general frame preserves text, postings,
symbols and other non-vector records. Store admissibility and receipt isolation
are proved for the concrete transactions.

Accepted indexing work seals these writes with the original request checkpoint.
The existing worker-generation and current-policy guards prevent a callback
from publishing after pause, cancellation or supersession. Generic interrupted
runs and completed retries use the existing receipt convergence proof.

These are formal product contracts, not Rust implementation verification. The
current pipeline still eagerly embeds first-party content and can return an
error before publishing its text. This slice changes the authoritative design;
the provider, pipeline, search and final dispatcher correspondence obligations
remain with their existing issues. It introduces no SQL table, MCP wire name,
deployment, provider call or live database change.
