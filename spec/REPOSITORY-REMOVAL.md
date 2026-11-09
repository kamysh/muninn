# Unregistration and forget-all

The existing CLI has `reindex`, which rebuilds, and `remove`, which unregisters
the entire family and deletes its code index. There is no separate operation
that clears an index while keeping the repository registered and waiting for
permission to recreate it. The canonical intent and normalized payload now say
`unregister`; the invented checkout-only removal payload is gone. No Rust CLI,
MCP wire name or deployed receipt format is changed by this specification PR.

The previously agreed forget-all intention additionally removes curated notes,
settings and every other family-owned record. An explicit, unambiguous typed
request is sufficient. It does not require a mandatory preview and second
confirmation. Ambiguous language is handled by the existing generic dialogue
before acceptance. Existing CLI confirmation flags remain an adapter concern.

## Complete stored outcome

`RemovalStore.settingsOrNotes` makes an exhaustive decision for every logical
owned category. Unregistration retains curated notes, note search data, immutable
creation policy, defaults and policy history/current settings. It removes the
registration, checkouts, all code content and indexes, graphs/resources, pending
work, continuations and temporary artifacts. Retained settings continue to carry
the family ID, so a later forget request can resolve the retained data even
though the registration itself no longer exists. No implicit re-enrollment or
index recreation is added.

Forget-all removes every family-owned category. In both cases, family-owned
request receipts become installation-owned ID-only markers. They contain no
request, repository location, result or pending work. This preserves the agreed
permanent protection against repeating old IDs. Existing other-family and shared
installation resources remain unchanged. The model includes all owned table,
graph and temporary-resource categories; an adapter cannot omit a vector table
or an older graph and still satisfy its fixed outcome.

The implementation of this policy is a finite scan compiled only to ordinary
`DB.remove` and marker `DB.put` actions. Unchanged foreign rows and retained
metadata are not rewritten. All actions and the original marker seal commit in
one transaction. General quantified proofs establish actual lookup outcomes,
unique keys, permitted placement, all strong references, private bookkeeping,
metadata preservation, other-family isolation and complete ownership cleanup.
They cover arbitrary valid worlds, including strongly connected data; no leaf
ordering or one-row-at-a-time no-incoming assumption is needed.

## Admission, waiting and completion

Acceptance checks the actual family identity and absence of another active
removal in the same transaction that saves the original request. Retries inspect
that receipt first. A missing or ambiguous target gets an ordinary question,
without inventing a saved checkpoint. Reusing an ID for another request keeps
its original meaning. Accepted cleanup uses its durable binding; it does not
require a registration record that cleanup may already have removed.

An active removal receipt closes current-reader admission and publication.
Registration facts and retained-view roots remain separate from this request
availability gate. Earlier readers finish normally. Until their records are
released, continuation explains the wait, keeps the original receipt active and
leaves the store unchanged. There is no internal retry loop, time cutoff or
successful completion while cleanup remains outstanding.

The reader-release rank is a natural number and strictly decreases whenever an
existing reader releases. Progress uses the already agreed environmental
assumptions: existing searches eventually release, the database eventually
accepts transactions and resumed work receives execution time. Adapters must
route every new reader/publication through the same gate. The later closed
protocol and Rust correspondence work must enforce those entry points; a type
check of a helper module alone does not establish that runtime wiring.

Once readers have finished, completion performs the actual cleanup and original
ID seal atomically. The original receipt can logically finish and reclaim its
details within that one commit. Its immediate completion certificate carries the
actual accepted-run/commit witness; a used-ID marker alone never certifies which
request completed. Other pending operations are retired by the
explicit repository removal; this does not report that their former goals were
achieved or pretend their earlier commits were rolled back. After a lost reply,
the ID marker prevents repeating any write and the generic dialogue asks the
agent to inspect current state. The interruption/retry theorem reaches the
fixed complete outcome, not an operation-selected weaker success predicate.

The logical DB transactions are authoritative requirements. Rust/SQL execution,
resource footprint mapping, serialization and actual external capability
lifetimes still require the existing adapter/correspondence verification work.
This PR performs no live deletion, migration, application installation or
system/service change.
