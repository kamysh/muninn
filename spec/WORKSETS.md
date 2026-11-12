# Fixed cleanup worksets

`Muninn.Workset.Queue.Fixed` takes a finite immutable `Manifest` of original
record-incarnation IDs. Its predicate-based scanner is private. Stored records
are the progress checkpoint: a committed deletion is durable progress and a
retry inspects the current store using the same manifest. There is no shrinking
cursor that can forget a currently needed record.

For each consistent observation, independently specified predicates distinguish
records still useful to the latest policy from records additionally held by
active readers. An included shared record stays tracked until the task ends.
An absent record satisfies its obligation; its captured identity stays in the
manifest. The operation layer must reject reuse of captured incarnations and
bind the saved manifest to the same request on retry.

The scanner returns proof of one of three states:

- Every captured record still present is useful, so this workset is satisfied.
- Unresolved records remain, but every one is currently blocked.
- At least one captured, unused, unheld record can be deleted.

The scanner examines later entries after a blocked one. A general theorem proves
that the presence of any deletable entry forces the advance result; a blocked
prefix cannot make it report waiting. Once readers add no extra need, every
unresolved obligation supplies a deletable entry.

Advancement executes the shared database transaction
`eraseRows 1 retain (commit tt)`. Every productive commit strictly reduces the
number of captured records still stored, independent of unrelated indexing.
Writing an uncaptured record cannot increase that measure. The transaction
preserves any saved manifest/receipt row outside the captured IDs exactly.
Waiting preserves the entire checkpoint, not just the remaining count.

This is a reusable progress kernel, not the exclusion worker. The caller still
must establish the complete capture, fixed request identity, independent meaning
of useful/held, safe record incarnations, consistent transaction observation and
actual persistence correspondence. The exclusion operation must separately
prove policy visibility, supersession and the complete user-visible outcome.

An eventual-progress guarantee assumes that the database eventually accepts
transactions, running readers eventually release their references, and the
worker receives execution time. Until then the durable task remains available
and reports what it is waiting for. No timeout discards the requested cleanup.
