# Durable request receipts

`Muninn.ReceiptTypes` and `Muninn.ReceiptLedger` refine receipts in the existing
`Muninn.OwnedState.World`. There is no second ledger store. The model remains a
logical inventory, not a prescription for SQL tables or host-file layout.

## States and replay

An entry has a stable operation ID and one of three indexed states:

- **Active:** complete normalized input, proof that a public mutation uses its
  own ID, and durable work containing its current generation, retained file
  versions and checkpoint data.
- **Finished:** the same input and saved result.
- **Used:** the operation ID alone. Input, result, work, repository and path
  fields are absent. Its owner is the installation, never the removed family.

An identical request resumes the saved work or returns the saved result.
Different input preserves the original world and explains that the new request
needs a new ID. An ID-only marker never permits another execution: it explains
that the details are gone and asks the caller to inspect the current state
before deciding whether another operation is needed.

Active receipts retain their required file versions through the existing
strong-reference invariant. Reclamation refuses to discard active work.
Finished details become an installation-owned marker, preserving the ID and
removing every payload field and strong reference. Marker retention has no
expiry transition.

## Atomic steps and lost replies

Acceptance checks the ID and allocates the receipt/work state within one shared
database transaction. It preserves every existing record. A storage-slot
collision continues the internal allocator rather than overwriting a record.

Each business transaction is sealed with its updated checkpoint or saved result
before commit. All committed effects and that receipt update are published
together; an abort publishes neither. An aborted step retains its old work and
returns a required nonempty dialogue prompt explaining the reason and next
action. It does not immediately call itself again.

An update must match both normalized input and the saved generation. Committing
a checkpoint increments the generation. Retrying the old step after a lost
reply returns the new checkpoint without evaluating its old business effect.
A finished result or used-ID marker likewise bypasses that effect.

`Effect` requires a proof of the fixed receipt-preservation predicate. A business
transaction cannot create, remove or alter receipts; the protocol alone changes
its own entry. The sealing proof preserves other operations' receipts and ID
markers. The generation is a concurrency token, not a substitute for an
operation-specific progress measure or outcome proof.

The general laws cover acceptance visibility, identical retry replay, mismatch
isolation, stale-step suppression, saved-result replay, marker retention and
ownership, preservation of active work, exact committed update results,
commit/abort sealing and every interruption boundary of a single atomic step.

## Remaining integration obligations

Parent #21 must connect these transitions to admission and corrective dialogue.
Each operation still owes its independent outcome, complete prerequisite and
whole-world preservation proofs; the proof-requiring dispatcher is #51.
Selecting `complete` does not itself certify the user-visible goal.

The runtime adapter must implement serialized ID admission and unique operation
IDs, durable checkpoints and the declared effect boundaries. Rust/SQL
correspondence and crash injection remain #52/#53. No runtime receipt store or
migration is installed by this specification change.

The database transaction laws do not provide atomicity across SQL, host files
or third-party caches. Bootstrap/local-file recovery and physical secret handling
remain #46 and the corresponding adapter contract. This model does not authorize
copying bootstrap secrets into a database. Registry resolution and complete
reference/prerequisite checks must happen through the independent admission
contracts; a receipt codec does not invent them.

This slice does not implement workers or prove their eventual completion. Their
finite-work progress, resource assumptions and concrete outcomes remain separate
operation obligations. It changes no wire names, services or installed binaries.
