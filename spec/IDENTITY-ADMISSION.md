# Identity-aware corrective admission

`Muninn.IdentityDialogue` and `Muninn.RequestAdmission` connect the closed typed
catalog, normalized identity, durable receipts and generic corrective dialogue.
They define the common formal gate, not a Rust handler or an installed service.

## Input and recovery

Input explicitly distinguishes a typed submission, continuation of the current
conversation, and an incomplete request carrying a clarification question.
Incomplete input cannot silently mean “continue the previous operation.”

Available context is reused unchanged, including its identity, original intent,
known facts and work references. Existing correction laws preserve those fields
except the explicitly corrected facts. An accepted request's normalized content
does not change when conversational facts are corrected. A different repository,
revision or other meaningful input receives the new-ID guidance instead.

Without context, a supplied mutation ID or explicit continuation ID is enough
to look up saved work. Restoring an internal catalog request provably preserves
the complete normalized meaning; it creates no wire names or new invocation.
If neither context nor identity is available, the ordinary restatement/identity
question is returned. A background job's parent ID is not substituted for its
own ID. Read-only/control/UI requests do not gain permanent receipt markers.

## Receipt-first transaction

The root `interact` gate routes the turn inside the actual shared transaction
world. It observes an existing receipt before invoking fresh admission:

- Matching active work returns its saved input and checkpoint.
- Matching finished work returns its recorded historical response.
- Changed input preserves the original work and asks for a new ID.
- A used-ID marker explains that details are gone and cannot become new work.
- Missing identity or incomplete input produces a question without writes.
- Only a new identified request can reach fresh prerequisite checking.

Saved responses describe the earlier operation. For example, retrying a note
write after another request edited that note returns the saved response; it does
not restore the earlier text or assert that the old goal still holds now.

Admission and receipt/work creation remain one transaction. No permission from
an earlier database snapshot is used. Mapping transaction replies is proved to
preserve every database effect and its commit/rollback boundary.

## Certificates and dialogue

The application supplies one independent prerequisite/result/outcome model over
the complete closed `Meaning` type. All adapters for the same meaning use those
same predicates and result type. Individual handlers cannot choose weaker ones.

A permission contains exact normalized-input equality, matching context/request
identity and the prerequisite proof. Canonical restoration proves that available
prerequisites yield a permission; a checker cannot claim that another question
is required while those prerequisites are established.

A completion answer requires both the independent outcome proof and a matching
finished receipt in the current world. A cache-only success cannot leave the ID
unrecorded and later permit fresh execution. An already satisfied business goal
still needs the operation's durable completion bookkeeping. That bookkeeping
and any operation-specific data-removal requirements belong to its contract.

Questions preserve the complete owned world. Generic dialogue preserves accepted
work across clarification, reconnect and context loss. Each assessment ends its
internal turn; the existing no-two-internal-steps theorem still applies. There
is no automatic agent reply, generative-model action or terminal-failure branch.

The general integration laws include recovery by ID after context loss, saved
input/result reuse, changed-input isolation, exact receipt-transaction admission,
missing-identity/incomplete-input noninterference, and end-to-end suppression of
new work after a lost acceptance reply. The root interruption theorem includes
all boundaries of its one atomic transaction, including lost acknowledgement.

## Remaining boundaries

Concrete operation outcomes/prerequisites, complete whole-world preservation and
worker termination proofs remain the individual operation contracts and #51's
proof-requiring dispatcher. The generic model is not permission to supply a
vacuous application outcome predicate.

Raw parsing and client/host events must refine these input distinctions through
#48/#49. In particular, parse failure must not be mapped to `continueCurrent`.
Runtime correspondence and crash injection remain #52/#53. Database outages and
host-file recovery remain #46; no cross-resource atomicity is claimed here.
This slice changes no Rust, migrations, wire names, services or installation.
