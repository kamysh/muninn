# Repository and checkout identity

Database IDs survive a legitimate relocation. Locations tell Muninn where to
inspect, not which repository owns saved work. `RepositoryIdentity.ObjectId`
means provider-issued object-incarnation evidence, not an inode reused without
an incarnation guarantee, a Git commit, remote URL or path hash. Providers must
return no key when they cannot establish reliable evidence. Inspection stamps
bind corrective answers to the particular observation being confirmed. This
specification writes no identity markers into Git metadata.

## Discovery dialogue

Positive directory-root or Git-common-directory evidence reuses the family;
positive root or Git-admin-directory evidence reuses its checkout. A saved
directory registration remains a directory registration after Git appears.
Ordinary discovery preserves kind, IDs and checkout incarnation.

Without positive evidence, a generic question explains the uncertainty and
offers either the same repository/worktree or a new replacement. Confirmation
records the saved ID, inspected root and observation stamp. Family and checkout
confirmations use separate facts. A same-worktree answer cannot be inferred
from a family answer. Both options advance the decision; a new answer does not
silently reassociate old data. If the accepted request intent changes, the
ordinary request-identity dialogue supplies a fresh request ID.

The provider supplies the selected operation scope and its requested locator.
It must establish that its canonical root/object observations concern that
scope. The model does not prove the filesystem, Git executable or agent answers
truthful. Unknown evidence requires clarification; it does not block unrelated
legacy registrations merely because their old directories cannot be inspected.

## Stored transitions

`OwnedState.RegistrationInfo` and `CheckoutInfo` carry mandatory database IDs
and optional physical bindings. Checkout incarnations remain explicit even
without usable filesystem identity evidence. `RegistryCreation.Reserve` checks
the actual world for existing IDs, incarnations and positively associated
families before creating anything. Fresh record and owner IDs reserve past
references as well as currently present rows. Its three writes reserve the
family, immutable typed creation policy and initial checkout together; indexing
and creation-completed remain false.

`RepositoryRegistry.Family.Move` reads both actual control records in the
transaction. Physical evidence or a current explicit clarification is required
for each. Other registered IDs already associated with the observed objects
prevent silent reassociation. Both metadata changes commit together, retain
database IDs/incarnation, clear confirmed-absence retirement and preserve
indexing authorization and checkout controls. Existing indexed views, content,
notes and settings are not rewritten by a location change.

`Family.Add` preserves the existing family while admitting a fresh checkout.
The actual store must contain neither its ID/incarnation nor an already
associated checkout. Automatic work still follows the existing family
indexing-start gate: registration alone never authorizes indexing.

`IdentityCheckpoint.Run` seals each concrete transition with the original
active receipt in the same transaction. Its general laws establish actual
commit, stored receipt visibility, retry without repeated writes, completion,
and equality of the interrupted-then-completed final world to the intended
committed world. Registration preserves every old record before the receipt
seal; explicit laws preserve all existing family-owned records after that seal,
including other receipts. Move and addition likewise preserve other families.

## Explicit directory conversion

`DirectoryConversion` requires the actual directory binding and an explicit
request naming its family. Git is queried for retained paths in the selected
checkout and generation; content versions remain reusable while ignore
answers are refreshed. A directory family has one checkout; this is checked
as an admission obligation rather than silently discarding another checkout.

Publication work and both metadata changes form one shared transaction.
Until it commits the saved directory registration/view remains usable; a crash
cannot expose a half-converted registration. The original request stays active
with its cleanup task until that work completes. IDs, incarnation, indexing
authorization and pause state are preserved. Curated notes, configuration and
compatible indexed records remain in the store. The new view applies current
family selection rules to the fresh Git defaults.

The storage adapter must supply a transaction and proofs of the fixed final
map, structural view, actual metadata, admissibility, retained data, family
isolation and cleanup capture. The adapter cannot choose its own success goal.
This is the same proof-carrying publication boundary as #30; a concrete row
writer and Rust correspondence are separate existing work, not proved by this
Agda type check. No application behavior, database or service is changed here.
