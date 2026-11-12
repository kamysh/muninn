# Family note state

`KnowledgeState` models notes under repository-family and note IDs. A note is
family-wide or limited to one checkout. `NoteRequests` resolves the requested
location to a checkout in the expected family. Existing scoped notes can be
edited or deleted only from their own checkout; family-wide notes are shared
across checkouts in that family. New note IDs must be unused across families.

A note write or deletion commits its note change and request receipt together.
The independent world goals specify the changed note, its derived vector,
preservation of unrelated notes, vectors, profiles, locations and other state,
and preservation of other request receipts. A repeated committed request
replays its receipt; other note changes do not make it run again.

Note vector state uses the repository family's profile. Recreating the profile
preserves note text and clears that family's derived note vectors. A vector is
accepted only for the current note and profile. Listing and search outcomes
require visibility in the selected family and worktree; matching, ranking and
pagination algorithms are outside this state model.

`RepositoryWorld` represents the locator mapping, note state and an opaque
remainder. It does not prove that every real database record is represented or
that a locator resolves correctly in Rust. The final closed dispatcher and the
storage/runtime correspondence remain #18 and #51–#52. The current Rust note
implementation uses exact repository-path keys and the global embedding profile;
it does not yet provide the family/worktree behavior modeled here.
