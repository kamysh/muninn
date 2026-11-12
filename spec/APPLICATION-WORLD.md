# Application world

`Muninn.ApplicationWorld` is an independent logical view of persistent state.
It records a family owner, a logical record identity and kind, installation
state, and request receipts. Kinds distinguish registration, policy, notes,
index data, work, readers, continuations and owned resources. Logical kinds do
not require separate SQL tables or prescribe how search works.

The reference invariant requires family references to resolve within the same
family to the expected kind, and installation references to resolve in
installation state. Record identities are unique within their ownership domain
because each owner and key selects at most one entry. The reference lists are
logical state: the future storage correspondence must show they include every
real reference. The type checker does not inspect an opaque payload and cannot
establish that correspondence by itself.

Receipt ownership must match independently defined ownership of the request and
result, with neither missing nor unrelated owners. The forgetting and preservation goals use independent ownership of
installation values, requests and results directly, rather than trusting the
receipt owner list. Issue #51 must bind those definitions to fixed operation
semantics rather than allowing an operation to choose weaker ones.

The forgetting goal requires every family record to be absent and no
installation value, active request or completed result to contain that family. A used-ID marker has no family, path,
request or result content. The preservation goals retain unrelated installation state, other families,
unrelated requests and all used-ID markers. A completed result
shared with the forgotten family may be removed as a whole.

## Storage correspondence still required

The current migrations contain a public repository registry, usage and
path-keyed notes; per-family policy, checkout, file-version, file-binding,
chunk and structural-snapshot records; and AGE graph resources. A logical kind
can cover part of a row or a resource, rather than naming a physical table.
Current notes use exact paths, whereas the approved logical owner is the
repository family. Usage rows with a repository path require an ownership
mapping; installation-only usage belongs to installation state.

The currently implemented storage does not yet provide the complete agreed
durable request, continuation and work state. Issue #52 must connect the actual
storage and its complete reference footprint to this world. Issue #51 must make
the dispatcher use fixed outcomes and proofs. This model alone does not prove
that the running Rust application follows the specification.
