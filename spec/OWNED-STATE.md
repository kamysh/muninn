# Owned-state inventory

`Muninn.OwnedState` expands the logical world beyond published checkout views.
This inventory was checked against all nine migration files and the storage
paths below, at source commit `c076e99fc0f2bd5c54d1b80ff6391116d9cd736d`.
It distinguishes current storage from agreed state that Rust does not yet keep.
The audit also checked all current Rust filesystem write/delete sites: configuration
creation/replacement, temporary configuration staging, MCP logs/retention, model
cache delegation and output streams; test fixtures were excluded from ownership.

## Current storage and logical categories

| Storage or code | Logical records in `OwnedState` |
| --- | --- |
| `migrations/public/001_init.sql`, `families.sql`, `retired_paths.sql`: `public.repos` | `registration`, typed immutable `creationIntent`; database family ID, optional physical binding, retirement, legacy readability, absence-start timestamp, indexing authorization, creation completion and family pause are explicit fields |
| `migrations/repo/checkouts.sql`, `missing_checkouts.sql`: `checkouts` | `checkout`; database ID/incarnation, optional physical binding, retirement, pause, Git suspension and the absence-start timestamp are explicit fields; publication has its own current-view contract |
| `migrations/repo/configuration.sql`: `policy_defaults`, `policy_versions`, `family_policy` | `defaults`, `policyVersion`, `currentPolicy`; pointers require the corresponding immutable version/default record |
| `migrations/public/001_init.sql`: `knowledge` | `note`, `notePosting`, `noteVector`; the generated text and optional vector are independently visible to outcomes |
| `migrations/repo/worktrees.sql`: `file_versions` | `fileVersion` |
| Same migration: `base_files`, `file_deltas`, `worktree_base` | `baseBinding`, `deltaBinding`, `basePointer`; a delta explicitly distinguishes a deletion from a version reference |
| `migrations/repo/001_chunks.sql`, `worktrees.sql`: `chunks` and its generated `ts_vector` / optional `embedding` | `chunk`, `posting`, typed `vector` preparation/usable data; each kind remains independently observable even when SQL stores them in one row |
| `migrations/repo/structural_snapshots.sql`: `checkout_structural_snapshots` | `structuralSnapshot`, its `symbol` records and its `edge` records |
| `crates/core/src/store.rs:81-168`, `graph.rs:98-113,235-345` | `graphResource`, `symbol`, `edge`; includes primary and older linked-checkout AGE graphs, all four vertex and edge labels, and AGE-owned schema resources |
| `crates/core/src/store.rs:17-28,68-74`, `db.rs:184-205`, `family_store/preparation.rs` | `schemaResource`, `migration`; public and family migration receipts remain distinct from AGE readiness |
| `crates/core/src/store.rs:257-336`, `worktrees/mod.rs:750-780` | `legacy`; legacy chunks without a file-version reference remain visible rather than disappearing from the modeled world |
| `migrations/public/001_init.sql`: `mcp_usage` | `usage`; scoped to a family when known, otherwise to the installation |
| `crates/core/src/store.rs:430-515`, `family_store/preparation.rs` | `coordination`; saved preemption/preparation metadata is represented; session advisory locks themselves are external live capabilities |
| `crates/core/src/config.rs:254-256,347-363` | `bootstrap`; current installation configuration is a host file, not a family policy row |
| `crates/core/src/embeddings.rs:111-149` | `modelCache`; a shared local-model resource, including its external-cache ownership boundary |
| `crates/mcp/src/main.rs:277-366`: rolling file logger and retention task | `logFile`; installation-owned MCP log files are distinct from external system journal files |
| `crates/cli/src/main.rs:314-331`: owner-only temporary config before atomic replacement | `bootstrapStage`; includes a temporary file left by interruption before replacement/cleanup |

DDL indexes, sequences, generated columns and AGE catalogs belong to the resource
footprint of the corresponding logical records. This model does not prescribe
separate SQL tables for the logical kinds. The future adapter must expose their
complete footprint; deleting a chunk from a smaller model cannot establish that
its vector, text posting, graph records or storage resources were removed.

## Agreed state still missing from current persistence

`staging`, `acceptedWork`, `cleanupWork`, `activeReader`, `continuation` and
`receipt` are separate constructors. Receipt state is now refined by
[the durable receipt contract](RECEIPTS.md): active input/work, finished input/result
and installation-owned ID-only markers. Active receipt work contributes its
required file versions to the existing strong-reference invariant. Existing pending
embedding flags and registration intent cover only parts of the agreed durable workflow. There is
no complete durable cleanup/continuation/operation-receipt store today. Active
readers instead describe live capabilities; the model does not require persisting
a crashed reader or adding a reader table when PostgreSQL snapshot lifetimes
provide the same guarantee. This PR specifies the state, not its physical layout.

Accepted work retains the file versions it requires. Its typed job, parent request, input, phase and generation are defined in `WorkQueue`; saved continuations also name their parent request. [Work control](WORK-CONTROL.md) defines explicit start, disconnect, pause/resume and cancellation over the actual world. An active reader declares
the exact records it uses. Its operation contract must establish that this list
is complete. Cleanup captures and idle continuations retain weak incarnation
identities, not strong references: an already absent record is valid progress,
and an idle continuation cannot indefinitely prevent reclamation. The shared allocation
contract prevents reusing an incarnation still captured by work;
see [record allocation](RECORD-ALLOCATION.md). Cleanup tasks also carry the typed
operation ID of their accepting receipt; scheduling commits the task and
checkpoint under that same ID.

## Ownership, references and admissibility

Records have an installation or repository-family owner. Checkout-local records
retain checkout references; shared file versions stay family-owned. A family
cannot reference another family's records. Shared installation resources are
explicit. Notes are family-owned even when their payload describes a narrower
scope; a path string does not establish a new family.

The state invariant requires unique logical record identities, permitted owner
placement, resolution of every strong reference to a record of the expected
kind and permitted owner, and private execution bookkeeping. Strong references
cannot target readers, cleanup tasks, accepted work, continuations, receipts or
mutable current-view selectors.
Status tools may still inspect them through ordinary reads. This privacy rule
does not remove their outgoing holds on indexed data; see
[private bookkeeping](PRIVATE-BOOKKEEPING.md). Chunk, posting, vector, symbol, edge and snapshot
dependencies come from their constructors, rather than a cleanup operation
choosing which dependencies count. Weak identities are deliberately excluded.

General proofs establish that deleting a record preserves records of another
owner; references survive deletion of a distinct identity; and deleting an
unreferenced record preserves all admissibility requirements. In
particular, a record retained by another checkout, accepted work or an active
reader cannot satisfy that deletion theorem's no-incoming-reference guard.
This guard is a sufficient condition for this theorem, not the final cleanup
algorithm or a claim that every strongly connected group can be reclaimed
one record at a time.

## Runtime mismatches and remaining obligations

- Notes currently use exact `repo_path` strings (`knowledge.rs:13-22,41-94`);
  the agreed owner is a family. This PR does not migrate them.
- `store.rs:172-200` removes index schemas, graphs and registration, while
  public notes remain. [Unregistration and forget-all](REPOSITORY-REMOVAL.md) now have complete-world
  contracts; their Rust implementation and correspondence remain outstanding.
- `worktrees/mod.rs:896-898` reclaims file versions using base/delta references.
  It does not implement the agreed durable cleanup worksets or reader/accepted
  work roots represented here.
- The current bootstrap file and shared Hugging Face cache are installation
  resources. This inventory neither authorizes deleting third-party cache
  users nor moves configuration into the database.
- `crates/mcp/src/main.rs:337-365` currently prunes any old regular file in the
  configured log directory without checking the Muninn filename. The formal
  log-maintenance outcome must preserve files not owned by Muninn. This PR
  records the discrepancy; it does not repair that runtime behavior.
- Remaining per-kind metadata is retained as uninterpreted payload here. Saved
  policy/default contents are typed by [stored-policy resolution](STORED-POLICY.md). Identity and discovery are refined by [stable repository identity](REPOSITORY-IDENTITY.md),
  and selection/publication have their own contracts. Remaining transitions, ranking
  and operation-specific validity are subsequent issues; this ownership/reference
  invariant is not the complete product spec.
- The closed dispatcher and Rust/SQL projection must require this complete world
  and these invariants. Merely importing it does not enforce them in Rust.
  The generic finite-store interface does not establish an atomic transaction
  spanning SQL, host files and third-party caches. Each future adapter must
  justify its actual effect boundaries; inventory membership does not grant
  cross-resource atomicity.

External repository files, Git state, provider services, PostgreSQL extensions,
database WAL/free space, credentials managed by the user and system journal files
are environment resources, not records Muninn may silently delete. Contracts
must describe observations and capabilities at those boundaries separately.

## Exclusion-facing metadata refinement

[The exclusion outcome model](EXCLUSION-OUTCOMES.md) refines opaque fields into
registry retirement/legacy-read facts, checkout retirement/pause/Git state,
legacy and symbol source paths, and graph-resource scope/current use. These
logical facts must match actual published reads; cleanup cannot choose them as
retention preferences. The source inventory above remains a physical boundary,
not a claim that these are new SQL columns or that Rust already exports them.


## Current structural views

A family-owned `publishedView` association references one checkout and its
current structural snapshot. Snapshot contents are separate from the current-publication association;
being stored does not independently make a version current. The domain invariant,
reachability laws and pending publication integration are specified in
[current views](CURRENT-VIEWS.md).

## Typed stored policy

Saved defaults use the existing `PolicyDefaults`. Policy versions carry their
typed family identity, revision and `PolicyDraft`, and keep the original strong
defaults reference. The current pointer, version and defaults resolve from the
same owned world; see [stored-policy resolution](STORED-POLICY.md). Existing
ownership/reference laws do not alone establish immutable policy histories or
external locator-to-owner routing.

Vector payloads now follow [staged vector publication](STAGED-VECTORS.md):
exact source/profile identity and validated coordinates, with normal pending
and waiting metadata. The existing chunk reference and kind hierarchy remain;
this refinement does not require a new physical table.

Profile recreation deliberately removes code-derived records and typed note
vectors while preserving identity, curated note text and settings. Note vectors
now use the same validated `VectorData.State` payload as code vectors; their
semantic-use certificate resolves the actual saved repository profile. See
[profile recreation](PROFILE-RECREATION.md).

Private continuations now optionally retain a complete typed `SavedSearch`,
including code/structural input and stable family/checkout/incarnation scope.
The existing weak IDs reserve identities without pinning derived data. Arranged
indexing jobs keep their separately registered queue and receipt identities.
See [first-search continuation](FIRST-SEARCH.md).
