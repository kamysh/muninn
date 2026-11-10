# Embedding-profile recreation

Changing the backend or model is an explicit recreation of derived index data.
It is not an ordinary policy edit and not an in-place vector migration.
`Policy.policyKeepsEmbeddingProfile` proves that every ordinary policy step
retains the backend and model. Batch-size changes remain ordinary settings.

This defines the existing catalog's `recreateIndex` administration intent. It
adds no CLI command and does not restore the rejected standalone index-removal
command. Ordinary `reindex` continues to mean rebuilding. Runtime exposure and
pipeline assembly remain the existing administration/pipeline obligations.

## Fixed world outcome

`RecreationStore.derived` exhaustively classifies every owned category. Recreation
removes code versions, bindings, chunks, postings, vectors, symbols, relationships,
published/retained structural data, staging, legacy indexes and family graph
resources. Derived note vectors are also removed. The same transaction publishes
a fresh policy version with the requested embedding selection and advances its
current pointer.

Repository and checkout identity, curated note text, note text postings, frozen
defaults and policy history survive. The new policy preserves family, name,
file-selection rules, watcher settings and frozen defaults. Execution receipts
and private bookkeeping are not mistaken for index data. Other families' data
is outside the removal scope. The fresh policy incarnation is allocated outside
the original world's complete reservation set, including weak captured IDs.

These outcomes are over actual owned records. The operation cannot supply an
alternative deletion policy. `noDerivedAfterSeal` rules out every local derived
record in the committed world, including old code and note vectors; it is not
just a statement that the known old IDs were visited.

## Hold release and atomic retry

A committing transaction must resolve the inspected current policy, match the
requested family, and verify that retained records no longer reference derived
data. Running searches and accepted work must release those references first;
recreation cannot break their saved dependencies. If work is still using the
index, the existing corrective continuation explains how to finish or cancel
that work and continue the original request. No writes occur in that branch.

The actual finite deletion effects, replacement policy and original receipt
checkpoint commit together. On a crash or lost acknowledgement, the shared
receipt machinery replays the saved checkpoint instead of deleting/recreating
again. `interruptedNotePreserved` proves note retention at every interruption
boundary. `SavedRequest.converges` proves that every interrupted run followed by
a completed retry reaches the same committed world.

The request remains active after this recreation checkpoint: source indexing and
note-vector preparation must still finish. This slice does not report a rebuilt
index merely because its previous incarnation was removed. Scheduling, release
of other accepted jobs, prioritization against new work and end-to-end rebuild
progress belong to the existing pipeline/dispatcher issues. The convergence
theorem is for the ready atomic replacement, not a claim that external holders
eventually release without those lifecycle obligations.

## Repository profiles for code and notes

`RepositoryProfile.Active` resolves the actual saved family policy. Its resolved
key must match the stored backend, requested hosted model or bundled local model,
and backend dimension. The same resolved key is used for code and curated notes;
there is no global notes profile. Provider-specific configuration, normalization
and task/version fields remain explicit in the full key and are certified by
the provider adapter rather than guessed from the database dimension.

The compatible cache reads both code and note vectors, comparing the full key
and exact normalized input. A hit requires reuse rather than another embedding
calculation. A usable note requires the actual note text, its stored vector
association, exact input/profile agreement and validated coordinates. An
incompatible vector cannot satisfy that semantic-use contract, even if it has
the same dimension. A missing hosted model requires the normal configuration
dialogue before this resolved-profile certificate can be constructed.

Embedding-provider calls calculate vectors only. This does not authorize Muninn
to call a generative LLM to reason about a request or conduct its dialogue.

## Implementation boundary

These are authoritative Agda contracts and constructive logical transactions.
Rust, SQL schema recreation, configuration/MCP adapters, note-write adapters and
the closed dispatcher still have to implement them. No runtime test, installation,
deployment, provider request or live database mutation is part of this slice.
