# Formal Specification

This directory contains the Agda formal specification for muninn.

## What is specified

`Muninn.agda` covers seven areas:

1. **Core data types** — `UUID`, `FilePath`, `RepoId`, `ChunkId`, `LineRange`,
   `Chunk` (with optional embedding), `Repo` (with optional `indexedAt`),
   `SearchResult`, `Symbol`, `SymbolKind` (Function / Class / Module / Import),
   `StructuralEdge`, `Relation` (Calls / Imports / Defines / InheritsFrom).

2. **Repo registration invariant** — `UniqueRepoPaths` asserts that equal paths
   imply equal repo identities across any list of registered repos.

3. **Indexing state machine** — `IndexState` and `IndexTransition` encode the
   valid lifecycle as an indexed inductive type, making invalid transitions
   unrepresentable:
   `Unindexed → Indexing → Indexed ⇄ Watching → Stale → Indexing`

4. **Validity predicates** — `ValidRange` (start ≤ end) and `ValidChunk`
   (content ≢ "").

5. **Query semantics** — `Similarity` wraps a `Float` value, `rrfScore` gives
   the Reciprocal Rank Fusion formula `1 / (60 + rank)`, and
   `HybridResultBound` constrains result-list length to the requested limit.

6. **Embedding backend dimensions** — `EmbeddingDimension` maps each backend to
   its fixed vector width (Voyage → 1024, OpenAI → 1536, Local → 384).

7. **Two-layer configuration** — `GlobalConfig`, `RepoConfig`, `EffectiveConfig`,
   field-level merge semantics, the `DimFrozen` invariant (embedding dimension
   fixed after first index), repo discovery via scan roots, and MCP walk-up
   resolution from `cwd` to nearest `muninn.toml`.

## Checking the spec

With the nix dev shell (which provides Agda 2.8.0 and the standard library):

    cd spec && nix develop --command agda Muninn.agda

No errors are expected.

## Note on Float postulates

`Float` and its arithmetic operations (`_+F_`, `_/F_`, `fromℕF`) are
**postulated** rather than imported from `Data.Float`. This is intentional:
Agda's standard-library Float interface varies across versions and the
operations needed here are cleaner to axiomatise directly. The postulates are
realised by the host language's native double arithmetic in any concrete backend.
