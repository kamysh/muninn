{-# OPTIONS --safe #-}
-- Muninn/Graph.agda
-- Symbol types and structural relationship graph used for code navigation.
module Muninn.Graph where

open import Muninn.Types
open import Data.String using (String)
open import Data.List   using (List)

data SymbolKind : Set where
  Function : SymbolKind
  Class    : SymbolKind
  Module   : SymbolKind
  Import   : SymbolKind

record Symbol : Set where
  field name     : String
        kind     : SymbolKind
        filePath : FilePath
        range    : LineRange
        chunkId  : ChunkId

data Relation : Set where
  Calls        : Relation
  Imports      : Relation
  Defines      : Relation
  InheritsFrom : Relation

record StructuralEdge : Set where
  field from     : ChunkId
        to       : ChunkId
        relation : Relation

-- A per-repo structural graph: symbol nodes and directed relationship edges.
-- NARROWS (intentional): in the implementation SymbolGraph is not a Rust type.
-- The graph is stored in Apache AGE (PostgreSQL graph extension) and queried via
-- ag_catalog.cypher.  This record models the logical structure only.
record SymbolGraph : Set where
  field symbols : List Symbol
        edges   : List StructuralEdge

-- ─── Cypher Query Safety ──────────────────────────────────────────────────────

-- A value of type CypherBound A is a value of type A that is passed as a
-- bound parameter to ag_catalog.cypher/3 via the jsonb params argument
-- ($1, $2, … placeholders) rather than concatenated into the Cypher template
-- string.  This is the design-level guarantee that closes the SQL/Cypher
-- injection surface.
record CypherBound (A : Set) : Set where
  constructor bound
  field value : A

bindCypher : ∀ {A : Set} → A → CypherBound A
bindCypher x = bound x

-- A symbol upsert into the graph is safe when:
--   • The node label comes from the SymbolKind enum — a finite set of
--     hardcoded strings, never user-supplied text.
--   • The node key is a ChunkId (UUID) — structurally injection-impossible.
-- All other symbol fields (name, filePath, lineRange) are SET as bound
-- parameters via bindCypher, never embedded in the MERGE template.
record SafeSymbolUpsert : Set where
  field label   : SymbolKind   -- enum → safe Cypher label
        nodeKey : ChunkId      -- UUID  → safe MERGE key

-- A symbol graph query (e.g. find callers/callees by name) is safe when
-- the user-supplied symbol name is a bound parameter, not an interpolated
-- fragment of the Cypher string.
record SafeSymbolQuery : Set where
  field symbolName : CypherBound String   -- bound via $1, never concatenated
        relation   : Relation