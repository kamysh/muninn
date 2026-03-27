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
record SymbolGraph : Set where
  field symbols : List Symbol
        edges   : List StructuralEdge