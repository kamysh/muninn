use serde::{Deserialize, Serialize};
use uuid::Uuid;
use chrono::{DateTime, Utc};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LineRange {
    pub start: u32,
    pub end: u32,
}

impl LineRange {
    pub fn is_valid(&self) -> bool {
        self.start <= self.end
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Repo {
    pub id: Uuid,
    pub path: String,
    pub name: String,
    pub indexed_at: Option<DateTime<Utc>>,
    pub config: Option<serde_json::Value>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Chunk {
    pub id: Uuid,
    pub repo_id: Uuid,
    pub file_path: String,
    pub range: LineRange,
    pub content: String,
    pub embedding: Option<Vec<f32>>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SearchResult {
    pub chunk: Chunk,
    pub score: f32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Symbol {
    pub name: String,
    pub kind: SymbolKind,
    pub file_path: String,
    pub range: LineRange,
    pub chunk_id: Uuid,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum SymbolKind {
    Function,
    Class,
    Module,
    Import,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum StructuralRelation {
    Calls,
    Imports,
    Defines,
    InheritsFrom,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StructuralEdge {
    pub from: Uuid,
    pub to: Uuid,
    pub relation: StructuralRelation,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum IndexState {
    Unindexed,
    Indexing,
    Indexed,
    Watching,
    Stale,
}

/// Cosine similarity score in [0, 1]. Spec: Similarity record.
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub struct Similarity(pub f32);

impl Similarity {
    pub fn new(value: f32) -> Self {
        Self(value.clamp(0.0, 1.0))
    }

    pub fn value(self) -> f32 {
        self.0
    }
}