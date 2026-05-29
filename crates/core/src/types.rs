use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};
use uuid::Uuid;

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct LineRange {
    pub start: u32,
    pub end: u32,
}

impl LineRange {
    pub fn is_valid(&self) -> bool {
        self.start <= self.end
    }
}

/// Who holds a repo's indexing lock. Spec: Muninn.IndexFsm.HolderKind.
/// Foreground (CLI) jobs are interactive and never preempted; background
/// (daemon) reindexes yield the lock to a waiting foreground job.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum HolderKind {
    Fg,
    Bg,
}

impl HolderKind {
    pub fn as_str(self) -> &'static str {
        match self {
            HolderKind::Fg => "fg",
            HolderKind::Bg => "bg",
        }
    }

    pub fn from_db(s: &str) -> Option<Self> {
        match s {
            "fg" => Some(HolderKind::Fg),
            "bg" => Some(HolderKind::Bg),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Repo {
    pub id: Uuid,
    pub path: String,
    pub name: String,
    pub indexed_at: Option<DateTime<Utc>>,
    /// True after the first successful index; survives reindex reset.
    /// Used by the daemon to distinguish "never indexed" from "needs reindex".
    pub ever_indexed: bool,
    /// Embedding vector dimension used when this repo was registered.
    /// Authoritative: the per-repo chunks table was created with VECTOR(embedding_dim).
    pub embedding_dim: u32,
    /// Heartbeat-based distributed mutex. NULL = unlocked. non-NULL = locked;
    /// holder pulses every 60 s. Stale (dead holder) if older than 2 minutes.
    /// Spec: Muninn.Concurrency.
    pub indexing_heartbeat: Option<DateTime<Utc>>,
    /// Who holds the lock. NULL iff indexing_heartbeat is NULL.
    pub lock_holder: Option<HolderKind>,
    /// A foreground job is waiting and has asked a background holder to yield.
    pub preempt_requested: bool,
}

impl Repo {
    /// True if the indexing lock is currently held by a live process.
    /// A heartbeat older than 2 minutes means the holder is dead (stale lock).
    pub fn is_lock_live(&self) -> bool {
        match self.indexing_heartbeat {
            None => false,
            Some(hb) => (Utc::now() - hb) < chrono::Duration::seconds(120),
        }
    }
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

/// Outcome of processing a batch of files during indexing.
/// Spec: Muninn.Index.BatchOutcome.
/// NoneSucceeded is intentionally absent: a totally-failed batch must NOT
/// advance to Indexed.  Only a batch where at least one file was successfully
/// indexed may close the Indexing state.
#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub enum BatchOutcome {
    /// Every file in the batch was indexed without error.
    AllSucceeded,
    /// At least one file indexed; others were warned and skipped.
    SomeSucceeded,
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn line_range_valid_when_start_equals_end() {
        assert!(LineRange { start: 42, end: 42 }.is_valid());
    }

    #[test]
    fn line_range_invalid_when_start_greater() {
        assert!(!LineRange { start: 100, end: 0 }.is_valid());
    }

    #[test]
    fn similarity_clamps_above_one() {
        assert_eq!(Similarity::new(1.5).value(), 1.0);
    }

    #[test]
    fn similarity_clamps_below_zero() {
        assert_eq!(Similarity::new(-0.3).value(), 0.0);
    }

    #[test]
    fn similarity_preserves_valid_range() {
        let s = Similarity::new(0.75);
        assert!((s.value() - 0.75).abs() < f32::EPSILON);
    }

    use quickcheck::quickcheck;

    quickcheck! {
        fn prop_line_range_valid_iff_start_le_end(start: u32, end: u32) -> bool {
            let r = LineRange { start, end };
            r.is_valid() == (start <= end)
        }

        fn prop_similarity_always_in_unit_interval(v: f32) -> quickcheck::TestResult {
            if v.is_nan() {
                return quickcheck::TestResult::discard();
            }
            let s = Similarity::new(v);
            quickcheck::TestResult::from_bool(s.value() >= 0.0 && s.value() <= 1.0)
        }

        fn prop_similarity_identity_on_valid_input(v: f32) -> quickcheck::TestResult {
            if v < 0.0 || v > 1.0 || v.is_nan() {
                return quickcheck::TestResult::discard();
            }
            quickcheck::TestResult::from_bool((Similarity::new(v).value() - v).abs() < f32::EPSILON)
        }
    }
}