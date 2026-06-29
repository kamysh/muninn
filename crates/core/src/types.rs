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
    /// A foreground job is waiting for the index lock and has asked a background
    /// (daemon) holder to yield. Spec: Muninn.AdvisoryLock. The lock itself is a
    /// PostgreSQL session-scoped advisory lock, not a column.
    pub preempt_requested: bool,
    /// Set by `muninn pause`; the daemon skips paused repos (no reindex, no
    /// watcher) without dropping data. Cleared by `muninn resume`.
    pub paused: bool,
}

/// Which tier a chunk belongs to. Spec: Muninn.Types.Tier.
/// Tier 1 (first-party) is embedded eagerly and ranked at full weight; Tier 2
/// (vendored) is embedded lazily by the daemon and down-weighted in search.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Tier {
    Tier1,
    Tier2,
}

impl Tier {
    pub fn as_i16(self) -> i16 {
        match self {
            Tier::Tier1 => 1,
            Tier::Tier2 => 2,
        }
    }
    pub fn from_i16(v: i16) -> Option<Tier> {
        match v {
            1 => Some(Tier::Tier1),
            2 => Some(Tier::Tier2),
            _ => None,
        }
    }
}

/// A chunk's embedding lifecycle state. Spec: Muninn.Types.EmbeddingState.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum EmbeddingState {
    /// Vector present.
    Embedded,
    /// Tier-2 chunk awaiting daemon backfill (full-text searchable only).
    Pending,
    /// Embedder returned an empty vector (distinct from Pending).
    Absent,
}

impl EmbeddingState {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Embedded => "embedded",
            Self::Pending => "pending",
            Self::Absent => "absent",
        }
    }
    /// Parse from the DB text representation (named to avoid colliding with the
    /// std `FromStr::from_str` trait method).
    pub fn from_db_str(s: &str) -> Option<EmbeddingState> {
        match s {
            "embedded" => Some(Self::Embedded),
            "pending" => Some(Self::Pending),
            "absent" => Some(Self::Absent),
            _ => None,
        }
    }
}

/// SHA-256 of chunk content, used to deduplicate identical Tier-2 chunks so the
/// daemon embeds each unique content only once. Computed for all chunks.
pub fn content_sha256(content: &str) -> Vec<u8> {
    use sha2::{Digest, Sha256};
    Sha256::digest(content.as_bytes()).to_vec()
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Chunk {
    pub id: Uuid,
    pub repo_id: Uuid,
    pub file_path: String,
    pub range: LineRange,
    pub content: String,
    pub embedding: Option<Vec<f32>>,
    /// Tier 1 (first-party) or Tier 2 (vendored). Spec: Muninn.Types.Chunk.tier.
    pub tier: Tier,
    /// Embedding lifecycle. Spec: Muninn.Types.Chunk.embeddingState.
    pub embedding_state: EmbeddingState,
    /// SHA-256 of `content` for Tier-2 dedup; set at index time for all chunks.
    pub content_hash: Option<Vec<u8>>,
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

/// Who holds the indexing lock during an `Indexing` transition.
/// Spec: Muninn.AdvisoryLock.HolderKind (the *task* identity used by
/// Muninn.IndexFsm.Indexing — NOT a property of the advisory lock itself, which
/// records no holder). The CLI indexes as `Fg`, the daemon as `Bg`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum HolderKind {
    /// Foreground CLI job; never preempted.
    Fg,
    /// Background daemon; yields to a waiting foreground job.
    Bg,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum IndexState {
    Unindexed,
    /// A (re)index is running; the lock is held by this task kind.
    /// Spec: Muninn.IndexFsm.IndexState.Indexing : HolderKind → IndexState.
    Indexing(HolderKind),
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
    fn tier_round_trips_i16() {
        assert_eq!(Tier::from_i16(1), Some(Tier::Tier1));
        assert_eq!(Tier::from_i16(2), Some(Tier::Tier2));
        assert_eq!(Tier::Tier2.as_i16(), 2);
        assert_eq!(Tier::from_i16(7), None);
    }

    #[test]
    fn embedding_state_round_trips_str() {
        assert_eq!(
            EmbeddingState::from_db_str("pending"),
            Some(EmbeddingState::Pending)
        );
        assert_eq!(EmbeddingState::Embedded.as_str(), "embedded");
        assert_eq!(EmbeddingState::from_db_str("nonsense"), None);
    }

    #[test]
    fn content_sha256_is_stable_and_distinct() {
        assert_eq!(content_sha256("abc"), content_sha256("abc"));
        assert_ne!(content_sha256("abc"), content_sha256("abd"));
        assert_eq!(content_sha256("abc").len(), 32);
    }

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
            if !(0.0..=1.0).contains(&v) || v.is_nan() {
                return quickcheck::TestResult::discard();
            }
            quickcheck::TestResult::from_bool((Similarity::new(v).value() - v).abs() < f32::EPSILON)
        }
    }

    // ── IndexState / HolderKind (spec: Muninn.IndexFsm, Muninn.AdvisoryLock) ──

    #[test]
    fn holder_kind_distinguishes_fg_from_bg() {
        assert_ne!(HolderKind::Fg, HolderKind::Bg);
        assert_eq!(HolderKind::Fg, HolderKind::Fg);
    }

    #[test]
    fn indexing_holder_is_part_of_equality() {
        // The holder is part of the state's identity: an Fg index and a Bg index
        // are different states (this is what the spec's HolderKind parameter buys).
        assert_ne!(
            IndexState::Indexing(HolderKind::Fg),
            IndexState::Indexing(HolderKind::Bg)
        );
        assert_eq!(
            IndexState::Indexing(HolderKind::Bg),
            IndexState::Indexing(HolderKind::Bg)
        );
    }

    #[test]
    fn index_state_serde_round_trip_all_variants() {
        let variants = [
            IndexState::Unindexed,
            IndexState::Indexing(HolderKind::Fg),
            IndexState::Indexing(HolderKind::Bg),
            IndexState::Indexed,
            IndexState::Watching,
            IndexState::Stale,
        ];
        for v in variants {
            let json = serde_json::to_string(&v).expect("serialize");
            let back: IndexState = serde_json::from_str(&json).expect("deserialize");
            assert_eq!(v, back, "round-trip mismatch for {v:?}");
        }
    }

    #[test]
    fn indexing_serde_preserves_holder() {
        // A Bg index must not deserialize back as an Fg index (the holder is
        // carried through the wire format, not dropped).
        let json = serde_json::to_string(&IndexState::Indexing(HolderKind::Bg)).unwrap();
        let back: IndexState = serde_json::from_str(&json).unwrap();
        assert_eq!(back, IndexState::Indexing(HolderKind::Bg));
        assert_ne!(back, IndexState::Indexing(HolderKind::Fg));
    }

    quickcheck! {
        // Every IndexState (including both holder kinds) survives a JSON
        // serialize→deserialize round-trip unchanged.
        fn prop_index_state_json_round_trip(pick: u8) -> bool {
            let state = match pick % 6 {
                0 => IndexState::Unindexed,
                1 => IndexState::Indexing(HolderKind::Fg),
                2 => IndexState::Indexing(HolderKind::Bg),
                3 => IndexState::Indexed,
                4 => IndexState::Watching,
                _ => IndexState::Stale,
            };
            let json = serde_json::to_string(&state).unwrap();
            let back: IndexState = serde_json::from_str(&json).unwrap();
            back == state
        }

        // HolderKind round-trips and the two kinds never collide through serde.
        fn prop_holder_kind_round_trip(fg: bool) -> bool {
            let k = if fg { HolderKind::Fg } else { HolderKind::Bg };
            let json = serde_json::to_string(&k).unwrap();
            let back: HolderKind = serde_json::from_str(&json).unwrap();
            back == k
        }
    }
}
