//! Integration tests for tiered indexing (pipeline.rs::index_repo).
//!
//! Indexes a real temp repo and asserts each chunk's tier / embedding_state /
//! content_hash / embedding against the per-repo chunks table. Tier 1 chunks are
//! embedded eagerly; Tier 2 (vendored) chunks are full-text-only and Pending.
//!
//! Run against the live DB:
//!   nix develop --command cargo test --test tiered_indexing
//! DB config comes from ~/.config/muninn/config.toml + ~/.pgpass.

use futures::FutureExt;
use muninn_core::{
    config::GlobalConfig,
    db,
    embeddings::EmbeddingBackend,
    pipeline::index_repo,
    store::{self, chunks_table},
    types::{EmbeddingState, Tier},
};
use std::future::Future;
use std::panic::AssertUnwindSafe;
use std::pin::Pin;
// (no std::path::Path import needed; tmp.path() returns &Path)
use std::sync::Arc;
use tokio_postgres::Client;
use uuid::Uuid;

const TEST_DIM: usize = 64;

// ── helpers ────────────────────────────────────────────────────────────────

async fn connect() -> Client {
    let cfg = GlobalConfig::load().expect("load ~/.config/muninn/config.toml");
    db::connect(&cfg.database)
        .await
        .expect("connect to muninn DB")
}

/// A stub embedder that returns a fixed-dimension non-empty vector per text.
struct StubEmbedder {
    dim: usize,
}
impl EmbeddingBackend for StubEmbedder {
    fn embed<'a>(
        &'a self,
        texts: &'a [String],
    ) -> Pin<Box<dyn Future<Output = anyhow::Result<Vec<Vec<f32>>>> + Send + 'a>> {
        let dim = self.dim;
        let n = texts.len();
        Box::pin(async move { Ok((0..n).map(|_| vec![0.1f32; dim]).collect()) })
    }
}

/// One chunk row's tiering fields, read back from the per-repo table.
struct ChunkRow {
    file_path: String,
    tier: i16,
    embedding_state: String,
    has_embedding: bool,
    has_hash: bool,
}

async fn read_chunks(client: &Client, repo_id: Uuid) -> Vec<ChunkRow> {
    let table = chunks_table(repo_id);
    let rows = client
        .query(
            &format!(
                r#"SELECT file_path, tier, embedding_state,
                          (embedding IS NOT NULL) AS has_emb,
                          (content_hash IS NOT NULL) AS has_hash
                   FROM "{table}""#
            ),
            &[],
        )
        .await
        .expect("query chunks");
    rows.iter()
        .map(|r| ChunkRow {
            file_path: r.get("file_path"),
            tier: r.get("tier"),
            embedding_state: r.get("embedding_state"),
            has_embedding: r.get("has_emb"),
            has_hash: r.get("has_hash"),
        })
        .collect()
}

// ── test ───────────────────────────────────────────────────────────────────

#[tokio::test]
async fn foreground_index_splits_tier1_eager_tier2_pending() {
    let client = connect().await;

    // Build a temp repo: first-party src, a vendored node_modules file, and an
    // excluded minified file.
    let tmp = tempfile::tempdir().expect("tempdir");
    let root = tmp.path();
    std::fs::create_dir_all(root.join("src")).unwrap();
    std::fs::create_dir_all(root.join("node_modules/dep")).unwrap();
    std::fs::write(root.join("src/a.rs"), "fn first_party() { let x = 1; }\n").unwrap();
    std::fs::write(
        root.join("node_modules/dep/i.js"),
        "function vendored() { return 2; }\n",
    )
    .unwrap();
    std::fs::write(root.join("bundle.min.js"), "var a=1;var b=2;var c=3;\n").unwrap();

    let repo = store::register_repo(
        &client,
        &format!("/tmp/tiered-test-{}", Uuid::new_v4()),
        "tiered-test",
        TEST_DIM,
    )
    .await
    .expect("register repo");
    let repo_id = repo.id;

    // Run the assertions panic-safe so the test repo is always cleaned up.
    let outcome = AssertUnwindSafe(async {
        let embedder: Arc<dyn EmbeddingBackend> = Arc::new(StubEmbedder { dim: TEST_DIM });
        let exclude = vec!["**/*.min.js".to_string()];
        let vendor = vec!["**/node_modules/**".to_string()];
        index_repo(
            &client,
            repo_id,
            root,
            embedder,
            16,
            TEST_DIM,
            &exclude,
            &vendor,
            |_, _, _| {},
        )
        .await
        .expect("index_repo");

        let chunks = read_chunks(&client, repo_id).await;

        // The excluded *.min.js produced no chunks.
        assert!(
            !chunks
                .iter()
                .any(|c| c.file_path.ends_with("bundle.min.js")),
            "excluded file should have no chunks"
        );

        let src: Vec<&ChunkRow> = chunks
            .iter()
            .filter(|c| c.file_path.ends_with("src/a.rs"))
            .collect();
        assert!(!src.is_empty(), "src/a.rs should have chunks");
        for c in &src {
            assert_eq!(c.tier, Tier::Tier1.as_i16(), "src is Tier 1");
            assert_eq!(c.embedding_state, EmbeddingState::Embedded.as_str());
            assert!(c.has_embedding, "Tier 1 chunk is embedded");
            assert!(c.has_hash, "content_hash set for all chunks");
        }

        let vend: Vec<&ChunkRow> = chunks
            .iter()
            .filter(|c| c.file_path.ends_with("node_modules/dep/i.js"))
            .collect();
        assert!(!vend.is_empty(), "node_modules file should have chunks");
        for c in &vend {
            assert_eq!(c.tier, Tier::Tier2.as_i16(), "node_modules is Tier 2");
            assert_eq!(c.embedding_state, EmbeddingState::Pending.as_str());
            assert!(!c.has_embedding, "Tier 2 chunk has no embedding yet");
            assert!(c.has_hash, "content_hash set for Tier 2 chunk (dedup)");
        }
    })
    .catch_unwind()
    .await;

    // Always clean up the test repo, even on assertion failure, then re-raise.
    let _ = store::delete_repo(&client, repo_id).await;
    drop(tmp); // remove the temp repo dir
    if let Err(panic) = outcome {
        std::panic::resume_unwind(panic);
    }
}
