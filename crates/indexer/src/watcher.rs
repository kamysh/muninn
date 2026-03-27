use notify::{Watcher, RecursiveMode, Event, EventKind};
use std::path::PathBuf;
use std::sync::Arc;
use std::time::Duration;
use tokio::sync::mpsc;
use tokio::sync::Mutex;
use sqlx::PgPool;
use uuid::Uuid;
use anyhow::Result;
use ai_mem_core::embeddings::EmbeddingBackend;
use ai_mem_core::types::IndexState;
use crate::pipeline::index_file;

pub async fn watch_repo(
    pool: PgPool,
    repo_id: Uuid,
    repo_path: PathBuf,
    embedder: Arc<dyn EmbeddingBackend>,
    debounce_ms: u64,
    state: Arc<Mutex<IndexState>>,
    expected_dim: usize,
) -> Result<()> {
    let (tx, mut rx) = mpsc::channel::<PathBuf>(256);

    let mut watcher = notify::recommended_watcher(move |res: notify::Result<Event>| {
        if let Ok(event) = res {
            match event.kind {
                EventKind::Create(_) | EventKind::Modify(_) | EventKind::Remove(_) => {
                    for path in event.paths {
                        let _ = tx.blocking_send(path);
                    }
                }
                _ => {}
            }
        }
    })?;

    watcher.watch(&repo_path, RecursiveMode::Recursive)?;
    tracing::info!("watching {} for changes", repo_path.display());

    let debounce = Duration::from_millis(debounce_ms);

    loop {
        let Some(first) = rx.recv().await else { break };
        let mut batch = vec![first];

        // Transition to Stale (changes detected, not yet reindexed)
        *state.lock().await = IndexState::Stale;

        // collect more events within the debounce window
        let _ = tokio::time::timeout(debounce, async {
            loop {
                match rx.recv().await {
                    Some(p) => batch.push(p),
                    None => break,
                }
            }
        }).await;

        batch.sort();
        batch.dedup();

        // Transition Stale → Indexing
        *state.lock().await = IndexState::Indexing;

        for path in batch {
            if path.exists() {
                if let Err(e) = index_file(&pool, repo_id, &path, embedder.as_ref(), 4096, expected_dim).await {
                    tracing::warn!("incremental index error for {}: {}", path.display(), e);
                }
            } else {
                if let Err(e) = ai_mem_core::store::delete_file_chunks(
                    &pool, repo_id,
                    path.to_string_lossy().as_ref(),
                ).await {
                    tracing::warn!("failed to delete chunks for {}: {}", path.display(), e);
                }
            }
        }

        // finishIndex: Indexing → Indexed
        *state.lock().await = IndexState::Indexed;
        // attachWatcher: Indexed → Watching
        *state.lock().await = IndexState::Watching;
    }

    Ok(())
}