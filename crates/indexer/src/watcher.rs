use notify::{Event, EventKind, RecursiveMode, Watcher};
use std::path::PathBuf;
use std::sync::Arc;
use std::time::Duration;
use tokio::sync::mpsc;
use tokio::sync::Mutex;
use tokio_postgres::Client;
use uuid::Uuid;
use anyhow::Result;
use muninn_core::embeddings::EmbeddingBackend;
use muninn_core::types::IndexState;
use muninn_core::pipeline::{build_excludes, index_file};

// Client, ids, embedder, debounce, shared state and config knobs — all distinct
// concerns; bundling them into a struct would not improve clarity.
#[allow(clippy::too_many_arguments)]
pub async fn watch_repo(
    client: Arc<Client>,
    repo_id: Uuid,
    repo_path: PathBuf,
    embedder: Arc<dyn EmbeddingBackend>,
    debounce_ms: u64,
    state: Arc<Mutex<IndexState>>,
    embed_batch_size: usize,
    expected_dim: usize,
    exclude: Vec<String>,
) -> Result<()> {
    let overrides = build_excludes(&repo_path, &exclude);

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
        // detectChange: Watching → Stale  (or Stale → Stale on failed-batch re-entry)
        {
            let mut s = state.lock().await;
            debug_assert!(
                *s == IndexState::Watching || *s == IndexState::Stale,
                "detectChange: expected Watching or Stale, got {:?}",
                *s
            );
            *s = IndexState::Stale;
        }

        // collect more events within the debounce window
        let _ = tokio::time::timeout(debounce, async {
            while let Some(p) = rx.recv().await {
                batch.push(p);
            }
        })
        .await;

        batch.sort();
        batch.dedup();

        // reindexStale: Stale → Indexing
        {
            let mut s = state.lock().await;
            debug_assert!(
                *s == IndexState::Stale,
                "reindexStale: expected Stale, got {:?}",
                *s
            );
            *s = IndexState::Indexing;
        }

        let mut any_succeeded = false;
        for path in batch {
            let is_git_internal = path.components().any(|c| c.as_os_str() == ".git");
            let is_excluded = path
                .strip_prefix(&repo_path)
                .map(|rel| muninn_core::pipeline::path_excluded(&overrides, rel))
                .unwrap_or(false);
            if is_git_internal || is_excluded {
                continue;
            }

            if path.is_file() {
                match index_file(
                    &client,
                    repo_id,
                    &path,
                    embedder.as_ref(),
                    1500,
                    embed_batch_size,
                    expected_dim,
                )
                .await
                {
                    Ok(()) => any_succeeded = true,
                    Err(e) => tracing::warn!(
                        "incremental index error for {}: {}",
                        path.display(),
                        e
                    ),
                }
            } else {
                let fp = path.to_string_lossy();
                if let Err(e) =
                    muninn_core::store::delete_file_chunks(&client, repo_id, fp.as_ref()).await
                {
                    tracing::warn!("failed to delete chunks for {}: {}", path.display(), e);
                } else {
                    if let Err(e) =
                        muninn_core::graph::delete_file_symbols(&client, repo_id, fp.as_ref())
                            .await
                    {
                        tracing::warn!(
                            "failed to delete graph nodes for {}: {}",
                            path.display(),
                            e
                        );
                    }
                    any_succeeded = true;
                }
            }
        }

        // BatchOutcome invariant: finishIndex (Indexing → Indexed) requires at
        // least one file successfully processed. A totally-failed batch stays Stale.
        if any_succeeded {
            // finishIndex: Indexing → Indexed
            {
                let mut s = state.lock().await;
                debug_assert!(
                    *s == IndexState::Indexing,
                    "finishIndex: expected Indexing, got {:?}",
                    *s
                );
                *s = IndexState::Indexed;
            }
        } else {
            tracing::warn!(
                "watcher batch for repo {} had no successes — staying Stale",
                repo_id
            );
            {
                let mut s = state.lock().await;
                debug_assert!(
                    *s == IndexState::Indexing,
                    "stay-Stale: expected Indexing, got {:?}",
                    *s
                );
                *s = IndexState::Stale;
            }
            continue;
        }
        // attachWatcher: Indexed → Watching
        {
            let mut s = state.lock().await;
            debug_assert!(
                *s == IndexState::Indexed,
                "attachWatcher: expected Indexed, got {:?}",
                *s
            );
            *s = IndexState::Watching;
        }
    }

    Ok(())
}
