use notify::{Watcher, RecursiveMode, Event, EventKind};
use std::path::PathBuf;
use std::sync::Arc;
use std::time::Duration;
use tokio::sync::mpsc;
use tokio::sync::Mutex;
use sqlx::PgPool;
use uuid::Uuid;
use anyhow::Result;
use ignore::gitignore::GitignoreBuilder;
use muninn_core::embeddings::EmbeddingBackend;
use muninn_core::types::IndexState;
use muninn_core::pipeline::index_file;

pub async fn watch_repo(
    pool: PgPool,
    repo_id: Uuid,
    repo_path: PathBuf,
    embedder: Arc<dyn EmbeddingBackend>,
    debounce_ms: u64,
    state: Arc<Mutex<IndexState>>,
    embed_batch_size: usize,
    expected_dim: usize,
) -> Result<()> {
    // Build gitignore matcher from the repo root so the watcher skips the same
    // files that index_repo (WalkBuilder with git_ignore=true) would skip.
    // Build gitignore from ALL nested .gitignore files so that patterns like
    // BLD/ defined in subdirectory .gitignore files are respected.
    let gitignore = {
        let mut builder = GitignoreBuilder::new(&repo_path);
        let walker = ignore::WalkBuilder::new(&repo_path)
            .git_ignore(false)
            .hidden(false)
            .build();
        for entry in walker.filter_map(|e| e.ok()) {
            if entry.file_name() == ".gitignore" && entry.path().is_file() {
                if let Some(err) = builder.add(entry.path()) {
                    tracing::warn!(
                        "failed to load gitignore {}: {}",
                        entry.path().display(), err
                    );
                }
            }
        }
        match builder.build() {
            Ok(gi) => gi,
            Err(e) => {
                tracing::warn!("failed to build gitignore matcher for {}: {}", repo_path.display(), e);
                ignore::gitignore::Gitignore::empty()
            }
        }
    };

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
                "detectChange: expected Watching or Stale, got {:?}", *s
            );
            *s = IndexState::Stale;
        }

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

        // reindexStale: Stale → Indexing
        {
            let mut s = state.lock().await;
            debug_assert!(
                *s == IndexState::Stale,
                "reindexStale: expected Stale, got {:?}", *s
            );
            *s = IndexState::Indexing;
        }

        let mut any_succeeded = false;
        for path in batch {
            // Skip .git internals and gitignored paths (mirrors WalkBuilder in index_repo)
            let is_git_internal = path.components().any(|c| c.as_os_str() == ".git");
            let is_ignored = path.strip_prefix(&repo_path)
                .map(|rel| gitignore.matched(rel, false).is_ignore())
                .unwrap_or(false);
            if is_git_internal || is_ignored {
                continue;
            }

            if path.is_file() {
                match index_file(
                    &pool,
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
                    Err(e) => tracing::warn!("incremental index error for {}: {}", path.display(), e),
                }
            } else {
                if let Err(e) = muninn_core::store::delete_file_chunks(
                    &pool, repo_id,
                    path.to_string_lossy().as_ref(),
                ).await {
                    tracing::warn!("failed to delete chunks for {}: {}", path.display(), e);
                } else {
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
                    "finishIndex: expected Indexing, got {:?}", *s
                );
                *s = IndexState::Indexed;
            }
        } else {
            tracing::warn!("watcher batch for repo {} had no successes — staying Stale", repo_id);
            {
                let mut s = state.lock().await;
                debug_assert!(
                    *s == IndexState::Indexing,
                    "stay-Stale: expected Indexing, got {:?}", *s
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
                "attachWatcher: expected Indexed, got {:?}", *s
            );
            *s = IndexState::Watching;
        }
    }

    Ok(())
}
