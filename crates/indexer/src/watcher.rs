use anyhow::Result;
use muninn_core::embeddings::EmbeddingBackend;
use muninn_core::pipeline::{build_excludes, index_file};
use muninn_core::types::{HolderKind, IndexState, Tier};
use notify::{Event, EventKind, RecursiveMode, Watcher};
use std::path::PathBuf;
use std::sync::Arc;
use std::time::Duration;
use tokio::sync::mpsc;
use tokio::sync::Mutex;
use tokio_postgres::Client;
use uuid::Uuid;

// Client, ids, embedder, debounce, shared state and config knobs — all distinct
// concerns; bundling them into a struct would not improve clarity.
#[allow(clippy::too_many_arguments)]
pub async fn watch_repo(
    mut client: Arc<Client>,
    repo_id: Uuid,
    repo_path: PathBuf,
    embedder: Arc<dyn EmbeddingBackend>,
    debounce_ms: u64,
    state: Arc<Mutex<IndexState>>,
    embed_batch_size: usize,
    expected_dim: usize,
    exclude: Vec<String>,
    vendor: Vec<String>,
) -> Result<()> {
    // Bring this repo's schema current via kryzhen before the watcher starts
    // writing to it — this is the steady-state path most repos spend most of
    // their time on (not reindex), so it must backfill too, not just
    // register_repo/index_repo. `client` is a freshly-constructed Arc with no
    // other holders yet, so get_mut succeeds.
    {
        let schema = muninn_core::store::repo_schema(repo_id);
        let client_mut = Arc::get_mut(&mut client).ok_or_else(|| {
            anyhow::anyhow!("watch_repo: client Arc unexpectedly shared at startup")
        })?;
        muninn_core::db::run_repo_migrations(client_mut, &schema).await?;
    }

    let configured = muninn_core::family_policy::runtime::policy(client.as_ref(), repo_id)
        .await?
        .is_some();
    if configured
        || muninn_core::repo_resolver::discover_git_checkout(&repo_path)
            .await?
            .is_some_and(|g| g.root == repo_path)
    {
        let client =
            Arc::try_unwrap(client).map_err(|_| anyhow::anyhow!("watcher client is shared"))?;
        return watch_family(
            client,
            repo_id,
            repo_path,
            embedder,
            debounce_ms,
            embed_batch_size,
            expected_dim,
            exclude,
            vendor,
        )
        .await;
    }

    let overrides = build_excludes(&repo_path, &exclude);
    let vendor_overrides = build_excludes(&repo_path, &vendor);

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
            // The watcher is the daemon; its reindex always holds the lock as Bg.
            *s = IndexState::Indexing(HolderKind::Bg);
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
                // Classify the changed file: Tier 2 if it matches the vendor
                // override, else Tier 1. Spec: Muninn.Config.classify.
                let tier = path
                    .strip_prefix(&repo_path)
                    .map(|rel| {
                        if muninn_core::pipeline::path_excluded(&vendor_overrides, rel) {
                            Tier::Tier2
                        } else {
                            Tier::Tier1
                        }
                    })
                    .unwrap_or(Tier::Tier1);
                match index_file(
                    &client,
                    repo_id,
                    &path,
                    embedder.as_ref(),
                    1500,
                    embed_batch_size,
                    expected_dim,
                    tier,
                )
                .await
                {
                    Ok(()) => any_succeeded = true,
                    Err(e) => {
                        tracing::warn!("incremental index error for {}: {}", path.display(), e)
                    }
                }
            } else {
                let fp = path.to_string_lossy();
                if let Err(e) =
                    muninn_core::store::delete_file_chunks(&client, repo_id, fp.as_ref()).await
                {
                    tracing::warn!("failed to delete chunks for {}: {}", path.display(), e);
                } else {
                    if let Err(e) =
                        muninn_core::graph::delete_file_symbols(&client, repo_id, fp.as_ref()).await
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
                    *s == IndexState::Indexing(HolderKind::Bg),
                    "finishIndex: expected Indexing(Bg), got {:?}",
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
                    *s == IndexState::Indexing(HolderKind::Bg),
                    "stay-Stale: expected Indexing(Bg), got {:?}",
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

/// A family watcher watches available worktrees and Git administrative changes.
/// Periodic discovery catches creation/removal and retries suspended checkouts.
#[allow(clippy::too_many_arguments)]
async fn watch_family(
    mut client: Client,
    repo_id: Uuid,
    root: PathBuf,
    embedder: Arc<dyn EmbeddingBackend>,
    debounce_ms: u64,
    batch: usize,
    dimension: usize,
    exclude: Vec<String>,
    vendor: Vec<String>,
) -> Result<()> {
    let (tx, mut rx) = mpsc::channel::<PathBuf>(1024);
    let overflow = Arc::new(std::sync::atomic::AtomicBool::new(false));
    let lost = Arc::clone(&overflow);
    let mut watcher =
        notify::recommended_watcher(move |event: notify::Result<Event>| match event {
            Ok(event)
                if matches!(
                    event.kind,
                    EventKind::Create(_) | EventKind::Modify(_) | EventKind::Remove(_)
                ) =>
            {
                for path in event.paths {
                    if tx.try_send(path).is_err() {
                        lost.store(true, std::sync::atomic::Ordering::Relaxed);
                    }
                }
            }
            Err(_) => {
                lost.store(true, std::sync::atomic::Ordering::Relaxed);
            }
            _ => {}
        })?;
    let mut watched = std::collections::HashSet::new();
    let mut changed: Option<Vec<PathBuf>> = None;
    loop {
        // Install watches before scanning so edits during reconciliation are
        // queued for another pass. Failed/missing roots will be retried.
        if let Some(git) = muninn_core::repo_resolver::discover_git_checkout(&root).await? {
            let entries = muninn_core::repo_resolver::list_git_worktrees(&git.common_dir).await?;
            let mut live = std::collections::HashSet::new();
            for path in entries
                .into_iter()
                .map(|e| e.path)
                .chain(std::iter::once(git.common_dir))
            {
                if path.is_dir() {
                    live.insert(path.clone());
                    if !watched.contains(&path) {
                        match watcher.watch(&path, RecursiveMode::Recursive) {
                            Ok(()) => {
                                watched.insert(path);
                            }
                            Err(e) => {
                                tracing::warn!("cannot watch {}: {}", path.display(), e);
                                overflow.store(true, std::sync::atomic::Ordering::Relaxed);
                            }
                        }
                    }
                }
            }
            watched.retain(|path| {
                if live.contains(path) {
                    true
                } else {
                    let _ = watcher.unwatch(path);
                    false
                }
            });
        }
        if watched.is_empty() {
            watcher.watch(&root, RecursiveMode::Recursive)?;
            watched.insert(root.clone());
        }
        let git_family = muninn_core::repo_resolver::discover_git_checkout(&root)
            .await?
            .is_some_and(|g| g.root == root);
        let result = if git_family {
            muninn_core::worktrees::reconcile_changed_family(
                &mut client,
                repo_id,
                &root,
                Arc::clone(&embedder),
                batch,
                dimension,
                &exclude,
                &vendor,
                |_, _, _| {},
                changed.as_deref(),
            )
            .await
        } else {
            muninn_core::pipeline::index_repo(
                &mut client,
                repo_id,
                &root,
                Arc::clone(&embedder),
                batch,
                dimension,
                &exclude,
                &vendor,
                |_, _, _| {},
            )
            .await
        };
        let mut retry = Vec::new();
        let mut retry_all = false;
        match result {
            Ok((_, skips)) => {
                for skip in skips {
                    tracing::warn!(
                        "retained index for {}: {}",
                        skip.path.display(),
                        skip.reason
                    );
                    retry.push(skip.path);
                }
            }
            Err(e) => {
                tracing::warn!(root = %root.display(), "family reconciliation failed: {e:#}");
                retry_all = true;
                retry.push(root.clone());
            }
        }
        tokio::select! {
            event=rx.recv()=>{
                if let Some(path)=event {retry.push(path);} else {return Ok(());}
                tokio::time::sleep(Duration::from_millis(debounce_ms)).await;
                while let Ok(path)=rx.try_recv(){retry.push(path);}
            }
            _=tokio::time::sleep(Duration::from_secs(60))=>{}
        }
        changed = if retry_all || overflow.swap(false, std::sync::atomic::Ordering::Relaxed) {
            None
        } else {
            Some(retry)
        };
    }
}
