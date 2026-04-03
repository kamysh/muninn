mod watcher;

use muninn_core::{
    config::{GlobalConfig, RepoConfig, EffectiveConfig},
    db,
    embeddings::{make_backend, expected_dimension},
    pipeline::index_repo,
    store,
    types::{BatchOutcome, IndexState},
};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::Mutex;
use tokio::task::JoinHandle;
use uuid::Uuid;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    tracing_subscriber::fmt::init();

    let cfg = GlobalConfig::load()?;
    let pool = db::connect_with_app_name(&cfg.database, "muninn-index").await?;

    // Dedicated connection for LISTEN/NOTIFY.
    // PgListener reconnects automatically; combined with the 60 s fallback poll
    // this means no notifications are permanently lost.
    let mut listener = db::connect_listener(&cfg.database).await?;
    listener.listen("muninn_repos_changed").await?;

    tracing::info!("muninn-index started — watching all repos registered in the database");

    // Map from repo_id to the running watcher task handle.
    // Storing the handle (not just the id) lets us abort the watcher before a
    // full reindex so both cannot mutate the same chunks table concurrently.
    let mut watched: HashMap<Uuid, JoinHandle<()>> = HashMap::new();

    // Initial scan
    scan_and_dispatch(&cfg, &pool, &mut watched).await;

    loop {
        // Wait for a NOTIFY or fall back to a 60 s poll for resilience.
        tokio::select! {
            result = listener.recv() => {
                match result {
                    Ok(_) => tracing::debug!("received muninn_repos_changed notification"),
                    Err(e) => tracing::warn!("PgListener error (will reconnect): {}", e),
                }
            }
            _ = tokio::time::sleep(std::time::Duration::from_secs(60)) => {
                tracing::debug!("60 s poll tick");
            }
            _ = tokio::signal::ctrl_c() => {
                tracing::info!("shutting down");
                break;
            }
        }
        scan_and_dispatch(&cfg, &pool, &mut watched).await;
    }

    Ok(())
}

/// Query the repos table and dispatch watcher / reindex tasks as needed.
async fn scan_and_dispatch(
    cfg: &GlobalConfig,
    pool: &sqlx::PgPool,
    watched: &mut HashMap<Uuid, JoinHandle<()>>,
) {
    let repos = match store::list_repos(pool).await {
        Ok(r) => r,
        Err(e) => {
            tracing::error!("failed to list repos: {}", e);
            return;
        }
    };

    for repo in repos {
        let repo_path = std::path::Path::new(&repo.path);

        let dir_name = repo_path
            .file_name()
            .unwrap_or_default()
            .to_string_lossy()
            .to_string();

        let repo_cfg = match RepoConfig::load(repo_path) {
            Ok(c) => c,
            Err(e) => {
                tracing::warn!("skipping {}: could not load repo config: {}", repo.path, e);
                continue;
            }
        };
        let eff = EffectiveConfig::merge(cfg, &repo_cfg, &dir_name);
        let repo_dim = expected_dimension(&eff.embeddings);

        // DimFrozen check: stored dimension must match configured backend.
        if repo.embedding_dim as usize != repo_dim {
            tracing::error!(
                "repo {} stored embedding_dim {} but configured backend yields {}; \
                 unregister + re-index to switch backends",
                repo.path, repo.embedding_dim, repo_dim
            );
            continue;
        }

        if repo.indexed_at.is_none() {
            if watched.contains_key(&repo.id) {
                // indexed_at was reset via `muninn reindex`.
                // Abort the watcher first to prevent it from racing with index_repo
                // (both would delete-and-reinsert chunks for the same files).
                if let Some(handle) = watched.remove(&repo.id) {
                    handle.abort();
                    tracing::info!(
                        "paused watcher for {} to run full reindex",
                        repo.path
                    );
                }
                // Spawn background full reindex.  After success, notify the daemon so
                // it re-scans and re-attaches the watcher (startReindex → Indexing →
                // Indexed → attachWatcher → Watching in the spec state machine).
                let pool2 = pool.clone();
                let embedder: Arc<dyn muninn_core::embeddings::EmbeddingBackend> =
                    Arc::from(make_backend(&eff.embeddings));
                let batch_size = eff.embeddings.batch_size;
                let repo_id = repo.id;
                let repo_path_owned = repo_path.to_path_buf();
                let repo_path_str = repo.path.clone();
                tokio::spawn(async move {
                    let state = Arc::new(Mutex::new(IndexState::Indexing));
                    match index_repo(
                        &pool2, repo_id, &repo_path_owned, embedder,
                        batch_size, repo_dim, |_, _, _| {},
                    )
                    .await
                    {
                        Ok(outcome) => {
                            {
                                let mut s = state.lock().await;
                                debug_assert_eq!(*s, IndexState::Indexing);
                                *s = IndexState::Indexed;
                            }
                            if outcome == BatchOutcome::SomeSucceeded {
                                tracing::warn!(
                                    "reindex of {} completed with some files skipped",
                                    repo_path_str
                                );
                            } else {
                                tracing::info!("reindex of {} complete", repo_path_str);
                            }
                            // mark_indexed was called inside index_repo; now notify
                            // so the daemon re-scans and re-attaches the watcher promptly.
                            if let Err(e) = store::notify_repos_changed(&pool2).await {
                                tracing::warn!(
                                    "reindex of {} complete but notify failed: {}",
                                    repo_path_str, e
                                );
                            }
                        }
                        Err(e) => tracing::error!(
                            "reindex of {} failed: {}", repo_path_str, e
                        ),
                    }
                });
            }
            // else: registered but never indexed — user must run `muninn index <path>`
            continue;
        }

        // indexed_at IS NOT NULL — start watcher if not already watching.
        if watched.contains_key(&repo.id) {
            continue;
        }

        tracing::info!("starting watcher for {}", repo.path);

        let pool2 = pool.clone();
        let embedder: Arc<dyn muninn_core::embeddings::EmbeddingBackend> =
            Arc::from(make_backend(&eff.embeddings));
        let debounce = eff.watcher.debounce_ms;
        let id = repo.id;
        let repo_path_owned = repo_path.to_path_buf();
        let initial_state = Arc::new(Mutex::new(IndexState::Watching));

        let handle = tokio::spawn(async move {
            if let Err(e) = watcher::watch_repo(
                pool2, id, repo_path_owned, embedder,
                debounce, initial_state,
                eff.embeddings.batch_size, repo_dim,
            )
            .await
            {
                tracing::error!("watcher error: {}", e);
            }
        });

        watched.insert(repo.id, handle);
    }
}
