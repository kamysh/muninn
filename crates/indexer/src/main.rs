mod watcher;

use muninn_core::{
    config::{GlobalConfig, RepoConfig, EffectiveConfig},
    db,
    embeddings::{make_backend, expected_dimension},
    pipeline::index_repo,
    store,
    types::{BatchOutcome, IndexState},
};
use std::collections::HashSet;
use std::sync::Arc;
use tokio::sync::Mutex;
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

    // Track which repos have an active watcher task so we don't spawn duplicates.
    let mut watched: HashSet<Uuid> = HashSet::new();

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
    watched: &mut HashSet<Uuid>,
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
            if watched.contains(&repo.id) {
                // indexed_at was reset via `muninn reindex` — run a background full reindex.
                tracing::info!("reindexing {} (triggered by muninn reindex)", repo.path);
                let pool2 = pool.clone();
                let embedder: Arc<dyn muninn_core::embeddings::EmbeddingBackend> =
                    Arc::from(make_backend(&eff.embeddings));
                let batch_size = eff.embeddings.batch_size;
                let repo_id = repo.id;
                let repo_path_owned = repo_path.to_path_buf();
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
                                    repo_path_owned.display()
                                );
                            } else {
                                tracing::info!("reindex of {} complete", repo_path_owned.display());
                            }
                        }
                        Err(e) => tracing::error!("reindex of {} failed: {}", repo_path_owned.display(), e),
                    }
                });
            }
            // else: repo registered but never indexed — user must run `muninn index <path>`
            continue;
        }

        // indexed_at IS NOT NULL — start watcher if not already watching.
        if watched.contains(&repo.id) {
            continue;
        }

        tracing::info!("starting watcher for {}", repo.path);
        watched.insert(repo.id);

        let pool2 = pool.clone();
        let embedder: Arc<dyn muninn_core::embeddings::EmbeddingBackend> =
            Arc::from(make_backend(&eff.embeddings));
        let debounce = eff.watcher.debounce_ms;
        let id = repo.id;
        let repo_path_owned = repo_path.to_path_buf();
        let initial_state = Arc::new(Mutex::new(IndexState::Watching));

        tokio::spawn(async move {
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
    }
}
