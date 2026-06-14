mod watcher;

use clap::Parser;
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

#[derive(Parser)]
#[command(name = "muninn-index", about = "muninn indexer daemon", version)]
struct Cli {}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let _cli = Cli::parse();
    tracing_subscriber::fmt::init();

    let cfg = GlobalConfig::load()?;
    let client = db::connect_with_app_name(&cfg.database, "muninn-index").await?;
    // Self-apply migrations on startup: the daemon may come up (launchd/systemd)
    // before any CLI command has migrated the DB, and every scan SELECTs the
    // current repo columns. Idempotent. Spec: schema is current before queries.
    let mut migrate_client =
        db::connect_with_app_name(&cfg.database, "muninn-index-migrate").await?;
    db::run_migrations(&mut migrate_client).await?;
    drop(migrate_client);

    // Dedicated connection for LISTEN/NOTIFY.
    // The spawned task drives the connection; notifications arrive via the channel.
    // Combined with the 60 s fallback poll, no notifications are permanently lost.
    let (listen_client, mut notify_rx) = db::connect_listener(&cfg.database).await?;
    listen_client
        .execute("LISTEN muninn_repos_changed", &[])
        .await?;

    tracing::info!("muninn-index started — watching all repos registered in the database");

    // Map from repo_id to the running watcher task handle and the exclude
    // glob list it was started with. Storing the handle lets us abort the
    // watcher before a full reindex; storing the exclude list lets us detect
    // config changes and restart the watcher so newly-excluded paths stop
    // being re-indexed by a stale watcher after a foreground CLI reindex.
    let mut watched: HashMap<Uuid, (JoinHandle<()>, Vec<String>)> = HashMap::new();
    // Track repos with a reindex in flight to prevent duplicate spawns.
    let reindexing: Arc<Mutex<std::collections::HashSet<Uuid>>> =
        Arc::new(Mutex::new(std::collections::HashSet::new()));

    // Initial scan
    scan_and_dispatch(&cfg, &client, &mut watched, &reindexing).await;

    loop {
        // Wait for a NOTIFY or fall back to a 60 s poll for resilience.
        tokio::select! {
            msg = notify_rx.recv() => {
                match msg {
                    Some(_) => tracing::debug!("received muninn_repos_changed notification"),
                    None => tracing::warn!("LISTEN channel closed — continuing on poll"),
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
        scan_and_dispatch(&cfg, &client, &mut watched, &reindexing).await;
    }

    Ok(())
}

/// Query the repos table and dispatch watcher / reindex tasks as needed.
async fn scan_and_dispatch(
    cfg: &GlobalConfig,
    client: &tokio_postgres::Client,
    watched: &mut HashMap<Uuid, (JoinHandle<()>, Vec<String>)>,
    reindexing: &Arc<Mutex<std::collections::HashSet<Uuid>>>,
) {
    let repos = match store::list_repos(client).await {
        Ok(r) => r,
        Err(e) => {
            tracing::error!("failed to list repos: {}", e);
            return;
        }
    };

    // WatchedSubsetOfLive: abort and evict watcher handles for repos that are no
    // longer registered. Without this, an unregistered repo's watcher keeps
    // running and tries to write into a dropped chunks table.
    let live_ids: std::collections::HashSet<Uuid> = repos.iter().map(|r| r.id).collect();
    watched.retain(|id, (handle, _)| {
        if live_ids.contains(id) {
            true
        } else {
            handle.abort();
            tracing::info!("evicted watcher for unregistered repo {}", id);
            false
        }
    });

    for repo in repos {
        // Paused repos are skipped entirely — no reindex, no watcher — without
        // dropping data. If a watcher is running for a now-paused repo, evict it.
        // Spec: Muninn.Index.daemonDecision (paused → Skip).
        if repo.paused {
            if let Some((handle, _)) = watched.remove(&repo.id) {
                handle.abort();
                tracing::info!("paused {} — stopped its watcher", repo.path);
            }
            continue;
        }

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
                repo.path,
                repo.embedding_dim,
                repo_dim
            );
            continue;
        }

        if repo.indexed_at.is_none() {
            if !repo.ever_indexed {
                // Freshly registered, never indexed. Daemon never first-indexes;
                // the user must run `muninn add` (foreground). Spec:
                // Muninn.IndexFsm.DaemonNeverFirstIndexes.
                continue;
            }

            // A foreground job is waiting for this repo. Do not start a background
            // reindex we'd only have to yield — the foreground job will index it.
            // Spec: Muninn.IndexFsm foreground priority.
            if repo.preempt_requested {
                tracing::debug!(
                    "repo {} has a foreground waiter — leaving it for the CLI",
                    repo.path
                );
                continue;
            }

            // Was indexed before; `muninn reindex --background` reset indexed_at.
            // Skip if a reindex is already in flight for this process.
            if reindexing.lock().await.contains(&repo.id) {
                continue;
            }

            // Abort the watcher if one is running, to prevent it from racing
            // with index_repo (both would delete-and-reinsert chunks).
            if let Some((handle, _)) = watched.remove(&repo.id) {
                handle.abort();
                tracing::info!("paused watcher for {} to run full reindex", repo.path);
            }

            // IndexingPre: acquire the repo's advisory lock as the background
            // holder. If someone else holds it, skip — they will NOTIFY when done.
            let lock_conn = match store::try_lock(&cfg.database, repo.id).await {
                Ok(Some(conn)) => conn,
                Ok(None) => {
                    tracing::debug!(
                        "repo {} lock held by another process — skipping reindex this cycle",
                        repo.path
                    );
                    continue;
                }
                Err(e) => {
                    tracing::error!("try_lock for {}: {}", repo.path, e);
                    continue;
                }
            };

            // Spawn background full reindex. After success, notify the daemon so
            // it re-scans and re-attaches the watcher.
            reindexing.lock().await.insert(repo.id);
            let embedder: Arc<dyn muninn_core::embeddings::EmbeddingBackend> =
                Arc::from(make_backend(&eff.embeddings));
            let batch_size = eff.embeddings.batch_size;
            let exclude = eff.exclude.clone();
            let repo_id = repo.id;
            let repo_path_owned = repo_path.to_path_buf();
            let repo_path_str = repo.path.clone();
            let reindexing2 = Arc::clone(reindexing);
            let db_cfg = cfg.database.clone();
            tokio::spawn(async move {
                // Open a dedicated client for this background reindex task.
                let index_client =
                    match db::connect_with_app_name(&db_cfg, "muninn-index-reindex").await {
                        Ok(c) => c,
                        Err(e) => {
                            tracing::error!(
                                "failed to open reindex client for {}: {}",
                                repo_path_str,
                                e
                            );
                            reindexing2.lock().await.remove(&repo_id);
                            return;
                        }
                    };

                // Run the index while polling the preempt flag every 10 s. If a
                // foreground job requests the lock, abort (drop the index future)
                // and yield by releasing the advisory lock — the foreground job's
                // blocking acquire then wakes. Spec: Muninn.AdvisoryLock.
                let index_fut = index_repo(
                    &index_client,
                    repo_id,
                    &repo_path_owned,
                    embedder,
                    batch_size,
                    repo_dim,
                    &exclude,
                    |_, _, _| {},
                );
                tokio::pin!(index_fut);
                let mut ticker = tokio::time::interval(std::time::Duration::from_secs(10));
                ticker.tick().await; // consume the immediate first tick

                let finished = loop {
                    tokio::select! {
                        r = &mut index_fut => break Some(r),
                        _ = ticker.tick() => {
                            match store::is_preempt_requested(&index_client, repo_id).await {
                                Ok(true) => break None,
                                Ok(false) => {}
                                Err(e) => tracing::warn!(
                                    "preempt check failed for {}: {}",
                                    repo_id,
                                    e
                                ),
                            }
                        }
                    }
                };

                match finished {
                    Some(result) => {
                        if let Err(e) = store::unlock(&lock_conn, repo_id).await {
                            tracing::warn!("unlock for {} failed: {}", repo_path_str, e);
                        }
                        match result {
                            Ok((outcome, skips)) => {
                                if outcome == BatchOutcome::SomeSucceeded {
                                    tracing::warn!(
                                        "reindex of {} completed with {} files skipped",
                                        repo_path_str,
                                        skips.len()
                                    );
                                } else {
                                    tracing::info!("reindex of {} complete", repo_path_str);
                                }
                                // mark_indexed was called inside index_repo; now notify
                                // so the daemon re-scans and re-attaches the watcher.
                                if let Err(e) =
                                    store::notify_repos_changed(&index_client).await
                                {
                                    tracing::warn!(
                                        "reindex of {} complete but notify failed: {}",
                                        repo_path_str,
                                        e
                                    );
                                }
                            }
                            Err(e) => tracing::error!(
                                "reindex of {} failed: {}",
                                repo_path_str,
                                e
                            ),
                        }
                    }
                    None => {
                        // Preempted by a foreground job. The index future is dropped
                        // at scope end (cancelled). Release the advisory lock so the
                        // waiting foreground job acquires it; leave preempt_requested
                        // set so the daemon's scan guard does not re-grab before the
                        // foreground job clears it on acquire.
                        if let Err(e) = store::unlock(&lock_conn, repo_id).await {
                            tracing::warn!(
                                "unlock (yield) for {} failed: {}",
                                repo_path_str,
                                e
                            );
                        }
                        tracing::info!(
                            "yielded {} to a waiting foreground job",
                            repo_path_str
                        );
                    }
                }
                reindexing2.lock().await.remove(&repo_id);
            });
            continue;
        }

        // indexed_at IS NOT NULL — start watcher if not already watching, or
        // restart it if the exclude config has changed.
        if let Some((handle, running_exclude)) = watched.get(&repo.id) {
            if *running_exclude == eff.exclude {
                continue; // watcher is running with the correct exclude config
            }
            handle.abort();
            watched.remove(&repo.id);
            tracing::info!(
                "restarting watcher for {} (exclude config changed)",
                repo.path
            );
        }

        // DaemonMayWatch: a foreground/CLI reindex sets indexed_at = NULL for its
        // whole duration, so reaching here (indexed_at set) means no index holds
        // the lock; it is safe to attach a watcher.
        tracing::info!("starting watcher for {}", repo.path);

        let embedder: Arc<dyn muninn_core::embeddings::EmbeddingBackend> =
            Arc::from(make_backend(&eff.embeddings));
        let debounce = eff.watcher.debounce_ms;
        let batch_size = eff.embeddings.batch_size;
        let exclude = eff.exclude.clone();
        let id = repo.id;
        let repo_path_owned = repo_path.to_path_buf();
        let initial_state = Arc::new(Mutex::new(IndexState::Watching));
        let db_cfg = cfg.database.clone();

        let handle = tokio::spawn(async move {
            // Open a dedicated client for this watcher task.
            let watcher_client =
                match db::connect_with_app_name(&db_cfg, "muninn-index-watcher").await {
                    Ok(c) => c,
                    Err(e) => {
                        tracing::error!("failed to open watcher client: {}", e);
                        return;
                    }
                };
            if let Err(e) = watcher::watch_repo(
                Arc::new(watcher_client),
                id,
                repo_path_owned,
                embedder,
                debounce,
                initial_state,
                batch_size,
                repo_dim,
                exclude,
            )
            .await
            {
                tracing::error!("watcher error: {}", e);
            }
        });

        watched.insert(repo.id, (handle, eff.exclude.clone()));
    }
}
