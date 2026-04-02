mod discovery;
mod watcher;

use muninn_core::{
    config::{GlobalConfig, RepoConfig, EffectiveConfig},
    db,
    embeddings::{make_backend, expected_dimension},
    pipeline::index_repo,
    types::{BatchOutcome, IndexState},
};
use std::sync::Arc;
use tokio::sync::Mutex;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    tracing_subscriber::fmt::init();

    let cfg = GlobalConfig::load()?;
    let pool = db::connect(&cfg.database).await?;

    // Discover all repos under configured scan roots
    let mut repo_roots: Vec<std::path::PathBuf> = vec![];
    for root in &cfg.indexer.scan_roots {
        let root_path = match muninn_core::repo_resolver::resolve_path(root) {
            Ok(p) => p,
            Err(e) => {
                tracing::warn!("skipping scan root '{}': {}", root, e);
                continue;
            }
        };
        if !root_path.is_dir() {
            tracing::warn!("skipping scan root '{}': not a directory", root_path.display());
            continue;
        }
        let found = discovery::discover_repos(
            &root_path,
            cfg.indexer.scan_depth,
            cfg.indexer.include_hidden,
        );
        repo_roots.extend(found);
    }

    if repo_roots.is_empty() {
        tracing::warn!("no repos found — check indexer.scan_roots in config");
    }

    let mut handles = vec![];

    for repo_path in repo_roots {
        let dir_name = repo_path
            .file_name()
            .unwrap_or_default()
            .to_string_lossy()
            .to_string();

        let repo_cfg = RepoConfig::load(&repo_path)?;
        let eff = EffectiveConfig::merge(&cfg, &repo_cfg, &dir_name);
        let embedder: Arc<dyn muninn_core::embeddings::EmbeddingBackend> =
            Arc::from(make_backend(&eff.embeddings));
        let repo_dim = expected_dimension(&eff.embeddings);

        let (repo, is_new) = match muninn_core::store::get_repo_by_path(
            &pool,
            &repo_path.to_string_lossy(),
        )
        .await?
        {
            Some(r) => (r, false),
            None => (
                muninn_core::store::register_repo(
                    &pool,
                    &repo_path.to_string_lossy(),
                    &eff.repo_name,
                    repo_dim,
                )
                .await?,
                true,
            ),
        };
        if !is_new && repo.embedding_dim as usize != repo_dim {
            tracing::error!(
                "repo {} expects embedding_dim {} but config backend yields {}; \
                 unregister + re-index to switch backends",
                repo_path.display(),
                repo.embedding_dim,
                repo_dim
            );
            continue;
        }

        if repo.indexed_at.is_none() {
            if is_new {
                // Never indexed — skip. User must run `muninn index <path>` explicitly.
                tracing::info!(
                    "skipping {} — not yet indexed, run: muninn index {}",
                    repo_path.display(), repo_path.display()
                );
                continue;
            }
            // indexed_at was reset via `muninn reindex` — re-index in background.
            tracing::info!("reindexing: {}", repo_path.display());
            let state = Arc::new(Mutex::new(IndexState::Indexing));
            let outcome = index_repo(
                &pool,
                repo.id,
                &repo_path,
                embedder.clone(),
                eff.embeddings.batch_size,
                repo_dim,
                |_, _, _| {},
            )
            .await?;
            {
                let mut s = state.lock().await;
                debug_assert!(
                    *s == IndexState::Indexing,
                    "finishIndex: expected Indexing, got {:?}", *s
                );
                *s = IndexState::Indexed;
            }
            if outcome == BatchOutcome::SomeSucceeded {
                tracing::warn!("reindex of {} completed with some files skipped", repo_path.display());
            }
        }

        let initial_state = Arc::new(Mutex::new(IndexState::Watching));

        let pool2 = pool.clone();
        let embedder2 = embedder.clone();
        let debounce = eff.watcher.debounce_ms;
        let id = repo.id;

        handles.push(tokio::spawn(async move {
            if let Err(e) = watcher::watch_repo(
                pool2,
                id,
                repo_path,
                embedder2,
                debounce,
                initial_state,
                eff.embeddings.batch_size,
                repo_dim,
            )
            .await
            {
                tracing::error!("watcher error: {}", e);
            }
        }));
    }

    futures::future::join_all(handles).await;
    Ok(())
}
