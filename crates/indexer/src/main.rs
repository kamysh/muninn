mod discovery;
mod pipeline;
mod watcher;

use muninn_core::{
    config::{GlobalConfig, RepoConfig, EffectiveConfig},
    db,
    embeddings::{make_backend, expected_dimension_for},
    types::IndexState,
};
use std::sync::Arc;
use tokio::sync::Mutex;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    tracing_subscriber::fmt::init();

    let cfg = GlobalConfig::load()?;
    let pool = db::connect(&cfg.database.dsn()).await?;
    let embedder: Arc<dyn muninn_core::embeddings::EmbeddingBackend> =
        Arc::from(make_backend(&cfg.embeddings));

    // Discover all repos under configured scan roots
    let mut repo_roots: Vec<std::path::PathBuf> = vec![];
    for root in &cfg.indexer.scan_roots {
        let found = discovery::discover_repos(std::path::Path::new(root), cfg.indexer.scan_depth);
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
        let repo_dim = expected_dimension_for(&eff.embeddings);

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

        let initial_state = match (repo.indexed_at.is_some(), is_new) {
            (true, _) => IndexState::Indexed,
            (false, true) => IndexState::Unindexed,
            (false, false) => IndexState::Indexed,
        };
        let state = Arc::new(Mutex::new(initial_state));

        if repo.indexed_at.is_none() {
            if is_new {
                tracing::info!("first index: {}", repo_path.display());
            } else {
                tracing::info!("reindex requested: {}", repo_path.display());
            }
            *state.lock().await = IndexState::Indexing;
            pipeline::index_repo(
                &pool,
                repo.id,
                &repo_path,
                embedder.clone(),
                cfg.embeddings.batch_size,
                repo_dim,
            )
            .await?;
            *state.lock().await = IndexState::Indexed;
        }

        *state.lock().await = IndexState::Watching;

        let pool2 = pool.clone();
        let embedder2 = embedder.clone();
        let debounce = eff.watcher.debounce_ms;
        let state2 = state.clone();
        let id = repo.id;

        handles.push(tokio::spawn(async move {
            if let Err(e) =
                watcher::watch_repo(pool2, id, repo_path, embedder2, debounce, state2, repo_dim)
                    .await
            {
                tracing::error!("watcher error: {}", e);
            }
        }));
    }

    futures::future::join_all(handles).await;
    Ok(())
}