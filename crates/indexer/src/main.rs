mod pipeline;
mod watcher;

use ai_mem_core::{config::AppConfig, db, embeddings::{make_backend, expected_dimension}};
use ai_mem_core::types::IndexState;
use std::sync::Arc;
use tokio::sync::Mutex;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    tracing_subscriber::fmt::init();

    let cfg = AppConfig::load()?;
    let pool = db::connect(&cfg.database.dsn).await?;
    let embedder: Arc<dyn ai_mem_core::embeddings::EmbeddingBackend> =
        Arc::from(make_backend(&cfg.embeddings));
    // Used only when registering a repo for the first time.
    let config_dim = expected_dimension(&cfg.embeddings);

    let mut handles = vec![];

    for repo_entry in &cfg.repos {
        let path = std::path::PathBuf::from(&repo_entry.path);
        let repo = match ai_mem_core::store::get_repo_by_path(&pool, &repo_entry.path).await? {
            Some(r) => r,
            None => ai_mem_core::store::register_repo(
                &pool, &repo_entry.path, &repo_entry.name, config_dim,
            ).await?,
        };

        // Use the dimension recorded at registration time, not the current config.
        // This is the authoritative value matching the VECTOR(n) column in the chunks table.
        let repo_dim = repo.embedding_dim as usize;

        // Model initial state: Unindexed if never indexed, Indexed otherwise
        let state = Arc::new(Mutex::new(if repo.indexed_at.is_none() {
            IndexState::Unindexed
        } else {
            IndexState::Indexed
        }));

        if repo.indexed_at.is_none() {
            tracing::info!("full reindex: {}", repo_entry.path);
            *state.lock().await = IndexState::Indexing;
            pipeline::index_repo(&pool, repo.id, &path, embedder.clone(), cfg.embeddings.batch_size, repo_dim).await?;
            *state.lock().await = IndexState::Indexed;
        }

        // Transition to Watching before spawning the watcher
        *state.lock().await = IndexState::Watching;

        let pool2 = pool.clone();
        let embedder2 = embedder.clone();
        let path2 = path.clone();
        let id = repo.id;
        let debounce = cfg.watcher.debounce_ms;
        let state2 = state.clone();

        handles.push(tokio::spawn(async move {
            if let Err(e) = watcher::watch_repo(pool2, id, path2, embedder2, debounce, state2, repo_dim).await {
                tracing::error!("watcher error: {}", e);
            }
        }));
    }

    futures::future::join_all(handles).await;
    Ok(())
}