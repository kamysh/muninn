mod pipeline;

use ai_mem_core::{config::AppConfig, db, embeddings::make_backend};
use std::sync::Arc;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    tracing_subscriber::fmt::init();

    let cfg = AppConfig::load()?;
    let pool = db::connect(&cfg.database.dsn).await?;
    let embedder: Arc<dyn ai_mem_core::embeddings::EmbeddingBackend> =
        Arc::from(make_backend(&cfg.embeddings));

    for repo_entry in &cfg.repos {
        let path = std::path::PathBuf::from(&repo_entry.path);
        let repo = match ai_mem_core::store::get_repo_by_path(&pool, &repo_entry.path).await? {
            Some(r) => r,
            None => ai_mem_core::store::register_repo(&pool, &repo_entry.path, &repo_entry.name).await?,
        };

        if repo.indexed_at.is_none() {
            tracing::info!("full reindex: {}", repo_entry.path);
            pipeline::index_repo(&pool, repo.id, &path, embedder.clone(), cfg.embeddings.batch_size).await?;
        }
    }

    tracing::info!("all repos indexed; starting watchers (next task)");
    Ok(())
}