mod pipeline;
mod watcher;

use muninn_core::{config::GlobalConfig, db, embeddings::make_backend};
use std::sync::Arc;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    tracing_subscriber::fmt::init();

    let cfg = GlobalConfig::load()?;
    let _pool = db::connect(&cfg.database.dsn()).await?;
    let _embedder: Arc<dyn muninn_core::embeddings::EmbeddingBackend> =
        Arc::from(make_backend(&cfg.embeddings));

    // TODO Task 3: discover repos via scan_roots and index them
    tracing::info!("muninn-index started (repo discovery not yet implemented)");

    futures::future::pending::<()>().await;
    Ok(())
}
