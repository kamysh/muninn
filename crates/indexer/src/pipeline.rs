use ai_mem_core::{
    embeddings::EmbeddingBackend,
    parser::{detect_language, parse_file, chunk_file},
    store::{upsert_chunk, delete_file_chunks},
};
use sqlx::PgPool;
use uuid::Uuid;
use anyhow::Result;
use std::sync::Arc;
use std::path::Path;

pub async fn index_file(
    pool: &PgPool,
    repo_id: Uuid,
    path: &Path,
    embedder: &dyn EmbeddingBackend,
    max_chars: usize,
) -> Result<()> {
    let file_path = path.to_string_lossy().to_string();
    let source = std::fs::read_to_string(path)?;

    let language = detect_language(&file_path);
    let symbols = match language {
        Some(lang) => parse_file(&source, lang).unwrap_or_default(),
        None => vec![],
    };

    let mut chunks = chunk_file(&source, &symbols, max_chars);
    for c in &mut chunks {
        c.repo_id = repo_id;
        c.file_path = file_path.clone();
    }

    if chunks.is_empty() {
        return Ok(());
    }

    // Generate embeddings in one batch
    let texts: Vec<String> = chunks.iter().map(|c| c.content.clone()).collect();
    let embeddings = embedder.embed(&texts).await?;
    for (c, emb) in chunks.iter_mut().zip(embeddings) {
        c.embedding = Some(emb);
    }

    delete_file_chunks(pool, repo_id, &file_path).await?;
    for chunk in &chunks {
        upsert_chunk(pool, chunk).await?;
    }

    Ok(())
}

pub async fn index_repo(
    pool: &PgPool,
    repo_id: Uuid,
    repo_path: &Path,
    embedder: Arc<dyn EmbeddingBackend>,
    batch_size: usize,
) -> Result<()> {
    use ignore::WalkBuilder;

    let walker = WalkBuilder::new(repo_path)
        .hidden(false)
        .git_ignore(true)
        .build();

    let mut files: Vec<std::path::PathBuf> = vec![];
    for entry in walker.flatten() {
        if entry.file_type().map(|t| t.is_file()).unwrap_or(false) {
            files.push(entry.path().to_owned());
        }
    }

    for batch in files.chunks(batch_size) {
        for file in batch {
            if let Err(e) = index_file(pool, repo_id, file, embedder.as_ref(), 4096).await {
                tracing::warn!("skipping {}: {}", file.display(), e);
            }
        }
    }

    ai_mem_core::store::mark_indexed(pool, repo_id).await?;
    Ok(())
}