use crate::{
    embeddings::EmbeddingBackend,
    graph,
    parser::{detect_language, parse_file, chunk_file},
    store::{upsert_chunk, delete_file_chunks},
    types::{BatchOutcome, SymbolKind},
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
    embed_batch_size: usize,
    expected_dim: usize,
) -> Result<()> {
    let file_path = path.to_string_lossy().to_string();
    let bytes = std::fs::read(path)?;
    // Skip binary files (null byte is a reliable binary indicator)
    if bytes.contains(&0u8) {
        return Ok(());
    }
    let source = match String::from_utf8(bytes) {
        Ok(s) => s,
        Err(_) => return Ok(()), // Non-UTF-8 encoding — skip silently
    };

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

    // ValidChunk invariant: no chunk may have empty content.
    chunks.retain(|c| {
        if c.content.is_empty() {
            tracing::warn!("dropping empty-content chunk in {}", file_path);
            false
        } else {
            true
        }
    });
    if chunks.is_empty() {
        return Ok(());
    }

    // Generate embeddings in batches (batch_size = texts per request)
    let batch_size = if embed_batch_size == 0 {
        chunks.len().max(1)
    } else {
        embed_batch_size
    };
    for chunk_batch in chunks.chunks_mut(batch_size) {
        let texts: Vec<String> = chunk_batch.iter().map(|c| c.content.clone()).collect();
        let embeddings = embedder.embed(&texts).await?;
        for (c, emb) in chunk_batch.iter_mut().zip(embeddings) {
            // ValidStoredEmbedding invariant: length must equal repo's registered
            // dimension. Reject length-0 (empty) and dimension-mismatch embeddings —
            // storing either causes silent vector-distance failures at query time.
            if emb.is_empty() {
                tracing::warn!(
                    "embedder returned empty vector for chunk in {}; storing without embedding",
                    file_path
                );
                // c.embedding stays None
            } else if emb.len() != expected_dim {
                return Err(anyhow::anyhow!(
                    "ValidStoredEmbedding violation: embedding dimension {} != expected {} \
                     for chunk in {}; switching backends requires unregister + re-index",
                    emb.len(), expected_dim, file_path
                ));
            } else {
                c.embedding = Some(emb);
            }
        }
    }

    delete_file_chunks(pool, repo_id, &file_path).await?;
    for chunk in &chunks {
        upsert_chunk(pool, chunk).await?;
    }

    // Persist parsed symbols into the per-repo AGE graph (IsolatedGraph invariant:
    // chunks are persisted above before symbols reference them).
    for chunk in &chunks {
        if let Some(sym) = symbols.iter().find(|s| s.range == chunk.range) {
            let kind_str = match sym.kind {
                SymbolKind::Function => "Function",
                SymbolKind::Class    => "Class",
                SymbolKind::Module   => "Module",
                SymbolKind::Import   => "Import",
            };
            if let Err(e) = graph::upsert_symbol_node(
                pool, repo_id, chunk.id,
                &sym.name, kind_str, &file_path,
                chunk.range.start, chunk.range.end,
            ).await {
                tracing::warn!("failed to store symbol '{}' in graph: {}", sym.name, e);
            }
        }
    }

    Ok(())
}

/// Index all files in a repo.
///
/// Returns `BatchOutcome` indicating whether all or only some files succeeded.
/// `on_progress` is called after each file with `(files_done, total_files, path)`.
/// Pass `|_, _, _| {}` for no-op (daemon background use).
pub async fn index_repo(
    pool: &PgPool,
    repo_id: Uuid,
    repo_path: &Path,
    embedder: Arc<dyn EmbeddingBackend>,
    embed_batch_size: usize,
    expected_dim: usize,
    on_progress: impl Fn(usize, usize, &Path),
) -> Result<BatchOutcome> {
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

    let total = files.len();
    let mut done = 0usize;
    let mut any_succeeded = false;
    let mut any_failed = false;

    for file in &files {
        match index_file(
            pool,
            repo_id,
            file,
            embedder.as_ref(),
            4096,
            embed_batch_size,
            expected_dim,
        )
        .await
        {
            Ok(()) => any_succeeded = true,
            Err(e) => {
                any_failed = true;
                tracing::warn!("skipping {}: {}", file.display(), e);
            }
        }
        done += 1;
        on_progress(done, total, file);
    }

    // finishIndex (Indexing → Indexed) requires BatchOutcome ≠ NoneSucceeded.
    // A totally-failed non-empty batch must NOT mark the repo as indexed.
    if any_succeeded {
        crate::store::mark_indexed(pool, repo_id).await?;
        Ok(if any_failed { BatchOutcome::SomeSucceeded } else { BatchOutcome::AllSucceeded })
    } else if files.is_empty() {
        // Vacuously: no files to index — mark as indexed (AllSucceeded over empty set).
        crate::store::mark_indexed(pool, repo_id).await?;
        Ok(BatchOutcome::AllSucceeded)
    } else {
        tracing::error!(
            "repo {}: all {} files failed to index — not marking as indexed",
            repo_id, files.len()
        );
        Err(anyhow::anyhow!(
            "BatchOutcome: no files were successfully indexed in repo {}",
            repo_id
        ))
    }
}
