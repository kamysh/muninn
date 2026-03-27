use ai_mem_core::{search, graph, store, embeddings::EmbeddingBackend};
use ai_mem_core::types::Repo;
use sqlx::PgPool;
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use anyhow::Result;

pub struct SearchContext {
    pub pool: PgPool,
    pub embedder: Arc<dyn EmbeddingBackend>,
}

#[derive(Deserialize)]
pub struct SearchParams {
    pub query: String,
    /// Path of the repo to search (required — searches are always repo-scoped).
    pub repo: String,
    pub limit: Option<i64>,
}

#[derive(Serialize)]
pub struct SearchResponse {
    pub results: Vec<SearchResultItem>,
}

#[derive(Serialize)]
pub struct SearchResultItem {
    pub file_path: String,
    pub start_line: u32,
    pub end_line: u32,
    pub score: f32,
    pub content: String,
}

impl From<ai_mem_core::types::SearchResult> for SearchResultItem {
    fn from(r: ai_mem_core::types::SearchResult) -> Self {
        Self {
            file_path: r.chunk.file_path,
            start_line: r.chunk.range.start,
            end_line: r.chunk.range.end,
            score: r.score,
            content: r.chunk.content,
        }
    }
}

pub async fn search_hybrid(ctx: &SearchContext, params: SearchParams) -> Result<SearchResponse> {
    let limit = params.limit.unwrap_or(10);
    let repo = resolve_repo(&ctx.pool, &params.repo).await?;

    let embedding = ctx.embedder.embed(&[params.query.clone()]).await?;
    let query_vec = embedding.into_iter().next().unwrap_or_default();
    validate_query_dim(&query_vec, &repo)?;

    let semantic = search::semantic_search(&ctx.pool, &query_vec, repo.id, limit * 2).await?;
    let fulltext = search::fulltext_search(&ctx.pool, &params.query, repo.id, limit * 2).await?;
    let merged = search::rrf_merge(semantic, fulltext, limit as usize);

    Ok(SearchResponse {
        results: merged.into_iter().map(Into::into).collect(),
    })
}

pub async fn search_fulltext(ctx: &SearchContext, params: SearchParams) -> Result<SearchResponse> {
    let limit = params.limit.unwrap_or(10);
    let repo = resolve_repo(&ctx.pool, &params.repo).await?;
    let results = search::fulltext_search(&ctx.pool, &params.query, repo.id, limit).await?;
    Ok(SearchResponse {
        results: results.into_iter().map(Into::into).collect(),
    })
}

pub async fn search_semantic(ctx: &SearchContext, params: SearchParams) -> Result<SearchResponse> {
    let limit = params.limit.unwrap_or(10);
    let repo = resolve_repo(&ctx.pool, &params.repo).await?;

    let embedding = ctx.embedder.embed(&[params.query.clone()]).await?;
    let query_vec = embedding.into_iter().next().unwrap_or_default();
    validate_query_dim(&query_vec, &repo)?;

    let results = search::semantic_search(&ctx.pool, &query_vec, repo.id, limit).await?;
    Ok(SearchResponse {
        results: results.into_iter().map(Into::into).collect(),
    })
}

#[derive(Deserialize)]
pub struct StructuralParams {
    pub symbol: String,
    pub relation: String,
    /// Path of the repo to search (required).
    pub repo: String,
}

pub async fn search_structural(
    ctx: &SearchContext,
    params: StructuralParams,
) -> Result<serde_json::Value> {
    let (relation, incoming) = match params.relation.as_str() {
        "callers" => (ai_mem_core::types::StructuralRelation::Calls, true),
        "callees" => (ai_mem_core::types::StructuralRelation::Calls, false),
        "imports" => (ai_mem_core::types::StructuralRelation::Imports, false),
        "defines" => (ai_mem_core::types::StructuralRelation::Defines, false),
        "inheritors" => (ai_mem_core::types::StructuralRelation::InheritsFrom, true),
        "inherits" => (ai_mem_core::types::StructuralRelation::InheritsFrom, false),
        other => return Err(anyhow::anyhow!("unknown relation: {}", other)),
    };

    let repo = resolve_repo(&ctx.pool, &params.repo).await?;
    let symbols =
        graph::query_related(&ctx.pool, repo.id, &params.symbol, relation, incoming).await?;
    Ok(serde_json::json!({ "symbols": symbols }))
}

async fn resolve_repo(pool: &PgPool, path: &str) -> Result<Repo> {
    store::get_repo_by_path(pool, path)
        .await?
        .ok_or_else(|| anyhow::anyhow!("repo not found: {}", path))
}

/// Enforce RepoDimMatchesBackend: the query embedding must have the same
/// dimension as the VECTOR(n) column in the repo's chunks table.
fn validate_query_dim(query_vec: &[f32], repo: &Repo) -> Result<()> {
    let expected = repo.embedding_dim as usize;
    anyhow::ensure!(
        query_vec.len() == expected,
        "RepoDimMatchesBackend violation: query embedding has {} dimensions but \
         repo '{}' was indexed with {} (re-register the repo to switch backends)",
        query_vec.len(),
        repo.path,
        expected
    );
    Ok(())
}