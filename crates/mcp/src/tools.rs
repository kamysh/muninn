use ai_mem_core::{search, graph, store, embeddings::EmbeddingBackend};
use sqlx::PgPool;
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use uuid::Uuid;
use anyhow::Result;

pub struct SearchContext {
    pub pool: PgPool,
    pub embedder: Arc<dyn EmbeddingBackend>,
}

#[derive(Deserialize)]
pub struct SearchParams {
    pub query: String,
    pub repo: Option<String>,
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
    let repo_id = resolve_repo_id(&ctx.pool, params.repo.as_deref()).await?;

    let embedding = ctx.embedder.embed(&[params.query.clone()]).await?;
    let query_vec = embedding.into_iter().next().unwrap_or_default();

    let semantic = search::semantic_search(&ctx.pool, &query_vec, repo_id, limit * 2).await?;
    let fulltext = search::fulltext_search(&ctx.pool, &params.query, repo_id, limit * 2).await?;
    let merged = search::rrf_merge(semantic, fulltext, limit as usize);

    Ok(SearchResponse { results: merged.into_iter().map(Into::into).collect() })
}

pub async fn search_fulltext(ctx: &SearchContext, params: SearchParams) -> Result<SearchResponse> {
    let limit = params.limit.unwrap_or(10);
    let repo_id = resolve_repo_id(&ctx.pool, params.repo.as_deref()).await?;
    let results = search::fulltext_search(&ctx.pool, &params.query, repo_id, limit).await?;
    Ok(SearchResponse { results: results.into_iter().map(Into::into).collect() })
}

pub async fn search_semantic(ctx: &SearchContext, params: SearchParams) -> Result<SearchResponse> {
    let limit = params.limit.unwrap_or(10);
    let repo_id = resolve_repo_id(&ctx.pool, params.repo.as_deref()).await?;
    let embedding = ctx.embedder.embed(&[params.query.clone()]).await?;
    let query_vec = embedding.into_iter().next().unwrap_or_default();
    let results = search::semantic_search(&ctx.pool, &query_vec, repo_id, limit).await?;
    Ok(SearchResponse { results: results.into_iter().map(Into::into).collect() })
}

#[derive(Deserialize)]
pub struct StructuralParams {
    pub symbol: String,
    pub relation: String,
    pub repo: Option<String>,
}

pub async fn search_structural(ctx: &SearchContext, params: StructuralParams) -> Result<serde_json::Value> {
    let symbols = graph::query_related(&ctx.pool, &params.symbol, &params.relation).await?;
    Ok(serde_json::json!({ "symbols": symbols }))
}

async fn resolve_repo_id(pool: &PgPool, key: Option<&str>) -> Result<Option<Uuid>> {
    let Some(k) = key else { return Ok(None) };
    let repo = store::get_repo_by_path(pool, k).await?;
    Ok(repo.map(|r| r.id))
}