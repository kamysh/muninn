use anyhow::Result;
use muninn_core::types::Repo;
use muninn_core::{embeddings::EmbeddingBackend, graph, knowledge, search, store, worktrees};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use tokio_postgres::Client;
use uuid::Uuid;

pub struct SearchContext {
    pub client: Arc<Client>,
    pub embedder: Arc<dyn EmbeddingBackend>,
    pub embedding_dim: usize,
    pub config: muninn_core::config::GlobalConfig,
    pub family_embedders: Mutex<HashMap<&'static str, Arc<dyn EmbeddingBackend>>>,
    pub record_usage: bool,
}

#[derive(Deserialize)]
pub struct SearchParams {
    pub query: String,
    /// Path of the repo to search. Optional — resolved by walking up from `cwd` when absent.
    pub repo: Option<String>,
    /// Current working directory (supplied by Claude Code). Used to resolve `repo` when absent.
    pub cwd: Option<String>,
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

impl From<muninn_core::types::SearchResult> for SearchResultItem {
    fn from(r: muninn_core::types::SearchResult) -> Self {
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
    let limit = normalize_limit(params.limit)?;
    if let Some(target) = resolve_worktree(&ctx.client, &params).await? {
        let embedder = family_embedder(ctx, target.family).await?;
        let embedding = embedder.embed(std::slice::from_ref(&params.query)).await?;
        let vector = embedding.into_iter().next().unwrap_or_default();
        let family = muninn_core::family_store::get_family(&*ctx.client, target.family)
            .await?
            .ok_or_else(|| anyhow::anyhow!("family removed"))?;
        anyhow::ensure!(
            vector.len() == family.embedding_dim as usize,
            "query embedding dimension mismatch"
        );
        let results =
            worktrees::hybrid_search(&ctx.client, &target, &vector, &params.query, limit).await?;
        return Ok(SearchResponse {
            results: results.into_iter().map(Into::into).collect(),
        });
    }
    let repo = resolve_repo(&ctx.client, &params).await?;

    let embedder = family_embedder(ctx, repo.id).await?;
    let embedding = embedder.embed(std::slice::from_ref(&params.query)).await?;
    let query_vec = embedding.into_iter().next().unwrap_or_default();
    validate_query_dim(&query_vec, &repo)?;

    let candidate = (limit * 10).min(search::MAX_LIMIT);
    let semantic = search::semantic_search(&ctx.client, &query_vec, repo.id, candidate).await?;
    let fulltext = search::fulltext_search(&ctx.client, &params.query, repo.id, candidate).await?;
    let merged = search::rrf_merge(semantic, fulltext, limit as usize);

    Ok(SearchResponse {
        results: merged.into_iter().map(Into::into).collect(),
    })
}

pub async fn search_fulltext(ctx: &SearchContext, params: SearchParams) -> Result<SearchResponse> {
    let limit = normalize_limit(params.limit)?;
    if let Some(target) = resolve_worktree(&ctx.client, &params).await? {
        let results =
            worktrees::fulltext_search(&ctx.client, &target, &params.query, limit).await?;
        return Ok(SearchResponse {
            results: results.into_iter().map(Into::into).collect(),
        });
    }
    let repo = resolve_repo(&ctx.client, &params).await?;
    let results = search::fulltext_search(&ctx.client, &params.query, repo.id, limit).await?;
    Ok(SearchResponse {
        results: results.into_iter().map(Into::into).collect(),
    })
}

pub async fn search_semantic(ctx: &SearchContext, params: SearchParams) -> Result<SearchResponse> {
    let limit = normalize_limit(params.limit)?;
    if let Some(target) = resolve_worktree(&ctx.client, &params).await? {
        let embedder = family_embedder(ctx, target.family).await?;
        let embedding = embedder.embed(std::slice::from_ref(&params.query)).await?;
        let vector = embedding.into_iter().next().unwrap_or_default();
        let family = muninn_core::family_store::get_family(&*ctx.client, target.family)
            .await?
            .ok_or_else(|| anyhow::anyhow!("family removed"))?;
        anyhow::ensure!(
            vector.len() == family.embedding_dim as usize,
            "query embedding dimension mismatch"
        );
        let results = worktrees::semantic_search(&ctx.client, &target, &vector, limit).await?;
        return Ok(SearchResponse {
            results: results.into_iter().map(Into::into).collect(),
        });
    }
    let repo = resolve_repo(&ctx.client, &params).await?;

    let embedder = family_embedder(ctx, repo.id).await?;
    let embedding = embedder.embed(std::slice::from_ref(&params.query)).await?;
    let query_vec = embedding.into_iter().next().unwrap_or_default();
    validate_query_dim(&query_vec, &repo)?;

    let results = search::semantic_search(&ctx.client, &query_vec, repo.id, limit).await?;
    Ok(SearchResponse {
        results: results.into_iter().map(Into::into).collect(),
    })
}

#[derive(Deserialize)]
pub struct StructuralParams {
    pub symbol: String,
    pub relation: String,
    /// Absolute path of the repo. Optional when `cwd` is provided.
    pub repo: Option<String>,
    /// Current working directory. Used to resolve the repo when `repo` is absent.
    pub cwd: Option<String>,
}

pub async fn search_structural(
    ctx: &SearchContext,
    params: StructuralParams,
) -> Result<serde_json::Value> {
    let (relation, incoming) = match params.relation.as_str() {
        "callers" => (muninn_core::types::StructuralRelation::Calls, true),
        "callees" => (muninn_core::types::StructuralRelation::Calls, false),
        "imports" => (muninn_core::types::StructuralRelation::Imports, false),
        "defines" => (muninn_core::types::StructuralRelation::Defines, false),
        "inheritors" => (muninn_core::types::StructuralRelation::InheritsFrom, true),
        "inherits" => (muninn_core::types::StructuralRelation::InheritsFrom, false),
        other => return Err(anyhow::anyhow!("unknown relation: {}", other)),
    };

    let search_params = SearchParams {
        query: String::new(),
        repo: params.repo,
        cwd: params.cwd,
        limit: None,
    };
    if let Some(target) = resolve_worktree(&ctx.client, &search_params).await? {
        let symbols = graph::query_related(
            &ctx.client,
            target.graph,
            &params.symbol,
            relation,
            incoming,
        )
        .await?;
        return Ok(serde_json::json!({"symbols":symbols}));
    }
    let repo = resolve_repo(&ctx.client, &search_params).await?;
    let symbols =
        graph::query_related(&ctx.client, repo.id, &params.symbol, relation, incoming).await?;
    Ok(serde_json::json!({ "symbols": symbols }))
}

async fn resolve_worktree(
    client: &Client,
    params: &SearchParams,
) -> Result<Option<worktrees::Target>> {
    match params.repo.as_ref().or(params.cwd.as_ref()) {
        Some(path) => worktrees::resolve(client, std::path::Path::new(path)).await,
        None => Ok(None),
    }
}

async fn family_embedder(ctx: &SearchContext, id: Uuid) -> Result<Arc<dyn EmbeddingBackend>> {
    match muninn_core::family_policy::runtime::policy(ctx.client.as_ref(), id).await? {
        Some(view) => {
            let config = muninn_core::family_policy::runtime::effective(&ctx.config, &view);
            if config.embeddings.backend == ctx.config.embeddings.backend
                && config.embeddings.model == ctx.config.embeddings.model
            {
                return Ok(Arc::clone(&ctx.embedder));
            }
            let mut cached = ctx
                .family_embedders
                .lock()
                .map_err(|_| anyhow::anyhow!("embedding cache lock failed"))?;
            Ok(Arc::clone(
                cached
                    .entry(view.policy.embeddings.backend.model_identity())
                    .or_insert_with(|| {
                        Arc::from(muninn_core::embeddings::make_backend(&config.embeddings))
                    }),
            ))
        }
        None => Ok(Arc::clone(&ctx.embedder)),
    }
}

async fn resolve_repo(client: &Client, params: &SearchParams) -> Result<Repo> {
    if let Some(path) = params.repo.as_ref().or(params.cwd.as_ref()) {
        let path = std::fs::canonicalize(path)?;
        for root in path.ancestors() {
            if let Some(repo) = store::get_repo_by_path(client, &root.to_string_lossy()).await? {
                return Ok(repo);
            }
        }
    }
    let path = params
        .repo
        .as_ref()
        .or(params.cwd.as_ref())
        .ok_or_else(|| {
            anyhow::anyhow!("provide either 'repo' path or 'cwd' to resolve the repository")
        })?;
    anyhow::bail!("repo not found or not indexed: '{}'", path)
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

// ─── Knowledge tools ─────────────────────────────────────────────────────────

#[derive(Deserialize)]
pub struct RecordKnowledgeParams {
    pub repo: String,
    pub title: String,
    pub body: String,
    #[serde(default)]
    pub tags: Vec<String>,
    #[serde(default)]
    pub related_files: Vec<String>,
    /// If provided, update the existing item with this id instead of inserting.
    pub id: Option<String>,
}

#[derive(Serialize)]
pub struct KnowledgeItemResponse {
    pub id: String,
    pub repo: String,
    pub title: String,
    pub body: String,
    pub tags: Vec<String>,
    pub related_files: Vec<String>,
    pub created_at: String,
    pub updated_at: String,
}

impl From<knowledge::KnowledgeItem> for KnowledgeItemResponse {
    fn from(item: knowledge::KnowledgeItem) -> Self {
        Self {
            id: item.id.to_string(),
            repo: item.repo_path,
            title: item.title,
            body: item.body,
            tags: item.tags,
            related_files: item.related_files,
            created_at: item.created_at.to_rfc3339(),
            updated_at: item.updated_at.to_rfc3339(),
        }
    }
}

#[derive(Serialize)]
pub struct KnowledgeResultItem {
    pub id: String,
    pub title: String,
    pub body: String,
    pub tags: Vec<String>,
    pub related_files: Vec<String>,
    pub score: f32,
}

#[derive(Serialize)]
pub struct KnowledgeSearchResponse {
    pub results: Vec<KnowledgeResultItem>,
}

#[derive(Deserialize)]
pub struct SearchKnowledgeParams {
    pub query: String,
    pub repo: String,
    pub limit: Option<i64>,
}

#[derive(Deserialize)]
pub struct DeleteKnowledgeParams {
    pub id: String,
}

pub async fn record_knowledge(
    ctx: &SearchContext,
    params: RecordKnowledgeParams,
) -> Result<KnowledgeItemResponse> {
    let id = params.id.as_deref().map(Uuid::parse_str).transpose()?;

    let text = format!("{}\n{}", params.title, params.body);
    let embedding = ctx.embedder.embed(&[text]).await?;
    let emb = embedding.into_iter().next().unwrap_or_default();

    let item = knowledge::upsert(
        &ctx.client,
        id,
        &params.repo,
        &params.title,
        &params.body,
        &params.tags,
        &params.related_files,
        Some(&emb),
        ctx.embedding_dim,
    )
    .await?;

    Ok(item.into())
}

pub async fn search_knowledge(
    ctx: &SearchContext,
    params: SearchKnowledgeParams,
) -> Result<KnowledgeSearchResponse> {
    let limit = normalize_limit(params.limit)?;

    let embedding = ctx
        .embedder
        .embed(std::slice::from_ref(&params.query))
        .await?;
    let emb = embedding.into_iter().next().unwrap_or_default();

    let results =
        knowledge::search_hybrid(&ctx.client, &params.repo, &params.query, &emb, limit).await?;

    Ok(KnowledgeSearchResponse {
        results: results
            .into_iter()
            .map(|r| KnowledgeResultItem {
                id: r.item.id.to_string(),
                title: r.item.title,
                body: r.item.body,
                tags: r.item.tags,
                related_files: r.item.related_files,
                score: r.score,
            })
            .collect(),
    })
}

pub async fn delete_knowledge(
    ctx: &SearchContext,
    params: DeleteKnowledgeParams,
) -> Result<serde_json::Value> {
    let id = Uuid::parse_str(&params.id)?;
    let deleted = knowledge::delete(&ctx.client, id).await?;
    Ok(serde_json::json!({ "deleted": deleted }))
}

pub async fn list_knowledge(ctx: &SearchContext, repo_path: &str) -> Result<serde_json::Value> {
    let items = knowledge::list(&ctx.client, repo_path).await?;
    let response: Vec<KnowledgeItemResponse> = items.into_iter().map(Into::into).collect();
    Ok(serde_json::to_value(response)?)
}

fn normalize_limit(limit: Option<i64>) -> Result<i64> {
    let limit = limit.unwrap_or(10);
    anyhow::ensure!(limit >= 1, "limit must be at least 1");
    anyhow::ensure!(
        limit <= muninn_core::search::MAX_LIMIT,
        "limit must not exceed {}",
        muninn_core::search::MAX_LIMIT
    );
    Ok(limit)
}
