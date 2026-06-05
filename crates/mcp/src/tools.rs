use muninn_core::{search, graph, knowledge, store, embeddings::EmbeddingBackend};
use muninn_core::types::Repo;
use sqlx::PgPool;
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use anyhow::Result;
use uuid::Uuid;

pub struct SearchContext {
    pub pool: PgPool,
    pub embedder: Arc<dyn EmbeddingBackend>,
    pub embedding_dim: usize,
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
    let repo = resolve_repo(&ctx.pool, &params).await?;

    let embedding = ctx.embedder.embed(std::slice::from_ref(&params.query)).await?;
    let query_vec = embedding.into_iter().next().unwrap_or_default();
    validate_query_dim(&query_vec, &repo)?;

    // Fetch many more candidates than the final limit. RRF needs broad recall
    // from each leg so that cross-list boosts can surface the best matches.
    // With limit*2=20 candidates, a relevant file at semantic rank 21 (pushed
    // down by a large node_modules corpus) never participates in the merge and
    // gets no boost from its fulltext rank. 10× gives 100 candidates for the
    // typical limit=10 request, which is the standard RRF operating range.
    let candidate = (limit * 10).min(search::MAX_LIMIT);
    let semantic = search::semantic_search(&ctx.pool, &query_vec, repo.id, candidate).await?;
    let fulltext = search::fulltext_search(&ctx.pool, &params.query, repo.id, candidate).await?;
    let merged = search::rrf_merge(semantic, fulltext, limit as usize);

    Ok(SearchResponse {
        results: merged.into_iter().map(Into::into).collect(),
    })
}

pub async fn search_fulltext(ctx: &SearchContext, params: SearchParams) -> Result<SearchResponse> {
    let limit = normalize_limit(params.limit)?;
    let repo = resolve_repo(&ctx.pool, &params).await?;
    let results = search::fulltext_search(&ctx.pool, &params.query, repo.id, limit).await?;
    Ok(SearchResponse {
        results: results.into_iter().map(Into::into).collect(),
    })
}

pub async fn search_semantic(ctx: &SearchContext, params: SearchParams) -> Result<SearchResponse> {
    let limit = normalize_limit(params.limit)?;
    let repo = resolve_repo(&ctx.pool, &params).await?;

    let embedding = ctx.embedder.embed(std::slice::from_ref(&params.query)).await?;
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
    let repo = resolve_repo(&ctx.pool, &search_params).await?;
    let symbols =
        graph::query_related(&ctx.pool, repo.id, &params.symbol, relation, incoming).await?;
    Ok(serde_json::json!({ "symbols": symbols }))
}

async fn resolve_repo(pool: &PgPool, params: &SearchParams) -> Result<Repo> {
    let path = if let Some(ref explicit) = params.repo {
        explicit.clone()
    } else if let Some(ref cwd) = params.cwd {
        let cwd_path = std::path::Path::new(cwd);
        let root = muninn_core::repo_resolver::find_repo_root(cwd_path)
            .ok_or_else(|| anyhow::anyhow!("no {} found above '{}'", muninn_core::config::RepoConfig::FILE_NAME, cwd))?;
        root.to_string_lossy().to_string()
    } else {
        anyhow::bail!("provide either 'repo' path or 'cwd' to resolve the repository");
    };

    store::get_repo_by_path(pool, &path)
        .await?
        .ok_or_else(|| anyhow::anyhow!("repo not found or not indexed: '{}'", path))
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
    pub repo:          String,
    pub title:         String,
    pub body:          String,
    #[serde(default)]
    pub tags:          Vec<String>,
    #[serde(default)]
    pub related_files: Vec<String>,
    /// If provided, update the existing item with this id instead of inserting.
    pub id:            Option<String>,
}

#[derive(Serialize)]
pub struct KnowledgeItemResponse {
    pub id:            String,
    pub repo:          String,
    pub title:         String,
    pub body:          String,
    pub tags:          Vec<String>,
    pub related_files: Vec<String>,
    pub created_at:    String,
    pub updated_at:    String,
}

impl From<knowledge::KnowledgeItem> for KnowledgeItemResponse {
    fn from(item: knowledge::KnowledgeItem) -> Self {
        Self {
            id:            item.id.to_string(),
            repo:          item.repo_path,
            title:         item.title,
            body:          item.body,
            tags:          item.tags,
            related_files: item.related_files,
            created_at:    item.created_at.to_rfc3339(),
            updated_at:    item.updated_at.to_rfc3339(),
        }
    }
}

#[derive(Serialize)]
pub struct KnowledgeResultItem {
    pub id:            String,
    pub title:         String,
    pub body:          String,
    pub tags:          Vec<String>,
    pub related_files: Vec<String>,
    pub score:         f32,
}

#[derive(Serialize)]
pub struct KnowledgeSearchResponse {
    pub results: Vec<KnowledgeResultItem>,
}

#[derive(Deserialize)]
pub struct SearchKnowledgeParams {
    pub query: String,
    pub repo:  String,
    pub limit: Option<i64>,
}

#[derive(Deserialize)]
pub struct DeleteKnowledgeParams {
    pub id: String,
}

pub async fn record_knowledge(
    ctx:    &SearchContext,
    params: RecordKnowledgeParams,
) -> Result<KnowledgeItemResponse> {
    let id = params.id.as_deref().map(Uuid::parse_str).transpose()?;

    // Embed the title + body for semantic search.
    let text = format!("{}\n{}", params.title, params.body);
    let embedding = ctx.embedder.embed(&[text]).await?;
    let emb = embedding.into_iter().next().unwrap_or_default();

    let item = knowledge::upsert(
        &ctx.pool,
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
    ctx:    &SearchContext,
    params: SearchKnowledgeParams,
) -> Result<KnowledgeSearchResponse> {
    let limit = normalize_limit(params.limit)?;

    let embedding = ctx.embedder.embed(std::slice::from_ref(&params.query)).await?;
    let emb = embedding.into_iter().next().unwrap_or_default();

    let results = knowledge::search_hybrid(
        &ctx.pool,
        &params.repo,
        &params.query,
        &emb,
        limit,
    )
    .await?;

    Ok(KnowledgeSearchResponse {
        results: results
            .into_iter()
            .map(|r| KnowledgeResultItem {
                id:            r.item.id.to_string(),
                title:         r.item.title,
                body:          r.item.body,
                tags:          r.item.tags,
                related_files: r.item.related_files,
                score:         r.score,
            })
            .collect(),
    })
}

pub async fn delete_knowledge(
    ctx:    &SearchContext,
    params: DeleteKnowledgeParams,
) -> Result<serde_json::Value> {
    let id = Uuid::parse_str(&params.id)?;
    let deleted = knowledge::delete(&ctx.pool, id).await?;
    Ok(serde_json::json!({ "deleted": deleted }))
}

pub async fn list_knowledge(
    ctx:       &SearchContext,
    repo_path: &str,
) -> Result<serde_json::Value> {
    let items = knowledge::list(&ctx.pool, repo_path).await?;
    let response: Vec<KnowledgeItemResponse> = items.into_iter().map(Into::into).collect();
    Ok(serde_json::to_value(response)?)
}

fn normalize_limit(limit: Option<i64>) -> Result<i64> {
    let limit = limit.unwrap_or(10);
    anyhow::ensure!(limit >= 1, "limit must be at least 1");
    anyhow::ensure!(
        limit <= muninn_core::search::MAX_LIMIT,
        "limit must not exceed {}", muninn_core::search::MAX_LIMIT
    );
    Ok(limit)
}
