use anyhow::Result;
use muninn_core::types::Repo;
use muninn_core::{db, embeddings::EmbeddingBackend, graph, knowledge, search, store, worktrees};
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
    pub exact: Option<bool>,
}

#[derive(Serialize)]
pub struct SearchResponse {
    pub results: Vec<SearchResultItem>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub coverage: Option<worktrees::SemanticCoverage>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub view: Option<worktrees::CheckoutCoverage>,
}

#[derive(Serialize)]
pub struct SearchResultItem {
    pub file_path: String,
    pub start_line: u32,
    pub end_line: u32,
    pub score: f64,
    pub content: String,
}

impl From<muninn_core::types::SearchResult> for SearchResultItem {
    fn from(r: muninn_core::types::SearchResult) -> Self {
        Self {
            file_path: r.chunk.file_path,
            start_line: r.chunk.range.start,
            end_line: r.chunk.range.end,
            score: f64::from(r.score),
            content: r.chunk.content,
        }
    }
}

pub async fn search_hybrid(ctx: &SearchContext, params: SearchParams) -> Result<SearchResponse> {
    let limit = normalize_limit(params.limit)?;
    let mut search_client =
        db::connect_with_app_name(&ctx.config.database, "muninn-mcp-search").await?;
    if let Some(target) = resolve_worktree(ctx, &params).await? {
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
        let (results, view) = worktrees::hybrid_search_report(
            &mut search_client,
            &target,
            &vector,
            &params.query,
            limit,
        )
        .await?;
        return Ok(SearchResponse {
            results: results.into_iter().map(Into::into).collect(),
            coverage: None,
            view: Some(view),
        });
    }
    let repo = resolve_repo(&ctx.client, &params).await?;

    let embedder = family_embedder(ctx, repo.id).await?;
    let embedding = embedder.embed(std::slice::from_ref(&params.query)).await?;
    let query_vec = embedding.into_iter().next().unwrap_or_default();
    validate_query_dim(&query_vec, &repo)?;

    let merged = search::hybrid_search(
        &mut search_client,
        &query_vec,
        &params.query,
        repo.id,
        limit,
    )
    .await?;

    Ok(SearchResponse {
        results: merged.into_iter().map(Into::into).collect(),
        coverage: None,
        view: None,
    })
}

pub async fn search_fulltext(ctx: &SearchContext, params: SearchParams) -> Result<SearchResponse> {
    let limit = normalize_limit(params.limit)?;
    let mut search_client =
        db::connect_with_app_name(&ctx.config.database, "muninn-mcp-search").await?;
    if let Some(target) = resolve_worktree(ctx, &params).await? {
        let (results, view) =
            worktrees::fulltext_search_report(&mut search_client, &target, &params.query, limit)
                .await?;
        return Ok(SearchResponse {
            results: results.into_iter().map(Into::into).collect(),
            coverage: None,
            view: Some(view),
        });
    }
    let repo = resolve_repo(&ctx.client, &params).await?;
    let results =
        search::fulltext_search(&mut search_client, &params.query, repo.id, limit).await?;
    Ok(SearchResponse {
        results: results.into_iter().map(Into::into).collect(),
        coverage: None,
        view: None,
    })
}

pub async fn search_semantic(ctx: &SearchContext, params: SearchParams) -> Result<SearchResponse> {
    let limit = normalize_limit(params.limit)?;
    let mut search_client =
        db::connect_with_app_name(&ctx.config.database, "muninn-mcp-search").await?;
    if let Some(target) = resolve_worktree(ctx, &params).await? {
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
        let (results, coverage, view) = worktrees::semantic_search_report(
            &mut search_client,
            &target,
            &vector,
            limit,
            params.exact.unwrap_or(false),
        )
        .await?;
        return Ok(SearchResponse {
            results: results
                .into_iter()
                .map(|(result, score)| SearchResultItem {
                    score,
                    ..result.into()
                })
                .collect(),
            coverage: Some(coverage),
            view: Some(view),
        });
    }
    let repo = resolve_repo(&ctx.client, &params).await?;

    let embedder = family_embedder(ctx, repo.id).await?;
    let embedding = embedder.embed(std::slice::from_ref(&params.query)).await?;
    let query_vec = embedding.into_iter().next().unwrap_or_default();
    validate_query_dim(&query_vec, &repo)?;

    let (results, coverage) = worktrees::directory_semantic_search_report(
        &mut search_client,
        repo.id,
        &query_vec,
        limit,
        params.exact.unwrap_or(false),
    )
    .await?;
    Ok(SearchResponse {
        results: results
            .into_iter()
            .map(|(result, score)| SearchResultItem {
                score,
                ..result.into()
            })
            .collect(),
        coverage: Some(coverage),
        view: None,
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
    let mut search_client =
        db::connect_with_app_name(&ctx.config.database, "muninn-mcp-search").await?;
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
        exact: None,
    };
    let (candidates, view) = if let Some(target) = resolve_worktree(ctx, &search_params).await? {
        let (candidates, coverage) = worktrees::query_relationships_report(
            &mut search_client,
            &target,
            &params.symbol,
            relation,
            incoming,
        )
        .await?;
        (candidates, Some(coverage))
    } else {
        let repo = resolve_repo(&ctx.client, &search_params).await?;
        let candidates = graph::query_relationships(
            &mut search_client,
            repo.id,
            &params.symbol,
            relation,
            incoming,
        )
        .await?;
        (candidates, None)
    };
    let symbols: Vec<_> = candidates
        .iter()
        .map(|edge| edge.related(incoming))
        .collect();
    let mut response = serde_json::json!({
        "symbols": symbols,
        "candidates": candidates,
        "guidance": "These are name-based candidates. Use source paths and positions to distinguish matching definitions."
    });
    if let Some(coverage) = view {
        response["view"] = serde_json::to_value(coverage)?;
    }
    Ok(response)
}

async fn resolve_worktree(
    ctx: &SearchContext,
    params: &SearchParams,
) -> Result<Option<worktrees::Target>> {
    let Some(path) = params.repo.as_ref().or(params.cwd.as_ref()) else {
        return Ok(None);
    };
    let path = std::path::Path::new(path);
    let pending = match worktrees::resolve(&ctx.client, path).await {
        Ok(Some(target)) => return Ok(Some(target)),
        Ok(None) => None,
        Err(error) if error.is::<worktrees::PendingIndex>() => Some(error),
        Err(error) => return Err(error),
    };
    let Some(git) = muninn_core::repo_resolver::discover_git_checkout(path).await? else {
        return Ok(None);
    };
    let Some(repo) = worktrees::registered_family(&ctx.client, &git.root).await? else {
        return Ok(None);
    };
    if repo.paused {
        return pending.map_or(Ok(None), Err);
    }
    let (effective, policy) =
        muninn_core::family_policy::runtime::config(&*ctx.client, repo.id, &git.root, &ctx.config)
            .await?;
    let authorized = policy.as_ref().map_or(repo.ever_indexed, |view| {
        view.indexing_enabled && !view.paused
    });
    if !authorized {
        return pending.map_or(Ok(None), Err);
    }
    let root = muninn_core::family_policy::runtime::root(
        &*ctx.client,
        repo.id,
        std::path::Path::new(&repo.path),
    )
    .await?;
    let embedder = family_embedder(ctx, repo.id).await?;
    let mut index_client =
        db::connect_with_app_name(&ctx.config.database, "muninn-mcp-worktree-index").await?;
    worktrees::reconcile_requested_checkout(
        &mut index_client,
        repo.id,
        &root,
        &git.root,
        embedder,
        effective.embeddings.batch_size,
        repo.embedding_dim as usize,
        &effective.exclude,
        &effective.vendor,
    )
    .await?;
    worktrees::resolve(&ctx.client, &git.root).await
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

pub(super) async fn resolve_repo(client: &Client, params: &SearchParams) -> Result<Repo> {
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

#[derive(Deserialize, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum NoteScope {
    Family,
    Checkout,
}

#[derive(Deserialize, Serialize)]
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
    pub scope: Option<NoteScope>,
    pub operation_id: Option<String>,
}

#[derive(Deserialize, Serialize)]
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
    pub semantic_available: bool,
}

#[derive(Deserialize)]
pub struct SearchKnowledgeParams {
    pub query: String,
    pub repo: String,
    pub limit: Option<i64>,
}

#[derive(Deserialize, Serialize)]
pub struct DeleteKnowledgeParams {
    pub id: String,
    pub repo: Option<String>,
    pub operation_id: Option<String>,
}

pub async fn record_knowledge(
    ctx: &SearchContext,
    mut params: RecordKnowledgeParams,
) -> Result<KnowledgeItemResponse> {
    if let Some(id) = params.operation_id.take() {
        let result =
            crate::requests::start(ctx, "record_knowledge", &id, serde_json::to_value(params)?)
                .await?;
        anyhow::ensure!(result["cancelled"] != true, "note request was cancelled");
        return Ok(serde_json::from_value(result)?);
    }
    let prepared = prepare_note(ctx, params).await?;
    write_note(ctx.client.as_ref(), prepared).await
}

pub(super) struct PreparedNote {
    params: RecordKnowledgeParams,
    id: Option<Uuid>,
    pub(super) location: knowledge::NoteLocation,
    embedding: Option<Vec<f32>>,
    expected_dim: usize,
}

pub(super) async fn prepare_note(
    ctx: &SearchContext,
    params: RecordKnowledgeParams,
) -> Result<PreparedNote> {
    let id = params.id.as_deref().map(Uuid::parse_str).transpose()?;
    anyhow::ensure!(
        id.is_none() || params.scope.is_none(),
        "note scope is set at creation"
    );
    let location = if matches!(params.scope, Some(NoteScope::Checkout)) {
        let mut client =
            db::connect_with_app_name(&ctx.config.database, "muninn-mcp-note-checkout").await?;
        knowledge::NoteLocation::resolve_for_checkout_note(&mut client, &params.repo).await?
    } else {
        knowledge::NoteLocation::resolve(&ctx.client, &params.repo).await?
    };
    let embedder = match location.family_id {
        Some(family) => family_embedder(ctx, family).await?,
        None => Arc::clone(&ctx.embedder),
    };

    let expected_dim = location.embedding_dim.unwrap_or(ctx.embedding_dim);
    let text = format!("{}\n{}", params.title, params.body);
    let embedding = match embedder.embed(&[text]).await {
        Ok(embeddings) => embeddings.into_iter().next().filter(|vector| {
            vector.len() == expected_dim && muninn_core::embeddings::usable_vector(vector)
        }),
        Err(error) => {
            tracing::warn!(%error, "saving note text while the vector provider is unavailable");
            None
        }
    };
    Ok(PreparedNote {
        params,
        id,
        location,
        embedding,
        expected_dim,
    })
}

pub(super) async fn write_note(
    client: &impl tokio_postgres::GenericClient,
    note: PreparedNote,
) -> Result<KnowledgeItemResponse> {
    let PreparedNote {
        params,
        id,
        location,
        embedding,
        expected_dim,
    } = note;
    let item = knowledge::upsert_scoped(
        client,
        &location,
        matches!(params.scope, Some(NoteScope::Checkout)),
        id,
        &params.title,
        &params.body,
        &params.tags,
        &params.related_files,
        embedding.as_deref(),
        expected_dim,
    )
    .await?;

    Ok(item.into())
}

pub async fn search_knowledge(
    ctx: &SearchContext,
    params: SearchKnowledgeParams,
) -> Result<KnowledgeSearchResponse> {
    let limit = normalize_limit(params.limit)?;
    let location = knowledge::NoteLocation::resolve(&ctx.client, &params.repo).await?;
    let dimension = location.embedding_dim.unwrap_or(ctx.embedding_dim);
    let vector = if knowledge::has_vectors(&ctx.client, &location, dimension).await? {
        let embedder = match location.family_id {
            Some(family) => family_embedder(ctx, family).await?,
            None => Arc::clone(&ctx.embedder),
        };
        match embedder.embed(std::slice::from_ref(&params.query)).await {
            Ok(embeddings) => embeddings.into_iter().next().filter(|vector| {
                vector.len() == dimension && muninn_core::embeddings::usable_vector(vector)
            }),
            Err(error) => {
                tracing::warn!(%error, "notes remain searchable by text while the vector provider is unavailable");
                None
            }
        }
    } else {
        None
    };

    let mut reader =
        db::connect_with_app_name(&ctx.config.database, "muninn-mcp-note-search").await?;
    let snapshot = reader
        .build_transaction()
        .read_only(true)
        .isolation_level(tokio_postgres::IsolationLevel::RepeatableRead)
        .start()
        .await?;
    let results = if let Some(vector) = &vector {
        knowledge::search_hybrid(snapshot.client(), &location, &params.query, vector, limit).await?
    } else {
        knowledge::search_fulltext(snapshot.client(), &location, &params.query, limit).await?
    };
    snapshot.commit().await?;

    Ok(KnowledgeSearchResponse {
        semantic_available: vector.is_some(),
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
    mut params: DeleteKnowledgeParams,
) -> Result<serde_json::Value> {
    if let Some(id) = params.operation_id.take() {
        return crate::requests::start(ctx, "delete_knowledge", &id, serde_json::to_value(params)?)
            .await;
    }
    let id = Uuid::parse_str(&params.id)?;
    let deleted = if let Some(repo) = params.repo {
        let location = knowledge::NoteLocation::resolve(&ctx.client, &repo).await?;
        knowledge::delete_scoped(ctx.client.as_ref(), &location, id).await?
    } else {
        knowledge::delete(&ctx.client, id).await?
    };
    Ok(serde_json::json!({ "deleted": deleted }))
}

pub async fn list_knowledge(ctx: &SearchContext, repo_path: &str) -> Result<serde_json::Value> {
    let location = knowledge::NoteLocation::resolve(&ctx.client, repo_path).await?;
    let items = knowledge::list_scoped(&ctx.client, &location).await?;
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
