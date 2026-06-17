use anyhow::Result;
use chrono::{DateTime, Utc};
use pgvector::Vector;
use tokio_postgres::{Client, Row};
use uuid::Uuid;

use crate::search::rrf_merge;
use crate::types::{Chunk, LineRange, SearchResult};

// ─── Domain type ─────────────────────────────────────────────────────────────

#[derive(Debug, Clone)]
pub struct KnowledgeItem {
    pub id: Uuid,
    pub repo_path: String,
    pub title: String,
    pub body: String,
    pub tags: Vec<String>,
    pub related_files: Vec<String>,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

#[derive(Debug, Clone)]
pub struct KnowledgeResult {
    pub item: KnowledgeItem,
    pub score: f32,
}

// ─── Write ────────────────────────────────────────────────────────────────────

/// Insert or update a knowledge item for the given repo.
/// If `id` is Some, tries to update that record; if not found, inserts with a new id.
/// If `id` is None, always inserts.
/// `expected_dim` is the dimension of the active embedding backend; if `embedding` is
/// present its length must match to prevent dimension-mismatch errors at query time.
/// Returns the persisted item (with embedding cleared — caller must re-embed if needed).
// Cohesive set of knowledge-item fields; bundling them into a struct would just
// move the argument list elsewhere without improving clarity.
#[allow(clippy::too_many_arguments)]
pub async fn upsert(
    client: &Client,
    id: Option<Uuid>,
    repo_path: &str,
    title: &str,
    body: &str,
    tags: &[String],
    related_files: &[String],
    embedding: Option<&[f32]>,
    expected_dim: usize,
) -> Result<KnowledgeItem> {
    anyhow::ensure!(!title.is_empty(), "knowledge title must not be empty");
    anyhow::ensure!(!body.is_empty(), "knowledge body must not be empty");
    if let Some(emb) = embedding {
        anyhow::ensure!(
            emb.len() == expected_dim,
            "knowledge embedding dimension {} does not match configured backend dimension {}; \
             switching backends requires re-embedding all existing knowledge items",
            emb.len(),
            expected_dim
        );
    }

    let record_id = id.unwrap_or_else(Uuid::new_v4);
    let emb: Option<Vector> = embedding.map(|v| Vector::from(v.to_vec()));

    let row = client
        .query_one(
            r#"
        INSERT INTO knowledge (id, repo_path, title, body, tags, related_files, embedding)
        VALUES ($1, $2, $3, $4, $5, $6, $7)
        ON CONFLICT (id) DO UPDATE
            SET repo_path     = EXCLUDED.repo_path,
                title         = EXCLUDED.title,
                body          = EXCLUDED.body,
                tags          = EXCLUDED.tags,
                related_files = EXCLUDED.related_files,
                embedding     = EXCLUDED.embedding,
                updated_at    = now()
        RETURNING id, repo_path, title, body, tags, related_files, created_at, updated_at
        "#,
            &[
                &record_id,
                &repo_path,
                &title,
                &body,
                &tags,
                &related_files,
                &emb,
            ],
        )
        .await?;

    row_to_item(row)
}

/// Delete a knowledge item by id. Returns true if found and deleted.
pub async fn delete(client: &Client, id: Uuid) -> Result<bool> {
    let n = client
        .execute("DELETE FROM knowledge WHERE id = $1", &[&id])
        .await?;
    Ok(n > 0)
}

// ─── Read ─────────────────────────────────────────────────────────────────────

/// List all knowledge items for a repo, ordered by updated_at descending.
pub async fn list(client: &Client, repo_path: &str) -> Result<Vec<KnowledgeItem>> {
    let rows = client
        .query(
            r#"
        SELECT id, repo_path, title, body, tags, related_files, created_at, updated_at
        FROM knowledge
        WHERE repo_path = $1
        ORDER BY updated_at DESC
        "#,
            &[&repo_path],
        )
        .await?;

    rows.into_iter().map(row_to_item).collect()
}

// ─── Search ───────────────────────────────────────────────────────────────────

pub async fn search_fulltext(
    client: &Client,
    repo_path: &str,
    query: &str,
    limit: i64,
) -> Result<Vec<KnowledgeResult>> {
    let rows = client
        .query(
            r#"
        SELECT id, repo_path, title, body, tags, related_files, created_at, updated_at,
               ts_rank(ts_vector, plainto_tsquery('english', $2)) AS score
        FROM knowledge
        WHERE repo_path = $1
          AND ts_vector @@ plainto_tsquery('english', $2)
        ORDER BY score DESC
        LIMIT $3
        "#,
            &[&repo_path, &query, &limit],
        )
        .await?;

    rows.into_iter()
        .map(|row| {
            let score: f32 = row.try_get("score")?;
            let item = row_to_item(row)?;
            Ok(KnowledgeResult { score, item })
        })
        .collect()
}

pub async fn search_semantic(
    client: &Client,
    repo_path: &str,
    query_embedding: &[f32],
    limit: i64,
) -> Result<Vec<KnowledgeResult>> {
    let vec = Vector::from(query_embedding.to_vec());

    let rows = client
        .query(
            r#"
        SELECT id, repo_path, title, body, tags, related_files, created_at, updated_at,
               (1 - (embedding <=> $3))::float4 AS score
        FROM knowledge
        WHERE repo_path = $1
          AND embedding IS NOT NULL
        ORDER BY embedding <=> $3
        LIMIT $2
        "#,
            &[&repo_path, &limit, &vec],
        )
        .await?;

    rows.into_iter()
        .map(|row| {
            let score: f32 = row.try_get("score")?;
            let item = row_to_item(row)?;
            Ok(KnowledgeResult { score, item })
        })
        .collect()
}

/// Hybrid search: RRF merge of semantic + fulltext results.
pub async fn search_hybrid(
    client: &Client,
    repo_path: &str,
    query: &str,
    query_embedding: &[f32],
    limit: i64,
) -> Result<Vec<KnowledgeResult>> {
    let sem = search_semantic(client, repo_path, query_embedding, limit * 2).await?;
    let ft = search_fulltext(client, repo_path, query, limit * 2).await?;

    let sem_sr: Vec<SearchResult> = sem.iter().map(knowledge_to_search_result).collect();
    let ft_sr: Vec<SearchResult> = ft.iter().map(knowledge_to_search_result).collect();

    let merged_sr = rrf_merge(sem_sr, ft_sr, limit as usize);

    let all_items: std::collections::HashMap<Uuid, &KnowledgeResult> = sem
        .iter()
        .chain(ft.iter())
        .map(|r| (r.item.id, r))
        .collect();

    Ok(merged_sr
        .into_iter()
        .filter_map(|sr| {
            all_items.get(&sr.chunk.id).map(|r| KnowledgeResult {
                item: r.item.clone(),
                score: sr.score,
            })
        })
        .collect())
}

// ─── Helpers ──────────────────────────────────────────────────────────────────

fn row_to_item(row: Row) -> Result<KnowledgeItem> {
    Ok(KnowledgeItem {
        id: row.try_get("id")?,
        repo_path: row.try_get("repo_path")?,
        title: row.try_get("title")?,
        body: row.try_get("body")?,
        tags: row.try_get("tags")?,
        related_files: row.try_get("related_files")?,
        created_at: row.try_get("created_at")?,
        updated_at: row.try_get("updated_at")?,
    })
}

/// Wrap a KnowledgeResult in a SearchResult so we can reuse rrf_merge.
/// Uses the knowledge item id as the chunk id (unique per item).
fn knowledge_to_search_result(r: &KnowledgeResult) -> SearchResult {
    SearchResult {
        score: r.score,
        chunk: Chunk {
            id: r.item.id,
            repo_id: Uuid::nil(),
            file_path: r.item.title.clone(),
            range: LineRange { start: 0, end: 0 },
            content: r.item.body.clone(),
            embedding: None,
        },
    }
}
