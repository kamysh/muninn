use anyhow::Result;
use chrono::{DateTime, Utc};
use sqlx::{PgPool, Row};
use uuid::Uuid;

use crate::search::rrf_merge;
use crate::types::{Chunk, LineRange, SearchResult};

// ─── Domain type ─────────────────────────────────────────────────────────────

#[derive(Debug, Clone)]
pub struct KnowledgeItem {
    pub id:            Uuid,
    pub repo_path:     String,
    pub title:         String,
    pub body:          String,
    pub tags:          Vec<String>,
    pub related_files: Vec<String>,
    pub created_at:    DateTime<Utc>,
    pub updated_at:    DateTime<Utc>,
}

#[derive(Debug, Clone)]
pub struct KnowledgeResult {
    pub item:  KnowledgeItem,
    pub score: f32,
}

// ─── Write ────────────────────────────────────────────────────────────────────

/// Insert or update a knowledge item for the given repo.
/// If `id` is Some, tries to update that record; if not found, inserts with a new id.
/// If `id` is None, always inserts.
/// Returns the persisted item (with embedding cleared — caller must re-embed if needed).
pub async fn upsert(
    pool:          &PgPool,
    id:            Option<Uuid>,
    repo_path:     &str,
    title:         &str,
    body:          &str,
    tags:          &[String],
    related_files: &[String],
    embedding:     Option<&[f32]>,
) -> Result<KnowledgeItem> {
    anyhow::ensure!(!title.is_empty(), "knowledge title must not be empty");
    anyhow::ensure!(!body.is_empty(),  "knowledge body must not be empty");

    let record_id = id.unwrap_or_else(Uuid::new_v4);
    let emb_literal = embedding.map(|v| {
        format!("[{}]", v.iter().map(|f| f.to_string()).collect::<Vec<_>>().join(","))
    });

    let row = sqlx::query(
        r#"
        INSERT INTO knowledge (id, repo_path, title, body, tags, related_files, embedding)
        VALUES ($1, $2, $3, $4, $5, $6, $7::vector)
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
    )
    .bind(record_id)
    .bind(repo_path)
    .bind(title)
    .bind(body)
    .bind(tags)
    .bind(related_files)
    .bind(emb_literal)
    .fetch_one(pool)
    .await?;

    row_to_item(row)
}

/// Delete a knowledge item by id. Returns true if found and deleted.
pub async fn delete(pool: &PgPool, id: Uuid) -> Result<bool> {
    let result = sqlx::query("DELETE FROM knowledge WHERE id = $1")
        .bind(id)
        .execute(pool)
        .await?;
    Ok(result.rows_affected() > 0)
}

// ─── Read ─────────────────────────────────────────────────────────────────────

/// List all knowledge items for a repo, ordered by updated_at descending.
pub async fn list(pool: &PgPool, repo_path: &str) -> Result<Vec<KnowledgeItem>> {
    let rows = sqlx::query(
        r#"
        SELECT id, repo_path, title, body, tags, related_files, created_at, updated_at
        FROM knowledge
        WHERE repo_path = $1
        ORDER BY updated_at DESC
        "#,
    )
    .bind(repo_path)
    .fetch_all(pool)
    .await?;

    rows.into_iter().map(row_to_item).collect()
}

// ─── Search ───────────────────────────────────────────────────────────────────

pub async fn search_fulltext(
    pool:      &PgPool,
    repo_path: &str,
    query:     &str,
    limit:     i64,
) -> Result<Vec<KnowledgeResult>> {
    let rows = sqlx::query(
        r#"
        SELECT id, repo_path, title, body, tags, related_files, created_at, updated_at,
               ts_rank(ts_vector, plainto_tsquery('english', $2)) AS score
        FROM knowledge
        WHERE repo_path = $1
          AND ts_vector @@ plainto_tsquery('english', $2)
        ORDER BY score DESC
        LIMIT $3
        "#,
    )
    .bind(repo_path)
    .bind(query)
    .bind(limit)
    .fetch_all(pool)
    .await?;

    rows.into_iter()
        .map(|row| {
            Ok(KnowledgeResult {
                score: row.try_get::<f32, _>("score")?,
                item:  row_to_item(row)?,
            })
        })
        .collect()
}

pub async fn search_semantic(
    pool:            &PgPool,
    repo_path:       &str,
    query_embedding: &[f32],
    limit:           i64,
) -> Result<Vec<KnowledgeResult>> {
    let vec_literal = format!(
        "[{}]",
        query_embedding.iter().map(|f| f.to_string()).collect::<Vec<_>>().join(",")
    );

    let rows = sqlx::query(
        r#"
        SELECT id, repo_path, title, body, tags, related_files, created_at, updated_at,
               (1 - (embedding <=> $3::vector))::float4 AS score
        FROM knowledge
        WHERE repo_path = $1
          AND embedding IS NOT NULL
        ORDER BY embedding <=> $3::vector
        LIMIT $2
        "#,
    )
    .bind(repo_path)
    .bind(limit)
    .bind(vec_literal)
    .fetch_all(pool)
    .await?;

    rows.into_iter()
        .map(|row| {
            Ok(KnowledgeResult {
                score: row.try_get::<f32, _>("score")?,
                item:  row_to_item(row)?,
            })
        })
        .collect()
}

/// Hybrid search: RRF merge of semantic + fulltext results.
pub async fn search_hybrid(
    pool:            &PgPool,
    repo_path:       &str,
    query:           &str,
    query_embedding: &[f32],
    limit:           i64,
) -> Result<Vec<KnowledgeResult>> {
    let sem = search_semantic(pool, repo_path, query_embedding, limit * 2).await?;
    let ft  = search_fulltext(pool, repo_path, query, limit * 2).await?;

    // Reuse the existing RRF implementation via the SearchResult adaptor.
    let sem_sr: Vec<SearchResult> = sem.iter().map(|r| knowledge_to_search_result(r)).collect();
    let ft_sr:  Vec<SearchResult> = ft.iter().map(|r|  knowledge_to_search_result(r)).collect();

    let merged_sr = rrf_merge(sem_sr, ft_sr, limit as usize);

    // Reconstruct KnowledgeResults in merged order by matching chunk ids back to items.
    let all_items: std::collections::HashMap<Uuid, &KnowledgeResult> = sem
        .iter()
        .chain(ft.iter())
        .map(|r| (r.item.id, r))
        .collect();

    Ok(merged_sr
        .into_iter()
        .filter_map(|sr| {
            all_items.get(&sr.chunk.id).map(|r| KnowledgeResult {
                item:  r.item.clone(),
                score: sr.score,
            })
        })
        .collect())
}

// ─── Helpers ──────────────────────────────────────────────────────────────────

fn row_to_item(row: sqlx::postgres::PgRow) -> Result<KnowledgeItem> {
    Ok(KnowledgeItem {
        id:            row.try_get("id")?,
        repo_path:     row.try_get("repo_path")?,
        title:         row.try_get("title")?,
        body:          row.try_get("body")?,
        tags:          row.try_get("tags")?,
        related_files: row.try_get("related_files")?,
        created_at:    row.try_get("created_at")?,
        updated_at:    row.try_get("updated_at")?,
    })
}

/// Wrap a KnowledgeResult in a SearchResult so we can reuse rrf_merge.
/// Uses the knowledge item id as the chunk id (unique per item).
fn knowledge_to_search_result(r: &KnowledgeResult) -> SearchResult {
    SearchResult {
        score: r.score,
        chunk: Chunk {
            id:        r.item.id,
            repo_id:   Uuid::nil(),
            file_path: r.item.title.clone(),
            range:     LineRange { start: 0, end: 0 },
            content:   r.item.body.clone(),
            embedding: None,
        },
    }
}