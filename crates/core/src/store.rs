use crate::types::{Chunk, Repo};
use anyhow::Result;
use chrono::{DateTime, Utc};
use sqlx::{PgPool, Row};
use uuid::Uuid;

pub async fn register_repo(pool: &PgPool, path: &str, name: &str) -> Result<Repo> {
    let row = sqlx::query(
        r#"
        INSERT INTO repos (id, path, name, indexed_at, config)
        VALUES ($1, $2, $3, NULL, NULL)
        ON CONFLICT (path) DO UPDATE SET name = EXCLUDED.name
        RETURNING id, path, name, indexed_at, config
        "#,
    )
    .bind(Uuid::new_v4())
    .bind(path)
    .bind(name)
    .fetch_one(pool)
    .await?;

    Ok(row_to_repo(row)?)
}

pub async fn get_repo_by_path(pool: &PgPool, path: &str) -> Result<Option<Repo>> {
    let row = sqlx::query(
        r#"SELECT id, path, name, indexed_at, config FROM repos WHERE path = $1"#,
    )
    .bind(path)
    .fetch_optional(pool)
    .await?;

    row.map(row_to_repo).transpose()
}

pub async fn list_repos(pool: &PgPool) -> Result<Vec<Repo>> {
    let rows =
        sqlx::query(r#"SELECT id, path, name, indexed_at, config FROM repos ORDER BY name"#)
            .fetch_all(pool)
            .await?;

    rows.into_iter().map(row_to_repo).collect()
}

pub async fn delete_repo(pool: &PgPool, repo_id: Uuid) -> Result<()> {
    sqlx::query(r#"DELETE FROM repos WHERE id = $1"#)
        .bind(repo_id)
        .execute(pool)
        .await?;
    Ok(())
}

pub async fn mark_indexed(pool: &PgPool, repo_id: Uuid) -> Result<()> {
    sqlx::query(r#"UPDATE repos SET indexed_at = NOW() WHERE id = $1"#)
        .bind(repo_id)
        .execute(pool)
        .await?;
    Ok(())
}

/// Upsert a chunk by id.
///
/// TODO: embedding (VECTOR(1024)) is not stored here yet — add update_chunk_embedding()
/// when pgvector integration is ready.
pub async fn upsert_chunk(pool: &PgPool, chunk: &Chunk) -> Result<Uuid> {
    anyhow::ensure!(
        chunk.range.is_valid(),
        "invalid LineRange: start {} > end {}",
        chunk.range.start, chunk.range.end
    );
    anyhow::ensure!(
        !chunk.content.is_empty(),
        "chunk content must not be empty (ValidChunk invariant)"
    );
    let row = sqlx::query(
        r#"
        INSERT INTO chunks (id, repo_id, file_path, start_line, end_line, content, embedding)
        VALUES ($1, $2, $3, $4, $5, $6, NULL)
        ON CONFLICT (id) DO UPDATE
            SET repo_id    = EXCLUDED.repo_id,
                file_path  = EXCLUDED.file_path,
                start_line = EXCLUDED.start_line,
                end_line   = EXCLUDED.end_line,
                content    = EXCLUDED.content
        RETURNING id
        "#,
    )
    .bind(chunk.id)
    .bind(chunk.repo_id)
    .bind(&chunk.file_path)
    .bind(chunk.range.start as i32)
    .bind(chunk.range.end as i32)
    .bind(&chunk.content)
    .fetch_one(pool)
    .await?;

    let id: Uuid = row.try_get::<Uuid, _>("id")?;
    Ok(id)
}

pub async fn delete_file_chunks(
    pool: &PgPool,
    repo_id: Uuid,
    file_path: &str,
) -> Result<()> {
    sqlx::query(r#"DELETE FROM chunks WHERE repo_id = $1 AND file_path = $2"#)
        .bind(repo_id)
        .bind(file_path)
        .execute(pool)
        .await?;
    Ok(())
}

// ---- helpers ----------------------------------------------------------------

fn row_to_repo(row: sqlx::postgres::PgRow) -> Result<Repo> {
    Ok(Repo {
        id: row.try_get::<Uuid, _>("id")?,
        path: row.try_get::<String, _>("path")?,
        name: row.try_get::<String, _>("name")?,
        indexed_at: row.try_get::<Option<DateTime<Utc>>, _>("indexed_at")?,
        config: row.try_get::<Option<serde_json::Value>, _>("config")?,
    })
}