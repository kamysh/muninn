use crate::types::{Chunk, Repo};
use anyhow::Result;
use chrono::{DateTime, Utc};
use sqlx::{PgPool, Row};
use uuid::Uuid;

/// Derive the per-repo chunks table name from the repo UUID.
/// Uses the simple (no-hyphen) UUID hex so the name is a valid SQL identifier.
pub fn chunks_table(repo_id: Uuid) -> String {
    format!("chunks_{}", repo_id.as_simple())
}

/// Derive the per-repo AGE graph name from the repo UUID.
pub fn graph_name(repo_id: Uuid) -> String {
    format!("code_graph_{}", repo_id.as_simple())
}

pub async fn register_repo(
    pool: &PgPool,
    path: &str,
    name: &str,
    embedding_dim: usize,
) -> Result<Repo> {
    let row = sqlx::query(
        r#"
        INSERT INTO repos (id, path, name, indexed_at, embedding_dim)
        VALUES ($1, $2, $3, NULL, $4)
        ON CONFLICT (path) DO UPDATE SET name = EXCLUDED.name
        RETURNING id, path, name, indexed_at, embedding_dim
        "#,
    )
    .bind(Uuid::new_v4())
    .bind(path)
    .bind(name)
    .bind(embedding_dim as i32)
    .fetch_one(pool)
    .await?;

    let repo = row_to_repo(row)?;

    // Create per-repo chunks table (idempotent)
    let table = chunks_table(repo.id);
    sqlx::query(&format!(
        r#"
        CREATE TABLE IF NOT EXISTS "{table}" (
            id          UUID PRIMARY KEY,
            repo_id     UUID NOT NULL,
            file_path   TEXT NOT NULL,
            start_line  INT NOT NULL,
            end_line    INT NOT NULL CHECK (end_line >= start_line),
            content     TEXT NOT NULL CHECK (content <> ''),
            ts_vector   TSVECTOR GENERATED ALWAYS AS (to_tsvector('english', content)) STORED,
            embedding   VECTOR({embedding_dim})
        )
        "#
    ))
    .execute(pool)
    .await?;

    sqlx::query(&format!(
        r#"CREATE INDEX IF NOT EXISTS "{table}_ts_idx" ON "{table}" USING GIN (ts_vector)"#
    ))
    .execute(pool)
    .await?;

    sqlx::query(&format!(
        r#"CREATE INDEX IF NOT EXISTS "{table}_emb_idx" ON "{table}" USING hnsw (embedding vector_cosine_ops)"#
    ))
    .execute(pool)
    .await?;

    sqlx::query(&format!(
        r#"CREATE INDEX IF NOT EXISTS "{table}_file_idx" ON "{table}" (file_path)"#
    ))
    .execute(pool)
    .await?;

    // Create per-repo AGE graph (idempotent: check before create)
    let gname = graph_name(repo.id);
    let graph_exists: bool = sqlx::query(
        "SELECT EXISTS(SELECT 1 FROM ag_catalog.ag_graph WHERE name = $1)",
    )
    .bind(&gname)
    .fetch_one(pool)
    .await?
    .try_get(0)?;

    if !graph_exists {
        sqlx::query(&format!(
            "SELECT * FROM ag_catalog.create_graph('{gname}')"
        ))
        .execute(pool)
        .await?;
    }

    Ok(repo)
}

pub async fn delete_repo(pool: &PgPool, repo_id: Uuid) -> Result<()> {
    // Drop per-repo chunks table
    let table = chunks_table(repo_id);
    sqlx::query(&format!(r#"DROP TABLE IF EXISTS "{table}""#))
        .execute(pool)
        .await?;

    // Drop per-repo AGE graph (cascade = true drops all vertices and edges)
    let gname = graph_name(repo_id);
    let graph_exists: bool = sqlx::query(
        "SELECT EXISTS(SELECT 1 FROM ag_catalog.ag_graph WHERE name = $1)",
    )
    .bind(&gname)
    .fetch_one(pool)
    .await?
    .try_get(0)?;

    if graph_exists {
        sqlx::query(&format!(
            "SELECT * FROM ag_catalog.drop_graph('{gname}', true)"
        ))
        .execute(pool)
        .await?;
    }

    sqlx::query(r#"DELETE FROM repos WHERE id = $1"#)
        .bind(repo_id)
        .execute(pool)
        .await?;
    Ok(())
}

pub async fn get_repo_by_path(pool: &PgPool, path: &str) -> Result<Option<Repo>> {
    let row = sqlx::query(
        r#"SELECT id, path, name, indexed_at, embedding_dim FROM repos WHERE path = $1"#,
    )
    .bind(path)
    .fetch_optional(pool)
    .await?;

    row.map(row_to_repo).transpose()
}

pub async fn list_repos(pool: &PgPool) -> Result<Vec<Repo>> {
    let rows =
        sqlx::query(r#"SELECT id, path, name, indexed_at, embedding_dim FROM repos ORDER BY name"#)
            .fetch_all(pool)
            .await?;

    rows.into_iter().map(row_to_repo).collect()
}

pub async fn mark_indexed(pool: &PgPool, repo_id: Uuid) -> Result<()> {
    sqlx::query(r#"UPDATE repos SET indexed_at = NOW() WHERE id = $1"#)
        .bind(repo_id)
        .execute(pool)
        .await?;
    Ok(())
}

pub async fn upsert_chunk(pool: &PgPool, chunk: &Chunk) -> Result<Uuid> {
    anyhow::ensure!(
        chunk.range.is_valid(),
        "invalid LineRange: start {} > end {}",
        chunk.range.start,
        chunk.range.end
    );
    anyhow::ensure!(
        !chunk.content.is_empty(),
        "chunk content must not be empty (ValidChunk invariant)"
    );

    let table = chunks_table(chunk.repo_id);

    let embedding_literal = chunk.embedding.as_ref().map(|emb| {
        format!(
            "[{}]",
            emb.iter().map(|f| f.to_string()).collect::<Vec<_>>().join(",")
        )
    });

    let emb_placeholder = if embedding_literal.is_some() {
        "$7::vector"
    } else {
        "NULL"
    };

    let sql = format!(
        r#"
        INSERT INTO "{table}" (id, repo_id, file_path, start_line, end_line, content, embedding)
        VALUES ($1, $2, $3, $4, $5, $6, {emb_placeholder})
        ON CONFLICT (id) DO UPDATE
            SET file_path  = EXCLUDED.file_path,
                start_line = EXCLUDED.start_line,
                end_line   = EXCLUDED.end_line,
                content    = EXCLUDED.content,
                embedding  = EXCLUDED.embedding
        RETURNING id
        "#
    );

    let row = if let Some(emb) = embedding_literal {
        sqlx::query(&sql)
            .bind(chunk.id)
            .bind(chunk.repo_id)
            .bind(&chunk.file_path)
            .bind(chunk.range.start as i32)
            .bind(chunk.range.end as i32)
            .bind(&chunk.content)
            .bind(emb)
            .fetch_one(pool)
            .await?
    } else {
        sqlx::query(&sql)
            .bind(chunk.id)
            .bind(chunk.repo_id)
            .bind(&chunk.file_path)
            .bind(chunk.range.start as i32)
            .bind(chunk.range.end as i32)
            .bind(&chunk.content)
            .fetch_one(pool)
            .await?
    };

    let id: Uuid = row.try_get::<Uuid, _>("id")?;
    Ok(id)
}

pub async fn delete_file_chunks(pool: &PgPool, repo_id: Uuid, file_path: &str) -> Result<()> {
    let table = chunks_table(repo_id);
    sqlx::query(&format!(
        r#"DELETE FROM "{table}" WHERE file_path = $1"#
    ))
    .bind(file_path)
    .execute(pool)
    .await?;
    Ok(())
}

/// Check whether a chunk with the given id exists in the repo's store.
/// Used to enforce the IsolatedGraph invariant before inserting symbol nodes.
pub async fn chunk_exists(pool: &PgPool, repo_id: Uuid, chunk_id: Uuid) -> Result<bool> {
    let table = chunks_table(repo_id);
    let exists: bool = sqlx::query(&format!(
        r#"SELECT EXISTS(SELECT 1 FROM "{table}" WHERE id = $1)"#
    ))
    .bind(chunk_id)
    .fetch_one(pool)
    .await?
    .try_get(0)?;
    Ok(exists)
}

// ---- helpers ----------------------------------------------------------------

fn row_to_repo(row: sqlx::postgres::PgRow) -> Result<Repo> {
    Ok(Repo {
        id: row.try_get::<Uuid, _>("id")?,
        path: row.try_get::<String, _>("path")?,
        name: row.try_get::<String, _>("name")?,
        indexed_at: row.try_get::<Option<DateTime<Utc>>, _>("indexed_at")?,
        embedding_dim: row.try_get::<i32, _>("embedding_dim")? as u32,
    })
}