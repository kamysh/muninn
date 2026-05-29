use crate::types::{Chunk, Repo};
use anyhow::Result;
use chrono::{DateTime, Utc};
use sqlx::pool::PoolConnection;
use sqlx::{PgPool, Postgres, Row};
use uuid::Uuid;

/// The repo columns selected into a `Repo` by `row_to_repo`. Kept as one
/// constant so every query stays in sync with the struct.
const REPO_COLUMNS: &str = "id, path, name, indexed_at, ever_indexed, \
     embedding_dim, preempt_requested, paused";

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
    let row = sqlx::query(&format!(
        r#"
        INSERT INTO repos (id, path, name, indexed_at, embedding_dim)
        VALUES ($1, $2, $3, NULL, $4)
        ON CONFLICT (path) DO UPDATE SET name = EXCLUDED.name
        RETURNING {REPO_COLUMNS}
        "#
    ))
    .bind(Uuid::new_v4())
    .bind(path)
    .bind(name)
    .bind(embedding_dim as i32)
    .fetch_one(pool)
    .await?;

    let repo = row_to_repo(row)?;
    let stored_dim = repo.embedding_dim as usize;
    anyhow::ensure!(
        stored_dim == embedding_dim,
        "repo {} registered with embedding_dim {} but config expects {}; \
         unregister + re-register to change embedding backends",
        repo.path,
        stored_dim,
        embedding_dim
    );

    // Create per-repo chunks table (idempotent)
    let table = chunks_table(repo.id);
    let embedding_dim = stored_dim;
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
    let row = sqlx::query(&format!(
        r#"SELECT {REPO_COLUMNS} FROM repos WHERE path = $1"#
    ))
    .bind(path)
    .fetch_optional(pool)
    .await?;

    row.map(row_to_repo).transpose()
}

pub async fn list_repos(pool: &PgPool) -> Result<Vec<Repo>> {
    let rows = sqlx::query(&format!(
        r#"SELECT {REPO_COLUMNS} FROM repos ORDER BY name"#
    ))
    .fetch_all(pool)
    .await?;

    rows.into_iter().map(row_to_repo).collect()
}

/// Notify the indexer daemon that the set of registered repos has changed.
/// The daemon listens on the `muninn_repos_changed` channel via PostgreSQL LISTEN/NOTIFY
/// and will re-scan the repos table on receipt.
pub async fn notify_repos_changed(pool: &PgPool) -> Result<()> {
    sqlx::query("SELECT pg_notify('muninn_repos_changed', '')")
        .execute(pool)
        .await?;
    Ok(())
}

pub async fn mark_indexed(pool: &PgPool, repo_id: Uuid) -> Result<()> {
    sqlx::query(r#"UPDATE repos SET indexed_at = NOW(), ever_indexed = TRUE WHERE id = $1"#)
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
        !chunk.file_path.is_empty(),
        "NonEmptyFilePath violation: chunk file_path must not be empty"
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
    // NonEmptyFilePath invariant: an empty path would execute a vacuous delete
    // (matching nothing) or, worse, delete all chunks if the schema changes.
    anyhow::ensure!(
        !file_path.is_empty(),
        "NonEmptyFilePath violation: file_path must not be empty"
    );
    let table = chunks_table(repo_id);
    sqlx::query(&format!(
        r#"DELETE FROM "{table}" WHERE file_path = $1"#
    ))
    .bind(file_path)
    .execute(pool)
    .await?;
    Ok(())
}

/// Delete every chunk for a repo whose `file_path` is not in `keep`.
///
/// A full reindex re-inserts chunks only for files it walks, so files deleted
/// from disk or newly matched by an `[index] exclude` glob would otherwise
/// leave orphaned chunks behind. Calling this with the set of files just
/// indexed makes the reindex authoritative over the current file set. Returns
/// the number of rows deleted. With an empty `keep` set this deletes all chunks
/// (the entire file set is gone or excluded).
pub async fn prune_chunks_not_in(pool: &PgPool, repo_id: Uuid, keep: &[String]) -> Result<u64> {
    let table = chunks_table(repo_id);
    // `<> ALL($1)` is true when file_path equals no kept path; for an empty
    // array it is vacuously true, so every row is removed.
    let res = sqlx::query(&format!(
        r#"DELETE FROM "{table}" WHERE file_path <> ALL($1)"#
    ))
    .bind(keep)
    .execute(pool)
    .await?;
    Ok(res.rows_affected())
}

/// Distinct `file_path`s currently in the repo's chunk store that are NOT in
/// `keep`. These are the files a reindex no longer covers (deleted on disk or
/// newly excluded); the caller prunes their graph nodes before pruning chunks.
pub async fn file_paths_not_in(pool: &PgPool, repo_id: Uuid, keep: &[String]) -> Result<Vec<String>> {
    use sqlx::Row;
    let table = chunks_table(repo_id);
    let rows = sqlx::query(&format!(
        r#"SELECT DISTINCT file_path FROM "{table}" WHERE file_path <> ALL($1)"#
    ))
    .bind(keep)
    .fetch_all(pool)
    .await?;
    Ok(rows.into_iter().filter_map(|r| r.try_get::<String, _>("file_path").ok()).collect())
}

// ---- indexing lock (PostgreSQL session-scoped advisory lock) ----------------
//
// The mutex is `pg_advisory_lock`, held on a dedicated session (connection) for
// the index's duration. Liveness is the session itself: if the holder's process
// dies, PostgreSQL frees the lock automatically — no heartbeat, no staleness
// window. Spec: Muninn.AdvisoryLock.

/// The advisory-lock key for a repo: the first 8 bytes of its UUID as an i64.
/// Advisory locks are per-database, and muninn/mimir use separate databases, so
/// there is no cross-tool collision; within muninn's database a 64-bit key from
/// the UUID is collision-free for any realistic repo count.
fn advisory_key(repo_id: Uuid) -> i64 {
    let b = repo_id.as_bytes();
    i64::from_le_bytes([b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]])
}

/// Try to acquire the repo's advisory lock without blocking. On success returns
/// the connection holding it — the lock lives exactly as long as that connection
/// (release with `unlock`, or implicitly when the process/connection dies). On
/// contention returns `None` (the probe connection is dropped, holding nothing).
pub async fn try_lock(pool: &PgPool, repo_id: Uuid) -> Result<Option<PoolConnection<Postgres>>> {
    let mut conn = pool.acquire().await?;
    let got: bool = sqlx::query_scalar("SELECT pg_try_advisory_lock($1)")
        .bind(advisory_key(repo_id))
        .fetch_one(&mut *conn)
        .await?;
    Ok(if got { Some(conn) } else { None })
}

/// Block until the repo's advisory lock is acquired, then return the connection
/// holding it. Used by a foreground job after it has set the preempt flag: the
/// current holder (a daemon reindex, or another CLI) releases and this wakes.
pub async fn lock_blocking(pool: &PgPool, repo_id: Uuid) -> Result<PoolConnection<Postgres>> {
    let mut conn = pool.acquire().await?;
    sqlx::query("SELECT pg_advisory_lock($1)")
        .bind(advisory_key(repo_id))
        .execute(&mut *conn)
        .await?;
    Ok(conn)
}

/// Release the advisory lock held on `conn`. Call on the normal completion path;
/// a crash / Ctrl-C releases it automatically when the session ends.
pub async fn unlock(conn: &mut PoolConnection<Postgres>, repo_id: Uuid) -> Result<()> {
    sqlx::query("SELECT pg_advisory_unlock($1)")
        .bind(advisory_key(repo_id))
        .execute(&mut **conn)
        .await?;
    Ok(())
}

/// Mark a repo as owed a (re)index. Called at the START of a foreground index so
/// that any interruption (Ctrl-C, crash, lock auto-release) leaves indexed_at
/// NULL — owed — rather than pointing at a stale, partially-rebuilt index.
/// everIndexed is left unchanged. Spec: Muninn.IndexFsm.interrupt.
pub async fn mark_unindexed(pool: &PgPool, repo_id: Uuid) -> Result<()> {
    sqlx::query(r#"UPDATE repos SET indexed_at = NULL WHERE id = $1"#)
        .bind(repo_id)
        .execute(pool)
        .await?;
    Ok(())
}

/// Set or clear a repo's paused flag. When paused, the daemon skips the repo
/// entirely (no reindex, no watcher) without dropping data. Spec:
/// Muninn.Index.daemonDecision (paused → Skip).
pub async fn set_paused(pool: &PgPool, repo_id: Uuid, paused: bool) -> Result<()> {
    sqlx::query(r#"UPDATE repos SET paused = $2 WHERE id = $1"#)
        .bind(repo_id)
        .bind(paused)
        .execute(pool)
        .await?;
    Ok(())
}

/// Signal that a foreground job is waiting for the lock and the current
/// background holder should yield. Spec: Muninn.AdvisoryLock preempt.
pub async fn request_preempt(pool: &PgPool, repo_id: Uuid) -> Result<()> {
    sqlx::query(r#"UPDATE repos SET preempt_requested = TRUE WHERE id = $1"#)
        .bind(repo_id)
        .execute(pool)
        .await?;
    Ok(())
}

/// Clear the preempt flag. Called by a foreground job once it has acquired the
/// lock (it is the job the waiter was after).
pub async fn clear_preempt(pool: &PgPool, repo_id: Uuid) -> Result<()> {
    sqlx::query(r#"UPDATE repos SET preempt_requested = FALSE WHERE id = $1"#)
        .bind(repo_id)
        .execute(pool)
        .await?;
    Ok(())
}

/// Whether a foreground job has requested preemption. The background reindex
/// task polls this every ~10 s and yields the lock when it is true.
pub async fn is_preempt_requested(pool: &PgPool, repo_id: Uuid) -> Result<bool> {
    let row = sqlx::query(r#"SELECT preempt_requested FROM repos WHERE id = $1"#)
        .bind(repo_id)
        .fetch_optional(pool)
        .await?;
    Ok(row
        .map(|r| r.try_get::<bool, _>("preempt_requested"))
        .transpose()?
        .unwrap_or(false))
}

// ---- helpers ----------------------------------------------------------------

fn row_to_repo(row: sqlx::postgres::PgRow) -> Result<Repo> {
    Ok(Repo {
        id: row.try_get::<Uuid, _>("id")?,
        path: row.try_get::<String, _>("path")?,
        name: row.try_get::<String, _>("name")?,
        indexed_at: row.try_get::<Option<DateTime<Utc>>, _>("indexed_at")?,
        ever_indexed: row.try_get::<bool, _>("ever_indexed")?,
        embedding_dim: row.try_get::<i32, _>("embedding_dim")? as u32,
        preempt_requested: row.try_get::<bool, _>("preempt_requested")?,
        paused: row.try_get::<bool, _>("paused")?,
    })
}
