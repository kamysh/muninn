use crate::config::DatabaseConfig;
use crate::db::connect_for_lock;
use crate::types::{Chunk, Repo};
use anyhow::Result;
use chrono::{DateTime, Utc};
use pgvector::Vector;
use std::sync::Arc;
use tokio_postgres::{Client, Row};
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
    client: &Client,
    path: &str,
    name: &str,
    embedding_dim: usize,
) -> Result<Repo> {
    let row = client
        .query_one(
            &format!(
                r#"
        INSERT INTO repos (id, path, name, indexed_at, embedding_dim)
        VALUES ($1, $2, $3, NULL, $4)
        ON CONFLICT (path) DO UPDATE SET name = EXCLUDED.name
        RETURNING {REPO_COLUMNS}
        "#
            ),
            &[&Uuid::new_v4(), &path, &name, &(embedding_dim as i32)],
        )
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
    client
        .execute(
            &format!(
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
            ),
            &[],
        )
        .await?;

    client
        .execute(
            &format!(
                r#"CREATE INDEX IF NOT EXISTS "{table}_ts_idx" ON "{table}" USING GIN (ts_vector)"#
            ),
            &[],
        )
        .await?;

    client
        .execute(
            &format!(
                r#"CREATE INDEX IF NOT EXISTS "{table}_emb_idx" ON "{table}" USING hnsw (embedding vector_cosine_ops)"#
            ),
            &[],
        )
        .await?;

    client
        .execute(
            &format!(
                r#"CREATE INDEX IF NOT EXISTS "{table}_file_idx" ON "{table}" (file_path)"#
            ),
            &[],
        )
        .await?;

    // Create per-repo AGE graph (idempotent: check before create)
    let gname = graph_name(repo.id);
    let graph_exists: bool = client
        .query_one(
            "SELECT EXISTS(SELECT 1 FROM ag_catalog.ag_graph WHERE name = $1)",
            &[&gname],
        )
        .await?
        .get(0);

    if !graph_exists {
        client
            .execute(
                &format!("SELECT * FROM ag_catalog.create_graph('{gname}')"),
                &[],
            )
            .await?;
    }

    // Ensure the four known vertex labels exist and have property indexes on
    // `chunk_id` (MERGE hot path in upsert_symbol_nodes) and `file_path` (MATCH
    // hot path in delete_file_symbols). Idempotent; mirrors migration 014.
    client
        .execute(
            &format!(
                r#"
        DO $do$
        DECLARE
            lbl    TEXT;
            labels TEXT[] := ARRAY['Function', 'Class', 'Import', 'Module'];
        BEGIN
            FOREACH lbl IN ARRAY labels LOOP
                BEGIN
                    PERFORM ag_catalog.create_vlabel('{gname}', lbl);
                EXCEPTION WHEN others THEN NULL;
                END;
                IF EXISTS (
                    SELECT 1
                    FROM pg_class c
                    JOIN pg_namespace n ON c.relnamespace = n.oid
                    WHERE n.nspname = '{gname}' AND c.relname = lbl
                ) THEN
                    EXECUTE format(
                        'CREATE INDEX IF NOT EXISTS %I ON %I.%I USING btree '
                        '((properties -> ''"chunk_id"''::ag_catalog.agtype))',
                        lbl || '_chunk_id_idx', '{gname}', lbl
                    );
                    EXECUTE format(
                        'CREATE INDEX IF NOT EXISTS %I ON %I.%I USING btree '
                        '((properties -> ''"file_path"''::ag_catalog.agtype))',
                        lbl || '_file_path_idx', '{gname}', lbl
                    );
                END IF;
            END LOOP;
        END
        $do$;
        "#
            ),
            &[],
        )
        .await?;

    // Ensure the four known edge labels exist (idempotent).
    // AGE requires explicit create_elabel before MERGE can create edges of that type.
    client
        .execute(
            &format!(
                r#"
        DO $do$
        DECLARE
            lbl TEXT;
            labels TEXT[] := ARRAY['CALLS', 'IMPORTS', 'DEFINES', 'INHERITS_FROM'];
        BEGIN
            FOREACH lbl IN ARRAY labels LOOP
                BEGIN
                    PERFORM ag_catalog.create_elabel('{gname}', lbl);
                EXCEPTION WHEN others THEN NULL;
                END;
            END LOOP;
        END
        $do$;
        "#
            ),
            &[],
        )
        .await?;

    Ok(repo)
}

pub async fn delete_repo(client: &Client, repo_id: Uuid) -> Result<()> {
    let table = chunks_table(repo_id);
    client
        .execute(&format!(r#"DROP TABLE IF EXISTS "{table}""#), &[])
        .await?;

    let gname = graph_name(repo_id);
    let graph_exists: bool = client
        .query_one(
            "SELECT EXISTS(SELECT 1 FROM ag_catalog.ag_graph WHERE name = $1)",
            &[&gname],
        )
        .await?
        .get(0);

    if graph_exists {
        client
            .execute(
                &format!("SELECT * FROM ag_catalog.drop_graph('{gname}', true)"),
                &[],
            )
            .await?;
    }

    client
        .execute(r#"DELETE FROM repos WHERE id = $1"#, &[&repo_id])
        .await?;
    Ok(())
}

pub async fn get_repo_by_path(client: &Client, path: &str) -> Result<Option<Repo>> {
    let row = client
        .query_opt(
            &format!(r#"SELECT {REPO_COLUMNS} FROM repos WHERE path = $1"#),
            &[&path],
        )
        .await?;
    row.map(row_to_repo).transpose()
}

pub async fn list_repos(client: &Client) -> Result<Vec<Repo>> {
    let rows = client
        .query(
            &format!(r#"SELECT {REPO_COLUMNS} FROM repos ORDER BY name"#),
            &[],
        )
        .await?;
    rows.into_iter().map(row_to_repo).collect()
}

/// Notify the indexer daemon that the set of registered repos has changed.
pub async fn notify_repos_changed(client: &Client) -> Result<()> {
    client
        .execute("SELECT pg_notify('muninn_repos_changed', '')", &[])
        .await?;
    Ok(())
}

pub async fn mark_indexed(client: &Client, repo_id: Uuid) -> Result<()> {
    client
        .execute(
            r#"UPDATE repos SET indexed_at = NOW(), ever_indexed = TRUE WHERE id = $1"#,
            &[&repo_id],
        )
        .await?;
    Ok(())
}

pub async fn upsert_chunk(client: &Client, chunk: &Chunk) -> Result<Uuid> {
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
    let embedding: Option<Vector> = chunk.embedding.as_ref().map(|emb| Vector::from(emb.clone()));

    let sql = format!(
        r#"
        INSERT INTO "{table}" (id, repo_id, file_path, start_line, end_line, content, embedding)
        VALUES ($1, $2, $3, $4, $5, $6, $7)
        ON CONFLICT (id) DO UPDATE
            SET file_path  = EXCLUDED.file_path,
                start_line = EXCLUDED.start_line,
                end_line   = EXCLUDED.end_line,
                content    = EXCLUDED.content,
                embedding  = EXCLUDED.embedding
        RETURNING id
        "#
    );

    let row = client
        .query_one(
            &sql,
            &[
                &chunk.id,
                &chunk.repo_id,
                &chunk.file_path,
                &(chunk.range.start as i32),
                &(chunk.range.end as i32),
                &chunk.content,
                &embedding,
            ],
        )
        .await?;

    let id: Uuid = row.try_get(0)?;
    Ok(id)
}

pub async fn delete_file_chunks(client: &Client, repo_id: Uuid, file_path: &str) -> Result<()> {
    anyhow::ensure!(
        !file_path.is_empty(),
        "NonEmptyFilePath violation: file_path must not be empty"
    );
    let table = chunks_table(repo_id);
    client
        .execute(
            &format!(r#"DELETE FROM "{table}" WHERE file_path = $1"#),
            &[&file_path],
        )
        .await?;
    Ok(())
}

/// Delete every chunk for a repo whose `file_path` is not in `keep`.
pub async fn prune_chunks_not_in(client: &Client, repo_id: Uuid, keep: &[String]) -> Result<u64> {
    let table = chunks_table(repo_id);
    let n = client
        .execute(
            &format!(r#"DELETE FROM "{table}" WHERE file_path <> ALL($1)"#),
            &[&keep],
        )
        .await?;
    Ok(n)
}

/// Distinct `file_path`s currently in the repo's chunk store that are NOT in `keep`.
pub async fn file_paths_not_in(
    client: &Client,
    repo_id: Uuid,
    keep: &[String],
) -> Result<Vec<String>> {
    let table = chunks_table(repo_id);
    let rows = client
        .query(
            &format!(
                r#"SELECT DISTINCT file_path FROM "{table}" WHERE file_path <> ALL($1)"#
            ),
            &[&keep],
        )
        .await?;
    Ok(rows.into_iter().map(|r| r.get::<_, String>(0)).collect())
}

// ---- indexing lock (PostgreSQL session-scoped advisory lock) ----------------
//
// The advisory lock is held on a DEDICATED connection for the index's duration.
// Liveness is the TCP session itself: if the holder's process dies, PostgreSQL
// frees the lock automatically. Spec: Muninn.AdvisoryLock.

/// The advisory-lock key for a repo: the first 8 bytes of its UUID as an i64.
fn advisory_key(repo_id: Uuid) -> i64 {
    let b = repo_id.as_bytes();
    i64::from_le_bytes([b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]])
}

/// Try to acquire the repo's advisory lock without blocking. On success returns
/// an `Arc<Client>` whose underlying connection holds the lock. On contention
/// returns `None`.
pub async fn try_lock(cfg: &DatabaseConfig, repo_id: Uuid) -> Result<Option<Arc<Client>>> {
    let lock_client = connect_for_lock(cfg).await?;
    let got: bool = lock_client
        .query_one("SELECT pg_try_advisory_lock($1)", &[&advisory_key(repo_id)])
        .await?
        .get(0);
    if got {
        Ok(Some(lock_client))
    } else {
        Ok(None)
    }
}

/// Block until the repo's advisory lock is acquired, then return the connection
/// holding it.
pub async fn lock_blocking(cfg: &DatabaseConfig, repo_id: Uuid) -> Result<Arc<Client>> {
    let lock_client = connect_for_lock(cfg).await?;
    lock_client
        .execute("SELECT pg_advisory_lock($1)", &[&advisory_key(repo_id)])
        .await?;
    Ok(lock_client)
}

/// Release the advisory lock. Call on the normal completion path; a crash /
/// Ctrl-C releases it automatically when the session ends.
pub async fn unlock(conn: &Arc<Client>, repo_id: Uuid) -> Result<()> {
    conn.execute("SELECT pg_advisory_unlock($1)", &[&advisory_key(repo_id)])
        .await?;
    Ok(())
}

/// Mark a repo as owed a (re)index. Spec: Muninn.IndexFsm.interrupt.
pub async fn mark_unindexed(client: &Client, repo_id: Uuid) -> Result<()> {
    client
        .execute(
            r#"UPDATE repos SET indexed_at = NULL WHERE id = $1"#,
            &[&repo_id],
        )
        .await?;
    Ok(())
}

/// Set or clear a repo's paused flag. Spec: Muninn.Index.daemonDecision.
pub async fn set_paused(client: &Client, repo_id: Uuid, paused: bool) -> Result<()> {
    client
        .execute(
            r#"UPDATE repos SET paused = $2 WHERE id = $1"#,
            &[&repo_id, &paused],
        )
        .await?;
    Ok(())
}

/// Signal that a foreground job is waiting for the lock. Spec: Muninn.AdvisoryLock preempt.
pub async fn request_preempt(client: &Client, repo_id: Uuid) -> Result<()> {
    client
        .execute(
            r#"UPDATE repos SET preempt_requested = TRUE WHERE id = $1"#,
            &[&repo_id],
        )
        .await?;
    Ok(())
}

/// Clear the preempt flag.
pub async fn clear_preempt(client: &Client, repo_id: Uuid) -> Result<()> {
    client
        .execute(
            r#"UPDATE repos SET preempt_requested = FALSE WHERE id = $1"#,
            &[&repo_id],
        )
        .await?;
    Ok(())
}

/// Whether a foreground job has requested preemption.
pub async fn is_preempt_requested(client: &Client, repo_id: Uuid) -> Result<bool> {
    let row = client
        .query_opt(
            r#"SELECT preempt_requested FROM repos WHERE id = $1"#,
            &[&repo_id],
        )
        .await?;
    Ok(row.map(|r| r.get::<_, bool>(0)).unwrap_or(false))
}

// ---- helpers ----------------------------------------------------------------

fn row_to_repo(row: Row) -> Result<Repo> {
    Ok(Repo {
        id:                row.try_get("id")?,
        path:              row.try_get("path")?,
        name:              row.try_get("name")?,
        indexed_at:        row.try_get::<_, Option<DateTime<Utc>>>("indexed_at")?,
        ever_indexed:      row.try_get("ever_indexed")?,
        embedding_dim:     row.try_get::<_, i32>("embedding_dim")? as u32,
        preempt_requested: row.try_get("preempt_requested")?,
        paused:            row.try_get("paused")?,
    })
}
