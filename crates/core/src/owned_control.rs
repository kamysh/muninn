//! Family-owned logical control records: legacy file facts, configuration
//! staging, accepted work, cleanup tasks, readers, continuations and durable
//! receipts, plus the installation-owned ID-only receipt markers.
//!
//! Each function writes exactly the modeled record category; the statements
//! are declared in spec/RECORD-CORRESPONDENCE.json and checked mechanically.

use anyhow::{bail, Context, Result};
use tokio_postgres::{Client, GenericClient};
use uuid::Uuid;

fn qualified(schema: &str, table: &str) -> String {
    format!("\"{schema}\".{table}")
}

/// Legacy file fact: the saved Git answer and remaining payload for one path.
pub async fn upsert_legacy_file(
    client: &Client,
    schema: &str,
    path: &str,
    git_answer: &str,
    payload: &str,
) -> Result<()> {
    client
        .execute(
            &format!(
                "INSERT INTO {} (path, git_answer, payload) VALUES ($1,$2,$3) \
                 ON CONFLICT (path) DO UPDATE SET git_answer = EXCLUDED.git_answer, payload = EXCLUDED.payload",
                qualified(schema, "legacy_files")
            ),
            &[&path, &git_answer, &payload],
        )
        .await
        .context("upsert legacy file fact")?;
    Ok(())
}

/// Temporary configuration staging row.
pub async fn insert_staging(client: &Client, schema: &str, payload: &str) -> Result<Uuid> {
    let id = Uuid::new_v4();
    client
        .execute(
            &format!(
                "INSERT INTO {} (id, payload) VALUES ($1,$2)",
                qualified(schema, "staging")
            ),
            &[&id, &payload],
        )
        .await
        .context("insert staging row")?;
    Ok(id)
}

/// Accepted work: the owning operation, captured record identities and the
/// work payload.
pub async fn accept_work(
    client: &Client,
    schema: &str,
    operation_id: &str,
    captured_ids: &[Uuid],
    payload: &str,
) -> Result<Uuid> {
    let id = Uuid::new_v4();
    client
        .execute(
            &format!(
                "INSERT INTO {} (id, operation_id, captured_ids, payload) VALUES ($1,$2,$3,$4)",
                qualified(schema, "accepted_work")
            ),
            &[&id, &operation_id, &captured_ids, &payload],
        )
        .await
        .context("insert accepted work")?;
    Ok(id)
}

/// Cancel: remove accepted work for one operation; committed results stay.
pub async fn cancel_accepted_work(
    client: &Client,
    schema: &str,
    operation_id: &str,
) -> Result<u64> {
    let rows = client
        .execute(
            &format!(
                "DELETE FROM {} WHERE operation_id = $1",
                qualified(schema, "accepted_work")
            ),
            &[&operation_id],
        )
        .await
        .context("cancel accepted work")?;
    Ok(rows)
}

/// Cleanup task: the owning operation, captured identities and payload.
pub async fn insert_cleanup_task(
    client: &Client,
    schema: &str,
    operation_id: &str,
    captured_ids: &[Uuid],
    payload: &str,
) -> Result<Uuid> {
    let id = Uuid::new_v4();
    client
        .execute(
            &format!(
                "INSERT INTO {} (id, operation_id, captured_ids, payload) VALUES ($1,$2,$3,$4)",
                qualified(schema, "cleanup_work")
            ),
            &[&id, &operation_id, &captured_ids, &payload],
        )
        .await
        .context("insert cleanup task")?;
    Ok(id)
}

pub async fn delete_cleanup_task(client: &Client, schema: &str, id: Uuid) -> Result<u64> {
    let rows = client
        .execute(
            &format!(
                "DELETE FROM {} WHERE id = $1",
                qualified(schema, "cleanup_work")
            ),
            &[&id],
        )
        .await
        .context("delete cleanup task")?;
    Ok(rows)
}

/// Reader record: the held references and the reader payload.
pub async fn insert_reader(
    client: &Client,
    schema: &str,
    references: &[Uuid],
    payload: &str,
) -> Result<Uuid> {
    let id = Uuid::new_v4();
    client
        .execute(
            &format!(
                "INSERT INTO {} (id, references, payload) VALUES ($1,$2,$3)",
                qualified(schema, "active_readers")
            ),
            &[&id, &references, &payload],
        )
        .await
        .context("insert reader")?;
    Ok(id)
}

pub async fn delete_reader(client: &Client, schema: &str, id: Uuid) -> Result<u64> {
    let rows = client
        .execute(
            &format!(
                "DELETE FROM {} WHERE id = $1",
                qualified(schema, "active_readers")
            ),
            &[&id],
        )
        .await
        .context("delete reader")?;
    Ok(rows)
}

/// Saved continuation: captured identities and the continuation payload.
pub async fn insert_continuation(
    client: &Client,
    schema: &str,
    captured_ids: &[Uuid],
    payload: &str,
) -> Result<Uuid> {
    let id = Uuid::new_v4();
    client
        .execute(
            &format!(
                "INSERT INTO {} (id, captured_ids, payload) VALUES ($1,$2,$3)",
                qualified(schema, "continuations")
            ),
            &[&id, &captured_ids, &payload],
        )
        .await
        .context("insert continuation")?;
    Ok(id)
}

/// Durable receipt: accepted active work for one operation ID.
pub async fn accept_receipt(
    client: &Client,
    schema: &str,
    operation_id: &str,
    input: &serde_json::Value,
    work: &serde_json::Value,
) -> Result<bool> {
    let rows = client
        .execute(
            &format!(
                "INSERT INTO {} (operation_id, state, input, work) VALUES ($1,'active',$2,$3) \
                 ON CONFLICT (operation_id) DO NOTHING",
                qualified(schema, "receipts")
            ),
            &[&operation_id, &input, &work],
        )
        .await
        .context("accept receipt")?;
    if rows == 0 {
        let state: Option<String> = client
            .query_opt(
                &format!(
                    "SELECT state FROM {} WHERE operation_id = $1",
                    qualified(schema, "receipts")
                ),
                &[&operation_id],
            )
            .await
            .context("read receipt state")?
            .map(|row| row.get(0));
        bail!("receipt {operation_id} already exists in state {state:?}");
    }
    Ok(true)
}

/// Receipt checkpoint update: the business transaction seals its progress.
pub async fn update_receipt_checkpoint(
    client: &Client,
    schema: &str,
    operation_id: &str,
    work: &serde_json::Value,
) -> Result<u64> {
    let rows = client
        .execute(
            &format!(
                "UPDATE {} SET work = $2, updated_at = now() WHERE operation_id = $1 AND state = 'active'",
                qualified(schema, "receipts")
            ),
            &[&operation_id, &work],
        )
        .await
        .context("update receipt checkpoint")?;
    Ok(rows)
}

/// Finished receipt: the saved result replaces the active work.
pub async fn finish_receipt(
    client: &Client,
    schema: &str,
    operation_id: &str,
    result: &serde_json::Value,
) -> Result<u64> {
    let rows = client
        .execute(
            &format!(
                "UPDATE {} SET state = 'finished', result = $2, work = NULL, updated_at = now() \
                 WHERE operation_id = $1 AND state = 'active'",
                qualified(schema, "receipts")
            ),
            &[&operation_id, &result],
        )
        .await
        .context("finish receipt")?;
    Ok(rows)
}

/// Saved receipt for one operation ID, if present in this family schema.
pub async fn read_receipt(
    client: &impl GenericClient,
    schema: &str,
    operation_id: &str,
) -> Result<Option<Receipt>> {
    let row = client
        .query_opt(
            &format!(
                "SELECT state, input, work, result FROM {} WHERE operation_id = $1",
                qualified(schema, "receipts")
            ),
            &[&operation_id],
        )
        .await
        .context("read receipt")?;
    Ok(row.map(|row| Receipt {
        state: row.get(0),
        input: row.get(1),
        work: row.get(2),
        result: row.get(3),
    }))
}

/// Receipt projection used by the continuation adapter.
pub struct Receipt {
    pub state: String,
    pub input: Option<serde_json::Value>,
    pub work: Option<serde_json::Value>,
    pub result: Option<serde_json::Value>,
}

/// Installation-owned ID-only marker; a used operation ID never permits
/// another execution and never belongs to a removed family.
pub async fn compact_receipt_marker(client: &Client, operation_id: &str) -> Result<()> {
    client
        .execute(
            "INSERT INTO receipt_markers (operation_id) VALUES ($1) ON CONFLICT (operation_id) DO NOTHING",
            &[&operation_id],
        )
        .await
        .context("compact receipt marker")?;
    Ok(())
}

pub async fn marker_exists<C: GenericClient>(client: &C, operation_id: &str) -> Result<bool> {
    let row = client
        .query_opt(
            "SELECT operation_id FROM receipt_markers WHERE operation_id = $1",
            &[&operation_id],
        )
        .await
        .context("read receipt marker")?;
    Ok(row.is_some())
}
