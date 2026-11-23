//! Exclusion cleanup adapter: bounded, retryable deletion of captured records
//! that current readers and accepted work no longer need. Every committed
//! transaction boundary below is registered in `CRASH_BOUNDARIES` and checked
//! by muninn-setup/crash-injection-check.sh; a crash at an unregistered
//! boundary cannot be retried against the world outcome.
//!
//! Boundary mapping (see spec/CRASH-BOUNDARIES.json):
//! - exclusion.admission       -> admit_reader            (CleanupAdmission)
//! - exclusion.batch-deletion  -> run_batch               (CleanupEffects/CleanupLoop)
//! - exclusion.receipt-checkpoint -> checkpoint_receipt   (PolicyCleanupBatch)
//! - exclusion.followup-capture   -> capture_followup     (CleanupScheduling)
//! - exclusion.finalization       -> finalize_task        (CleanupFinalization)

use anyhow::{Context, Result};
use tokio_postgres::{Client, GenericClient};
use uuid::Uuid;

pub const CRASH_BOUNDARIES: &[&str] = &[
    "exclusion.admission",
    "exclusion.batch-deletion",
    "exclusion.receipt-checkpoint",
    "exclusion.followup-capture",
    "exclusion.finalization",
];

fn qualified(schema: &str, table: &str) -> String {
    format!("\"{schema}\".{table}")
}

pub struct CleanupTask {
    pub id: Uuid,
    pub operation_id: String,
    pub captured_ids: Vec<Uuid>,
    pub payload: String,
}

/// Read the cleanup task for one operation, if present.
pub async fn task_for_operation(
    client: &impl GenericClient,
    schema: &str,
    operation_id: &str,
) -> Result<Option<CleanupTask>> {
    let row = client
        .query_opt(
            &format!(
                "SELECT id, operation_id, captured_ids, payload FROM {} WHERE operation_id = $1",
                qualified(schema, "cleanup_work")
            ),
            &[&operation_id],
        )
        .await
        .context("read cleanup task")?;
    Ok(row.map(|row| CleanupTask {
        id: row.get(0),
        operation_id: row.get(1),
        captured_ids: row.get(2),
        payload: row.get(3),
    }))
}

/// exclusion.admission: admit a reader holding the given references in one
/// shared transaction; the stored row keeps those records protected.
pub async fn admit_reader(
    client: &Client,
    schema: &str,
    references: &[Uuid],
    payload: &str,
) -> Result<Uuid> {
    crate::owned_control::insert_reader(client, schema, references, payload).await
}

/// exclusion.batch-deletion: one bounded transaction deleting captured chunk
/// records that no reader reference or accepted work still holds. Committed
/// deletions are their own progress checkpoint; an interrupted batch is
/// retried with the same captured identity set.
pub async fn run_batch(client: &mut Client, schema: &str, task: &CleanupTask) -> Result<u64> {
    let tx = client.transaction().await?;
    let rows = tx
        .execute(
            &format!(
                "DELETE FROM {chunks} WHERE id = ANY($1) \
                 AND file_version IS NULL AND NOT (in_base) \
                 AND NOT EXISTS (SELECT 1 FROM {readers} r WHERE id = ANY(r.references)) \
                 AND NOT EXISTS (SELECT 1 FROM {work} w WHERE id = ANY(w.captured_ids))",
                chunks = qualified(schema, "chunks"),
                readers = qualified(schema, "active_readers"),
                work = qualified(schema, "accepted_work"),
            ),
            &[&task.captured_ids],
        )
        .await
        .context("bounded cleanup batch")?;
    tx.commit().await?;
    Ok(rows)
}

/// exclusion.receipt-checkpoint: seal the batch progress into the receipt in
/// the same transaction as the next batch run.
pub async fn checkpoint_receipt(
    client: &Client,
    schema: &str,
    operation_id: &str,
    work: &serde_json::Value,
) -> Result<u64> {
    crate::owned_control::update_receipt_checkpoint(client, schema, operation_id, work).await
}

/// exclusion.followup-capture: commit a follow-up workset for newly captured
/// blocking records under the same operation.
pub async fn capture_followup(
    client: &Client,
    schema: &str,
    operation_id: &str,
    captured_ids: &[Uuid],
    payload: &str,
) -> Result<Uuid> {
    crate::owned_control::insert_cleanup_task(client, schema, operation_id, captured_ids, payload)
        .await
}

/// exclusion.finalization: remove the completed task and compact the receipt
/// to its ID-only marker.
pub async fn finalize_task(client: &mut Client, schema: &str, task: &CleanupTask) -> Result<()> {
    let tx = client.transaction().await?;
    tx.execute(
        &format!(
            "DELETE FROM {} WHERE id = $1",
            qualified(schema, "cleanup_work")
        ),
        &[&task.id],
    )
    .await
    .context("finalize cleanup task")?;
    tx.execute(
        &format!(
            "DELETE FROM {} WHERE operation_id = $1",
            qualified(schema, "receipts")
        ),
        &[&task.operation_id],
    )
    .await
    .context("compact finished receipt")?;
    tx.execute(
        "INSERT INTO receipt_markers (operation_id) VALUES ($1) ON CONFLICT (operation_id) DO NOTHING",
        &[&task.operation_id],
    )
    .await
    .context("receipt marker")?;
    tx.commit().await?;
    Ok(())
}
