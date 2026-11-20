//! Serialized selection maintenance using the existing family lock key.
use anyhow::{ensure, Result};
use tokio_postgres::{Client, GenericClient, Transaction};
use uuid::Uuid;

/// Durable commit boundaries; checked against spec/CRASH-BOUNDARIES.json.
pub const CRASH_BOUNDARIES: &[&str] = &[
    "exclusion.request",
    "exclusion.publication",
    "exclusion.error",
];

fn table(family: Uuid) -> String {
    format!(
        "\"{}\".selection_maintenance",
        crate::store::repo_schema(family)
    )
}

pub async fn pending(client: &impl GenericClient, family: Uuid) -> Result<bool> {
    let table = table(family);
    let exists: bool = client
        .query_one("SELECT to_regclass($1) IS NOT NULL", &[&table])
        .await?
        .get(0);
    if !exists {
        return Ok(false);
    }
    Ok(client
        .query_one(
            &format!("SELECT EXISTS(SELECT 1 FROM {table} WHERE requested>completed)"),
            &[],
        )
        .await?
        .get(0))
}

pub async fn read(client: &mut Client, family: Uuid) -> Result<Transaction<'_>> {
    let tx = client.transaction().await?;
    let admitted: bool = tx
        .query_one(
            "SELECT pg_try_advisory_xact_lock_shared(hashtextextended($1,771913))",
            &[&family.to_string()],
        )
        .await?
        .get(0);
    ensure!(
        admitted,
        "family_busy: indexing or maintenance is running; retry later"
    );
    ensure!(
        !pending(&tx, family).await?,
        "family_maintenance: selection refresh is pending; inspect family status"
    );
    Ok(tx)
}

pub async fn ordinary_write(client: &mut Client, family: Uuid) -> Result<Transaction<'_>> {
    let tx = client.transaction().await?;
    crate::worktrees::lock(&tx, family).await?;
    ensure!(
        !pending(&tx, family).await?,
        "family_maintenance: selection refresh is pending"
    );
    Ok(tx)
}

// Call under the exclusive family lock. PostgreSQL rejects counter overflow.
pub(crate) async fn request(tx: &Transaction<'_>, family: Uuid, target: Uuid) -> Result<()> {
    let table = table(family);
    tx.execute(&format!("INSERT INTO {table}(target,requested,completed) VALUES($1,1,0) ON CONFLICT(target) DO UPDATE SET requested=selection_maintenance.requested+1,last_error=NULL"), &[&target]).await?;
    Ok(())
}

pub(crate) async fn request_family(tx: &Transaction<'_>, family: Uuid) -> Result<()> {
    let git: bool = tx
        .query_one(
            "SELECT COALESCE(family_kind='git',false) FROM public.repos WHERE id=$1",
            &[&family],
        )
        .await?
        .get(0);
    if !git {
        return request(tx, family, family).await;
    }
    let schema = crate::store::repo_schema(family);
    let targets = tx
        .query(
            &format!("SELECT id FROM \"{schema}\".checkouts WHERE registration_state<>'retired'"),
            &[],
        )
        .await?;
    if targets.is_empty() {
        request(tx, family, family).await?;
    } else {
        for target in targets {
            request(tx, family, target.get(0)).await?;
        }
    }
    Ok(())
}

pub(crate) async fn generation(
    tx: &Transaction<'_>,
    family: Uuid,
    target: Uuid,
) -> Result<Option<i64>> {
    Ok(tx
        .query_opt(
            &format!(
                "SELECT requested FROM {} WHERE target=$1 AND requested>completed",
                table(family)
            ),
            &[&target],
        )
        .await?
        .map(|row| row.get(0)))
}

pub(crate) async fn complete(
    tx: &Transaction<'_>,
    family: Uuid,
    target: Uuid,
    generation: Option<i64>,
) -> Result<()> {
    let table = table(family);
    if let Some(generation) = generation {
        tx.execute(
            &format!("UPDATE {table} SET completed=$2,last_error=NULL WHERE target=$1"),
            &[&target, &generation],
        )
        .await?;
    }
    Ok(())
}

pub(crate) async fn forget(tx: &Transaction<'_>, family: Uuid, target: Uuid) -> Result<()> {
    let table = table(family);
    tx.execute(&format!("DELETE FROM {table} WHERE target=$1"), &[&target])
        .await?;
    Ok(())
}

pub(crate) async fn failed(
    client: &mut Client,
    family: Uuid,
    target: Uuid,
    error: &str,
) -> Result<()> {
    let table = table(family);
    let tx = client.transaction().await?;
    crate::worktrees::lock(&tx, family).await?;
    let error: String = error.chars().take(2048).collect();
    tx.execute(
        &format!("UPDATE {table} SET last_error=$2 WHERE target=$1 AND requested>completed"),
        &[&target, &error],
    )
    .await?;
    tx.commit().await?;
    Ok(())
}

pub async fn status(client: &impl GenericClient, family: Uuid) -> Result<serde_json::Value> {
    if !pending(client, family).await? {
        return Ok(serde_json::json!({"pending":false,"targets":[]}));
    }
    let rows = client.query(&format!("SELECT target,requested,completed,last_error FROM {} WHERE requested>completed ORDER BY target",table(family)), &[]).await?;
    let targets: Vec<_> = rows
        .into_iter()
        .map(|row| {
            serde_json::json!({
                "target":row.get::<_,Uuid>(0),"requested":row.get::<_,i64>(1),
                "completed":row.get::<_,i64>(2),"last_error":row.get::<_,Option<String>>(3)
            })
        })
        .collect();
    Ok(serde_json::json!({"pending":true,"targets":targets}))
}
