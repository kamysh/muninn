//! Durable checkout-local selection refresh receipts.
use anyhow::Result;
use std::{
    collections::BTreeSet,
    path::{Path, PathBuf},
};
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

pub async fn read(client: &mut Client, _family: Uuid) -> Result<Transaction<'_>> {
    Ok(client
        .build_transaction()
        .isolation_level(tokio_postgres::IsolationLevel::RepeatableRead)
        .read_only(true)
        .start()
        .await?)
}

/// Older standalone indexes have absolute chunk paths and no checkout
/// membership. A pending policy still filters that committed view.
pub async fn legacy_hidden_paths(tx: &Transaction<'_>, family: Uuid) -> Result<BTreeSet<String>> {
    if !pending(tx, family).await? {
        return Ok(BTreeSet::new());
    }
    let root: String = tx
        .query_one("SELECT path FROM public.repos WHERE id=$1", &[&family])
        .await?
        .get(0);
    let root = Path::new(&root);
    let policy = crate::family_policy::runtime::policy(tx, family).await?;
    let selection = crate::family_policy::runtime::Selection::new(root, policy.as_ref(), &[], &[])?;
    let paths: Vec<String> = tx
        .query(
            &format!(
                "SELECT DISTINCT file_path FROM {} WHERE file_version IS NULL",
                crate::store::chunks_ref(family)
            ),
            &[],
        )
        .await?
        .into_iter()
        .map(|row| row.get(0))
        .collect();
    let relative: Vec<_> = paths
        .iter()
        .map(|path| {
            Path::new(path)
                .strip_prefix(root)
                .unwrap_or(Path::new(path))
                .to_owned()
        })
        .collect();
    let ignored = if crate::repo_resolver::discover_git_checkout(root)
        .await?
        .is_some()
    {
        let paths: Vec<PathBuf> = relative
            .iter()
            .filter(|path| path.is_relative())
            .cloned()
            .collect();
        let mut ignored = crate::git_ignore::check(root, &paths).await?.into_iter();
        relative
            .iter()
            .map(|path| path.is_relative() && ignored.next().unwrap_or(false))
            .collect()
    } else {
        vec![false; relative.len()]
    };
    Ok(paths
        .into_iter()
        .zip(relative)
        .zip(ignored)
        .filter_map(|((path, relative), ignored)| {
            use crate::pipeline::Decision::Drop;
            (relative.is_absolute()
                || selection.classify_with_git(&relative, false, ignored) == Drop
                || relative
                    .ancestors()
                    .skip(1)
                    .filter(|p| !p.as_os_str().is_empty())
                    .any(|p| selection.classify(p, true) == Drop))
            .then_some(path)
        })
        .collect())
}

/// Serialize writes to the legacy single-checkout index. Worktree versions
/// and membership updates have their own narrower coordination.
pub async fn ordinary_write(client: &mut Client, family: Uuid) -> Result<Transaction<'_>> {
    let tx = client.transaction().await?;
    crate::worktrees::lock(&tx, family).await?;
    Ok(tx)
}

// The upsert serializes concurrent requests for this target.
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
            &format!("UPDATE {table} SET completed=greatest(completed,$2),last_error=NULL WHERE target=$1"),
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
