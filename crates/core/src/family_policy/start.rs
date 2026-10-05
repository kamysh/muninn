//! Explicit first-start authorization. Saving policy never calls this function.
use super::*;
use crate::{config::GlobalConfig, family_store, store};
use serde::{Deserialize, Serialize};
use serde_json::json;
use std::path::Path;
use tokio_postgres::Client;
use uuid::Uuid;

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Request {
    pub api_version: u32,
    pub expected_family_id: Uuid,
    pub expected_revision: u64,
}
impl Request {
    pub fn parse(input: &str) -> Result<Self> {
        let r: Self = serde_json::from_str(input)
            .map_err(|_| PolicyError::new("invalid_request", "invalid start request"))?;
        if r.api_version != 1 || r.expected_revision == 0 || r.expected_revision > MAX_REVISION {
            return Err(PolicyError::new(
                "invalid_request",
                "invalid start version or revision",
            ));
        }
        Ok(r)
    }
}

/// Commits authorization before foreground work. Interrupted work is retryable
/// by the daemon; the returned view is authorization, not indexing completion.
pub async fn authorize(
    client: &mut Client,
    path: &Path,
    request: &Request,
    global: &GlobalConfig,
) -> Result<PolicyView> {
    Request::parse(
        &serde_json::to_string(request)
            .map_err(|_| PolicyError::new("invalid_request", "invalid start request"))?,
    )?;
    let tx = client.transaction().await?;
    family_store::lock_registry(&tx)
        .await
        .map_err(|_| PolicyError::new("database_error", "cannot lock family registry"))?;
    let context = readonly::resolve(&tx, path).await?;
    let view = context
        .view
        .ok_or_else(|| PolicyError::new("not_registered", "register the family before starting"))?;
    if view.family_id != request.expected_family_id {
        return Err(PolicyError::new(
            "family_conflict",
            "selected family changed",
        ));
    }
    if view.revision != request.expected_revision {
        return Err(PolicyError::new(
            "revision_conflict",
            "policy changed; inspect it before starting",
        ));
    }
    let incomplete:bool=tx.query_one("SELECT registration_intent IS NOT NULL AND registration_completed_at IS NULL FROM public.repos WHERE id=$1",&[&view.family_id]).await?.get(0);
    if incomplete {
        return Err(PolicyError::new(
            "registration_incomplete",
            "finish registration before starting",
        ));
    }
    if view.paused || context.checkout["paused"] == true {
        return Err(PolicyError::new(
            "paused",
            "resume the paused family or checkout before starting",
        ));
    }
    if context.checkout["registration_state"] == "suppressed"
        || context.checkout["registration_state"] == "retired"
    {
        return Err(PolicyError::new(
            "inactive_checkout",
            "selected checkout is not active",
        ));
    }
    let cfg = runtime::effective(global, &view);
    if view.policy.embeddings.backend != Backend::Local
        && cfg
            .embeddings
            .api_key
            .as_ref()
            .is_none_or(|k| k.trim().is_empty())
    {
        return Err(PolicyError::new(
            "missing_credentials",
            "configure credentials for the selected embedding backend",
        ));
    }
    tx.execute("UPDATE public.repos SET indexing_enabled_at=now(),indexing_enable_origin='explicit-start' WHERE id=$1 AND indexing_enabled_at IS NULL",&[&view.family_id]).await?;
    let updated = inspect(&tx, view.family_id).await?;
    store::notify_repos_changed(tx.client())
        .await
        .map_err(|_| PolicyError::new("database_error", "cannot notify indexer"))?;
    tx.commit().await?;
    Ok(updated)
}

pub fn receipt(view: &PolicyView, completed: bool, skipped: usize) -> serde_json::Value {
    json!({"family_id":view.family_id,"revision":view.revision,"indexing_enabled":true,"indexing_completed":completed,"skipped_checkouts_or_files":skipped})
}
