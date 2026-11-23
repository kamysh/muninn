//! Administration and continuation adapters: one MCP tool per planned wire
//! name from the closed catalog, delegating to the shared core functions.
//! Every handler reports through the same JSON envelope as the CLI adapters.

use std::path::{Path, PathBuf};
use std::sync::Arc;

use anyhow::{anyhow, bail, Context, Result};
use serde_json::{json, Value};
use uuid::Uuid;

use crate::tools::SearchContext;
use muninn_core::{
    db,
    family_policy::{
        self,
        readonly::{self, Operation},
        ApplyRequest, InitialRequest,
    },
    owned_control, store, worktrees,
};

async fn resolve_family(ctx: &SearchContext, repo: &str) -> Result<(Uuid, PathBuf)> {
    let path = Path::new(repo);
    let family = worktrees::registered_family(ctx.client.as_ref(), path)
        .await
        .context("resolve registered family")?
        .ok_or_else(|| anyhow!("repository not registered: {repo}"))?;
    let root = muninn_core::family_policy::runtime::root(
        ctx.client.as_ref(),
        family.id,
        Path::new(&family.path),
    )
    .await?;
    Ok((family.id, root))
}

/// inspect_policy: the current stored policy and effective configuration.
pub async fn inspect_policy(ctx: &SearchContext, repo: &str) -> Result<Value> {
    let (_, root) = resolve_family(ctx, repo).await?;
    let mut client = db::connect(&ctx.config.database).await?;
    readonly::query(&mut client, &root, Operation::Inspect, None)
        .await
        .map_err(|e| anyhow!(e.to_string()))
}

/// check_policy: validate a draft without writing anything.
pub async fn check_policy(ctx: &SearchContext, repo: &str, draft: &Value) -> Result<Value> {
    let (_, root) = resolve_family(ctx, repo).await?;
    let text = serde_json::to_string(draft)?;
    let mut client = db::connect(&ctx.config.database).await?;
    readonly::query(&mut client, &root, Operation::Check, Some(&text))
        .await
        .map_err(|e| anyhow!(e.to_string()))
}

/// apply_policy: apply a validated draft atomically.
pub async fn apply_policy(ctx: &SearchContext, repo: &str, draft: &Value) -> Result<Value> {
    let (_, root) = resolve_family(ctx, repo).await?;
    let text = serde_json::to_string(draft)?;
    let request = ApplyRequest::parse(&text).map_err(|e| anyhow!(e.to_string()))?;
    let mut client = db::connect(&ctx.config.database).await?;
    let data = family_policy::apply_path(&mut client, &root, &request).await?;
    Ok(data)
}

/// preflight_family: creation defaults and advice for an unregistered path.
pub async fn preflight_family(ctx: &SearchContext, repo: &str) -> Result<Value> {
    let mut client = db::connect(&ctx.config.database).await?;
    readonly::query(&mut client, Path::new(repo), Operation::Preflight, None)
        .await
        .map_err(|e| anyhow!(e.to_string()))
}

/// register_family: register with a frozen creation policy.
pub async fn register_family(ctx: &SearchContext, repo: &str, draft: &Value) -> Result<Value> {
    let text = serde_json::to_string(draft)?;
    let input = InitialRequest::parse(&text).map_err(|e| anyhow!(e.to_string()))?;
    let mut client = db::connect(&ctx.config.database).await?;
    let data = family_policy::registration::add_with_creation(
        &mut client,
        || db::connect_for_preparation(&ctx.config.database),
        Path::new(repo),
        Some(&input),
        |_root| {
            let defaults = muninn_core::family_policy::defaults_from_global(&ctx.config)?;
            Ok((input.policy.clone(), defaults))
        },
    )
    .await?;
    Ok(data)
}

/// start_family: authorize indexing for a registered family.
pub async fn start_family(ctx: &SearchContext, repo: &str, draft: &Value) -> Result<Value> {
    let (_, root) = resolve_family(ctx, repo).await?;
    let text = serde_json::to_string(draft)?;
    let request =
        family_policy::start::Request::parse(&text).map_err(|e| anyhow!(e.to_string()))?;
    let mut client = db::connect(&ctx.config.database).await?;
    let view = family_policy::start::authorize(&mut client, &root, &request, &ctx.config).await?;
    Ok(json!({"authorized": true, "family_id": view.family_id, "revision": view.revision}))
}

/// reindex_family: run the foreground index for a registered family.
pub async fn reindex_family(ctx: &SearchContext, repo: &str) -> Result<Value> {
    let (family_id, root) = resolve_family(ctx, repo).await?;
    let mut client = db::connect(&ctx.config.database).await?;
    let (eff, policy) =
        muninn_core::family_policy::runtime::config(&client, family_id, &root, &ctx.config).await?;
    if policy.as_ref().is_some_and(|p| !p.indexing_enabled) {
        bail!("Use start_family for the first index");
    }
    let embedder: Arc<dyn muninn_core::embeddings::EmbeddingBackend> =
        Arc::from(muninn_core::embeddings::make_backend(&eff.embeddings));
    let expected_dim = muninn_core::embeddings::expected_dimension(&eff.embeddings);
    let (outcome, skips) = muninn_core::pipeline::index_repo(
        &mut client,
        family_id,
        &root,
        embedder,
        eff.embeddings.batch_size,
        expected_dim,
        &eff.exclude,
        &eff.vendor,
        |_, _, _| {},
    )
    .await?;
    Ok(json!({"indexed": outcome, "skips": skips.len()}))
}

/// pause_family / resume_family: saved authorization state.
pub async fn pause_family(ctx: &SearchContext, repo: &str) -> Result<Value> {
    let (family_id, _) = resolve_family(ctx, repo).await?;
    let client = ctx.client.as_ref();
    store::set_paused(client, family_id, true).await?;
    Ok(json!({"paused": true, "family_id": family_id}))
}

pub async fn resume_family(ctx: &SearchContext, repo: &str) -> Result<Value> {
    let (family_id, _) = resolve_family(ctx, repo).await?;
    let client = ctx.client.as_ref();
    store::set_paused(client, family_id, false).await?;
    Ok(json!({"paused": false, "family_id": family_id}))
}

/// cancel_work: remove accepted work for one operation; committed results stay.
pub async fn cancel_work(ctx: &SearchContext, repo: &str, operation_id: &str) -> Result<Value> {
    let (family_id, _) = resolve_family(ctx, repo).await?;
    let client = ctx.client.as_ref();
    let schema = store::repo_schema(family_id);
    if let Ok(id) = Uuid::parse_str(operation_id) {
        let id = id.to_string();
        if owned_control::mcp_request_owner(client, &id).await? == Some(Some(family_id)) {
            let removed =
                owned_control::finish_receipt(client, &schema, &id, &json!({"cancelled": true}))
                    .await?;
            return Ok(json!({"cancelled": removed > 0, "removed_rows": removed}));
        }
    }
    let removed = owned_control::cancel_accepted_work(client, &schema, operation_id).await?;
    Ok(json!({"cancelled": removed > 0, "removed_rows": removed}))
}

/// inspect_status: the family's registration, indexing and usage snapshot.
pub async fn inspect_status(ctx: &SearchContext, repo: &str) -> Result<Value> {
    let (_, root) = resolve_family(ctx, repo).await?;
    let mut client = db::connect(&ctx.config.database).await?;
    let data = readonly::query(&mut client, &root, Operation::Inspect, None)
        .await
        .map_err(|e| anyhow!(e.to_string()))?;
    Ok(data)
}

/// unregister_family: retire and clear derived code, preserving authored notes.
pub async fn unregister_family(ctx: &SearchContext, repo: &str) -> Result<Value> {
    let (family_id, _) = resolve_family(ctx, repo).await?;
    let mut client = db::connect(&ctx.config.database).await?;
    store::unregister_repo(&mut client, family_id).await?;
    Ok(json!({"unregistered": true, "family_id": family_id}))
}

/// forget_repository: unregister and delete all owned index data.
pub async fn forget_repository(ctx: &SearchContext, repo: &str) -> Result<Value> {
    let path = Path::new(repo);
    let registered = if path.try_exists()? {
        worktrees::registered_family(ctx.client.as_ref(), path).await?
    } else {
        None
    };
    let family = match registered {
        Some(family) => family,
        None => store::get_repo_by_path_for_removal(ctx.client.as_ref(), repo)
            .await?
            .context("repository family is not registered")?,
    };
    let mut client = db::connect(&ctx.config.database).await?;
    store::forget_repo(&mut client, family.id).await?;
    Ok(json!({"forgotten": true, "family_id": family.id}))
}

/// recreate_index: set a new profile and clear its old derived records.
pub async fn recreate_index(ctx: &SearchContext, repo: &str, draft: &Value) -> Result<Value> {
    let (family_id, _) = resolve_family(ctx, repo).await?;
    let request = serde_json::from_value(draft.clone())?;
    let mut client = db::connect(&ctx.config.database).await?;
    family_policy::recreate_profile(&mut client, family_id, &request).await
}

/// convert_directory preserves the registered family and its checkout identity.
pub async fn convert_directory(ctx: &SearchContext, repo: &str, draft: &Value) -> Result<Value> {
    let (family_id, root) = resolve_family(ctx, repo).await?;
    let request = family_policy::start::Request::parse(&serde_json::to_string(draft)?)
        .map_err(|e| anyhow!(e.to_string()))?;
    let mut client = db::connect(&ctx.config.database).await?;
    family_policy::convert_directory(&mut client, family_id, &root, &request).await
}

/// continue_request: resume the saved work or return the saved result for an
/// operation ID; an ID-only marker explains that the details are gone.
pub async fn continue_request(
    ctx: &SearchContext,
    operation_id: &str,
    message: Option<String>,
) -> Result<Value> {
    let client = ctx.client.as_ref();
    let marker = owned_control::marker_exists(client, operation_id).await?;
    if marker {
        return Ok(json!({
            "resumed": false,
            "guidance": "This request already completed and its details were compacted to the ID. Inspect the current state before deciding whether another operation is needed."
        }));
    }
    if let Some(response) = crate::requests::resume(ctx, operation_id).await? {
        return Ok(response);
    }
    let families = store::list_repos(client).await?;
    for family in families {
        let schema = store::repo_schema(family.id);
        if let Some(receipt) = owned_control::read_receipt(client, &schema, operation_id).await? {
            if receipt.state == "finished" {
                return Ok(json!({"resumed": true, "finished": true, "result": receipt.result}));
            }
            return Ok(json!({
                "resumed": true,
                "finished": false,
                "work": receipt.work,
                "message": message,
                "guidance": "Resuming the saved work."
            }));
        }
    }
    Ok(json!({"resumed": false, "guidance": "No saved work for this operation ID."}))
}
