//! Recoverable searches persist the resolved intent before starting index work.
use crate::tools::{self, SearchContext, SearchParams};
use anyhow::{bail, ensure, Context, Result};
use muninn_core::{db, family_store, knowledge, owned_control, repo_resolver, store, worktrees};
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use std::path::{Path, PathBuf};
use uuid::Uuid;

#[derive(Deserialize, Serialize)]
struct Intent {
    tool: String,
    args: Value,
    git_dir: Option<PathBuf>,
}

async fn target(ctx: &SearchContext, args: &Value) -> Result<(Uuid, PathBuf, Option<PathBuf>)> {
    let locator = args["repo"]
        .as_str()
        .or_else(|| args["cwd"].as_str())
        .context("provide repo or cwd for a recoverable search")?;
    let path = Path::new(locator);
    if let Some(git) = repo_resolver::discover_git_checkout(path).await? {
        let family = worktrees::registered_family(&ctx.client, &git.root)
            .await?
            .context("repository family is not registered")?;
        return Ok((family.id, git.root, Some(git.git_dir)));
    }
    let repo = tools::resolve_repo(
        &ctx.client,
        &SearchParams {
            query: String::new(),
            repo: Some(locator.to_owned()),
            cwd: None,
            limit: None,
            exact: None,
        },
    )
    .await?;
    Ok((repo.id, PathBuf::from(repo.path), None))
}

pub async fn search(ctx: &SearchContext, tool: &str, args: Value) -> Result<Value> {
    let Some(id) = args.get("operation_id") else {
        return execute(ctx, tool, args).await;
    };
    let id = id
        .as_str()
        .context("operation_id must be a UUID")?
        .to_owned();
    start(ctx, tool, &id, args).await
}

pub(super) async fn start(
    ctx: &SearchContext,
    tool: &str,
    id: &str,
    mut args: Value,
) -> Result<Value> {
    let id = Uuid::parse_str(id)?.to_string();
    let (family, root, git_dir) = target(ctx, &args).await?;
    args["repo"] = serde_json::to_value(root)?;
    let fields = args
        .as_object_mut()
        .context("search arguments must be an object")?;
    fields.remove("operation_id");
    fields.remove("cwd");
    let intent = serde_json::to_value(Intent {
        tool: tool.to_owned(),
        args,
        git_dir,
    })?;
    let mut client =
        db::connect_with_app_name(&ctx.config.database, "muninn-mcp-search-receipt").await?;
    let schema = store::repo_schema(family);
    let receipt_table = format!("{schema}.receipts");
    if !client
        .query_one("SELECT to_regclass($1) IS NOT NULL", &[&receipt_table])
        .await?
        .get::<_, bool>(0)
    {
        db::run_repo_migrations(&mut client, &schema).await?;
    }
    let tx = client.transaction().await?;
    ensure!(
        !owned_control::marker_exists(&tx, &id).await?,
        "operation ID already used"
    );
    if owned_control::claim_mcp_request(&tx, &id, family).await? {
        owned_control::accept_receipt(&tx, &schema, &id, &intent, &json!({})).await?;
    } else {
        ensure!(
            owned_control::mcp_request_owner(&tx, &id).await? == Some(Some(family)),
            "operation ID already used"
        );
        let receipt = owned_control::read_receipt(&tx, &schema, &id)
            .await?
            .context("saved search receipt unavailable")?;
        ensure!(
            receipt.input.as_ref() == Some(&intent),
            "operation ID already bound to a different request"
        );
    }
    tx.commit().await?;
    let result = complete(ctx, family, &id).await.with_context(|| {
        format!(
            "request {id} remains recoverable with continue_request if its checkout is available"
        )
    })?;
    Ok(result)
}

/// An unowned ID may belong to another kind of operation.
pub async fn resume(ctx: &SearchContext, id: &str) -> Result<Option<Value>> {
    let Ok(id) = Uuid::parse_str(id) else {
        return Ok(None);
    };
    let id = id.to_string();
    let Some(owner) = owned_control::mcp_request_owner(ctx.client.as_ref(), &id).await? else {
        return Ok(None);
    };
    let Some(family) = owner else {
        return Ok(Some(
            json!({"resumed": false, "guidance": "The request family was removed and the operation ID has been retained."}),
        ));
    };
    let result = complete(ctx, family, &id).await?;
    Ok(Some(
        json!({"resumed": true, "finished": true, "result": result}),
    ))
}

async fn complete(ctx: &SearchContext, family: Uuid, id: &str) -> Result<Value> {
    let client = ctx.client.as_ref();
    let schema = store::repo_schema(family);
    let registration = family_store::get_family(client, family)
        .await?
        .context("search family removed")?;
    ensure!(registration.retired_at.is_none(), "search family retired");
    let receipt = owned_control::read_receipt(client, &schema, id)
        .await?
        .context("saved search receipt unavailable")?;
    if receipt.state == "finished" {
        return receipt.result.context("finished search has no result");
    }
    let intent: Intent =
        serde_json::from_value(receipt.input.context("saved search missing intent")?)?;
    let (current_family, current_root, git_dir) = target(ctx, &intent.args).await?;
    ensure!(
        family == current_family
            && git_dir == intent.git_dir
            && current_root.as_os_str()
                == intent.args["repo"]
                    .as_str()
                    .context("saved search missing root")?,
        "the saved search checkout is no longer at its recorded location"
    );
    if matches!(
        intent.tool.as_str(),
        "record_knowledge" | "delete_knowledge"
    ) {
        return complete_note(ctx, family, id, &schema, intent).await;
    }
    let result = execute(ctx, &intent.tool, intent.args).await?;
    if owned_control::finish_receipt(client, &schema, id, &result).await? == 1 {
        return Ok(result);
    }
    owned_control::read_receipt(client, &schema, id)
        .await?
        .and_then(|receipt| receipt.result)
        .context("search receipt changed while completing")
}

enum NoteAction {
    Write(Box<tools::PreparedNote>),
    Delete(knowledge::NoteLocation, Uuid),
}

async fn complete_note(
    ctx: &SearchContext,
    family: Uuid,
    id: &str,
    schema: &str,
    intent: Intent,
) -> Result<Value> {
    // Providers run before the row lock. At most one mutation and receipt
    // commit, even when two connections prepare the same intent.
    let action = if intent.tool == "record_knowledge" {
        let prepared = tools::prepare_note(ctx, serde_json::from_value(intent.args)?).await?;
        ensure!(
            prepared.location.family_id == Some(family),
            "note family has no scoped policy"
        );
        NoteAction::Write(Box::new(prepared))
    } else {
        let params: tools::DeleteKnowledgeParams = serde_json::from_value(intent.args)?;
        let repo = params
            .repo
            .context("repository required to continue a note deletion")?;
        let location = knowledge::NoteLocation::resolve(&ctx.client, &repo).await?;
        ensure!(
            location.family_id == Some(family),
            "note family has no scoped policy"
        );
        NoteAction::Delete(location, Uuid::parse_str(&params.id)?)
    };
    let mut writer =
        db::connect_with_app_name(&ctx.config.database, "muninn-mcp-note-receipt").await?;
    let tx = writer.transaction().await?;
    tx.query_one(
        "SELECT id FROM public.repos WHERE id=$1 AND retired_at IS NULL FOR KEY SHARE",
        &[&family],
    )
    .await?;
    let receipt = owned_control::lock_receipt(&tx, schema, id)
        .await?
        .context("saved note request unavailable")?;
    if receipt.state == "finished" {
        return receipt
            .result
            .context("finished note request has no result");
    }
    let result = match action {
        NoteAction::Write(prepared) => {
            serde_json::to_value(tools::write_note(&tx, *prepared).await?)?
        }
        NoteAction::Delete(location, id) => {
            json!({"deleted": knowledge::delete_scoped(&tx, &location, id).await?})
        }
    };
    ensure!(owned_control::finish_receipt(&tx, schema, id, &result).await? == 1);
    tx.commit().await?;
    Ok(result)
}

async fn execute(ctx: &SearchContext, tool: &str, args: Value) -> Result<Value> {
    let result = match tool {
        "search_hybrid" => tools::search_hybrid(ctx, serde_json::from_value(args)?).await?,
        "search_fulltext" => tools::search_fulltext(ctx, serde_json::from_value(args)?).await?,
        "search_semantic" => tools::search_semantic(ctx, serde_json::from_value(args)?).await?,
        "search_structural" => {
            return tools::search_structural(ctx, serde_json::from_value(args)?).await
        }
        _ => bail!("unknown search: {tool}"),
    };
    Ok(serde_json::to_value(result)?)
}
