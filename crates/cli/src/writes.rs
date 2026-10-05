//! Explicit JSON writes; dispatched separately from legacy migration startup.
use crate::readonly::{enrich_credentials, error};
use muninn_core::{
    config::GlobalConfig,
    db,
    family_policy::{self as policy, ApplyRequest},
};
use serde_json::Value;
use std::{io::Read, path::Path};

pub async fn apply(path: &Path) -> policy::Result<Value> {
    let mut input = String::new();
    std::io::stdin()
        .read_to_string(&mut input)
        .map_err(|_| error("invalid_request", "cannot read UTF-8 JSON from stdin"))?;
    // Validate before opening a DB connection. Never echo rejected documents.
    let request = ApplyRequest::parse(&input)?;
    let cfg = GlobalConfig::load().map_err(|_| {
        error(
            "bootstrap_config_error",
            "cannot load global Muninn connection configuration",
        )
    })?;
    let mut client = db::connect(&cfg.database).await.map_err(|_| {
        error(
            "database_error",
            "cannot connect using global Muninn configuration",
        )
    })?;
    let mut data = policy::apply_path(&mut client, path, &request).await?;
    enrich_credentials(&mut data, &cfg, false)?;
    Ok(data)
}

pub async fn add(path: &Path, with_input: bool) -> policy::Result<Value> {
    let input = if with_input {
        let mut input = String::new();
        std::io::stdin()
            .read_to_string(&mut input)
            .map_err(|_| error("invalid_request", "cannot read UTF-8 JSON from stdin"))?;
        Some(policy::InitialRequest::parse(&input)?)
    } else {
        None
    };
    let cfg = GlobalConfig::load().map_err(|_| {
        error(
            "bootstrap_config_error",
            "cannot load global Muninn connection configuration",
        )
    })?;
    let mut client = db::connect(&cfg.database).await.map_err(|_| {
        error(
            "database_error",
            "cannot connect using global Muninn configuration",
        )
    })?;
    let mut data = policy::registration::add(
        &mut client,
        || db::connect_for_preparation(&cfg.database),
        path,
        input.as_ref(),
    )
    .await?;
    enrich_credentials(&mut data, &cfg, false)?;
    Ok(data)
}

pub async fn start(path: &Path, input: bool) -> policy::Result<Value> {
    let request = if input {
        let mut text = String::new();
        std::io::stdin()
            .read_to_string(&mut text)
            .map_err(|_| error("invalid_request", "cannot read start request"))?;
        Some(policy::start::Request::parse(&text)?)
    } else {
        None
    };
    let cfg = GlobalConfig::load()
        .map_err(|_| error("bootstrap_config_error", "cannot load global configuration"))?;
    let mut client = db::connect(&cfg.database)
        .await
        .map_err(|_| error("database_error", "cannot connect to database"))?;
    let request = match request {
        Some(r) => r,
        None => {
            let context = policy::readonly::resolve(&client, path).await?;
            let view = context
                .view
                .ok_or_else(|| error("not_registered", "register this family first"))?;
            policy::start::Request {
                api_version: 1,
                expected_family_id: view.family_id,
                expected_revision: view.revision,
            }
        }
    };
    start_configured(&mut client, &cfg, path, &request).await
}

pub async fn start_configured(
    client: &mut tokio_postgres::Client,
    cfg: &GlobalConfig,
    path: &Path,
    request: &policy::start::Request,
) -> policy::Result<Value> {
    use muninn_core::{embeddings, pipeline, store};
    // Reject a stale/wrong family before requesting preemption. Authorization
    // rechecks these guards under the registry lock after the job lock is held.
    let selected = policy::readonly::resolve(client, path).await?;
    let view = selected
        .view
        .ok_or_else(|| error("not_registered", "register the family before starting"))?;
    if view.family_id != request.expected_family_id {
        return Err(error("family_conflict", "selected family changed"));
    }
    if view.revision != request.expected_revision {
        return Err(error(
            "revision_conflict",
            "policy changed; inspect it before starting",
        ));
    }
    // Foreground job lock is acquired before enabling daemon retries.
    let lock = match store::try_lock(&cfg.database, request.expected_family_id)
        .await
        .map_err(|_| error("database_error", "cannot acquire indexing lock"))?
    {
        Some(c) => c,
        None => {
            store::request_preempt(client, request.expected_family_id)
                .await
                .map_err(|_| error("database_error", "cannot request foreground indexing"))?;
            store::lock_blocking(&cfg.database, request.expected_family_id)
                .await
                .map_err(|_| error("database_error", "cannot acquire indexing lock"))?
        }
    };
    // Clear our wait signal even if the following authorization recheck fails.
    store::clear_preempt(&lock, request.expected_family_id)
        .await
        .map_err(|_| error("database_error", "cannot clear foreground request"))?;
    let view = policy::start::authorize(client, path, request, cfg).await?;
    let context = policy::readonly::resolve(client, path).await?;
    let eff = policy::runtime::effective(cfg, &view);
    store::mark_unindexed(client, view.family_id)
        .await
        .map_err(|_| error("database_error", "cannot schedule indexing"))?;
    let backend = std::sync::Arc::from(embeddings::make_backend(&eff.embeddings));
    let result = pipeline::index_repo(
        client,
        view.family_id,
        &context.root,
        backend,
        eff.embeddings.batch_size,
        view.dimension as usize,
        &eff.exclude,
        &eff.vendor,
        |_, _, _| {},
    )
    .await;
    let _ = store::unlock(&lock, view.family_id).await;
    let _ = store::notify_repos_changed(client).await;
    match result {
        Ok((_, skips)) => Ok(policy::start::receipt(&view, skips.is_empty(), skips.len())),
        Err(_) => {
            let mut e=error("indexing_incomplete","Indexing was enabled but this pass failed; inspect the indexer log or retry muninn start PATH. Previous completed views are retained.");
            e.details = serde_json::json!({"family_id":view.family_id,"indexing_enabled":true,"indexing_completed":false});
            Err(e)
        }
    }
}
