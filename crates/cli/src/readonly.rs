//! Early-dispatched family reads. All DB work is in a read-only transaction;
//! this module has no registration, migration or policy-write calls.
use muninn_core::{
    config::{EmbeddingBackend, GlobalConfig},
    db,
    family_policy::{self as policy, readonly, Backend, Policy, PolicyError},
};
pub use readonly::Operation as Mode;
use serde_json::{json, Value};
use std::{io::Read, path::Path};
pub fn error(code: &'static str, message: &'static str) -> PolicyError {
    PolicyError {
        code,
        message,
        details: json!({}),
    }
}
pub fn exit_code(error: &PolicyError) -> i32 {
    match error.code {
        "invalid_request" | "invalid_policy" | "invalid_path" => 2,
        "family_conflict"
        | "revision_conflict"
        | "registration_intent_conflict"
        | "policy_already_initialized" => 3,
        "schema_not_ready"
        | "not_registered"
        | "policy_not_initialized"
        | "legacy_identity_unresolved"
        | "dimension_migration_required"
        | "profile_change_not_supported" => 4,
        "registration_incomplete" | "reindex_required" | "revision_exhausted" => 4,
        _ => 1,
    }
}
pub fn finish(result: policy::Result<Value>) -> ! {
    let (code, response) = match result {
        Ok(data) => (0, policy::success(data)),
        Err(error) => (exit_code(&error), policy::failure(&error)),
    };
    println!("{response}");
    std::process::exit(code);
}
fn credential_availability(cfg: &GlobalConfig, candidate: &Policy) -> &'static str {
    let matches = matches!(
        (&cfg.embeddings.backend, candidate.embeddings.backend),
        (EmbeddingBackend::Voyage, Backend::Voyage) | (EmbeddingBackend::OpenAI, Backend::OpenAI)
    );
    if candidate.embeddings.backend == Backend::Local {
        "not_required"
    } else if matches
        && cfg
            .embeddings
            .api_key
            .as_ref()
            .is_some_and(|key| !key.trim().is_empty())
    {
        "configured_not_verified"
    } else {
        "missing_for_selected_backend"
    }
}

pub async fn run(path: &Path, mode: Mode) -> policy::Result<Value> {
    let input = if mode == Mode::Check {
        let mut input = String::new();
        std::io::stdin()
            .read_to_string(&mut input)
            .map_err(|_| error("invalid_request", "cannot read UTF-8 JSON from stdin"))?;
        Some(input)
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
    let mut data = readonly::query(&mut client, path, mode, input.as_deref()).await?;
    enrich_credentials(&mut data, &cfg, mode == Mode::Check)?;
    Ok(data)
}

pub(super) fn enrich_credentials(
    data: &mut Value,
    cfg: &GlobalConfig,
    candidate: bool,
) -> policy::Result<()> {
    let selected: Policy = serde_json::from_value(if candidate {
        data["candidate"]["policy"].clone()
    } else {
        data["policy"].clone()
    })
    .map_err(|_| error("invalid_stored_policy", "cannot decode policy response"))?;
    data["capabilities"]["credential_availability"] =
        json!(credential_availability(cfg, &selected));
    data["capabilities"]["credential_scope"] = json!(if candidate {
        "candidate_policy"
    } else {
        "policy"
    });
    Ok(())
}
