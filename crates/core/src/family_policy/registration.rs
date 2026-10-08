//! Explicit registration with durable creation intent. Application templates use
//! Kryzhen via the coordinator; AGE alone owns its separate graph namespace.
use super::{preflight, readonly, store, Defaults, InitialRequest, Policy, PolicyError, Result};
use crate::family_store::{
    self, CheckoutIdentity, Family, GraphRequirement, PreparationConnection,
};
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use std::{future::Future, path::Path};
use tokio_postgres::{Client, GenericClient};

#[derive(Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Intent {
    format_version: u32,
    policy: Policy,
    defaults: Defaults,
}
impl Intent {
    fn decode(value: Value) -> Result<Self> {
        let intent: Self = serde_json::from_value(value).map_err(|_| invalid_intent())?;
        if intent.format_version != 1 {
            return Err(invalid_intent());
        }
        intent.policy.validate().map_err(|_| invalid_intent())?;
        intent.defaults.validate().map_err(|_| invalid_intent())?;
        Ok(intent)
    }
}
fn invalid_intent() -> PolicyError {
    PolicyError::new(
        "invalid_registration_intent",
        "stored creation intent requires diagnosis",
    )
}
fn failure(message: &'static str) -> PolicyError {
    PolicyError::new("registration_error", message)
}
async fn intent(client: &impl GenericClient, family: &Family) -> Result<(Option<Intent>, bool)> {
    let row = client.query_one("SELECT registration_intent, registration_completed_at IS NOT NULL FROM public.repos WHERE id=$1 AND retired_at IS NULL", &[&family.id]).await?;
    let intent = row
        .get::<_, Option<Value>>(0)
        .map(Intent::decode)
        .transpose()?;
    Ok((intent, row.get(1)))
}
struct Reservation {
    family: Family,
    identity: CheckoutIdentity,
    intent: Option<Intent>,
    created: bool,
    recovering: bool,
}

async fn reserve(
    client: &mut Client,
    path: &Path,
    input: Option<&InitialRequest>,
    creation: impl FnOnce(&Path) -> Result<(Policy, Defaults)>,
) -> Result<Reservation> {
    let tx = client.transaction().await?;
    family_store::lock_registry(&tx)
        .await
        .map_err(|_| failure("cannot lock registration"))?;
    let (identity, existing) = readonly::identify(&tx, path).await?;
    let reservation = if let Some(family) = existing {
        let (intent, complete) = intent(&tx, &family).await?;
        if let Some(input) = input {
            if complete || intent.is_none() {
                return Err(PolicyError::new(
                    "policy_already_initialized",
                    "family already exists; use config --apply for policy changes",
                ));
            }
            if intent.as_ref().unwrap().policy != input.policy {
                return Err(PolicyError::new("registration_intent_conflict", "an interrupted add has a different initial policy; retry without input to retain it"));
            }
        }
        Reservation {
            family,
            identity,
            recovering: intent.is_some() && !complete,
            intent,
            created: false,
        }
    } else {
        let root = identity
            .root
            .to_path_buf()
            .map_err(|_| failure("cannot decode checkout root"))?;
        let (default_policy, defaults) = creation(&root)?;
        let policy = input
            .map(|input| input.policy.clone())
            .unwrap_or(default_policy);
        let intent = Intent {
            format_version: 1,
            policy,
            defaults,
        };
        intent.policy.validate()?;
        intent.defaults.validate()?;
        let document = json!(intent);
        let family = family_store::reserve_family_in_tx(
            &tx,
            &identity,
            &root.to_string_lossy(),
            &intent.policy.name,
            intent.policy.embeddings.backend.dimension(),
            Some(&document),
        )
        .await
        .map_err(|_| failure("cannot reserve family; check legacy path ownership and identity"))?;
        Reservation {
            family,
            identity,
            intent: Some(intent),
            created: true,
            recovering: false,
        }
    };
    tx.commit().await?;
    Ok(reservation)
}

/// The injected factory must return an owned, dedicated coordinator connection.
/// No fallback DB, live import, indexing or schema drops are performed here.
pub async fn add<F, Fut>(
    client: &mut Client,
    prepare: F,
    path: &Path,
    input: Option<&InitialRequest>,
) -> Result<Value>
where
    F: Fn() -> Fut,
    Fut: Future<Output = anyhow::Result<PreparationConnection>>,
{
    add_with_creation(client, prepare, path, input, |root| {
        Ok((
            Policy::shipped(
                root.file_name()
                    .unwrap_or(root.as_os_str())
                    .to_string_lossy()
                    .into_owned(),
            ),
            Defaults::shipped(),
        ))
    })
    .await
}

pub async fn add_with_creation<F, Fut>(
    client: &mut Client,
    prepare: F,
    path: &Path,
    input: Option<&InitialRequest>,
    creation: impl FnOnce(&Path) -> Result<(Policy, Defaults)>,
) -> Result<Value>
where
    F: Fn() -> Fut,
    Fut: Future<Output = anyhow::Result<PreparationConnection>>,
{
    if let Some(input) = input {
        input.validate()?;
    }
    // Reject invalid filesystem input before any public preparation commits.
    if !tokio::fs::metadata(path)
        .await
        .map_err(|_| PolicyError::new("invalid_path", "cannot read registration directory"))?
        .is_dir()
    {
        return Err(PolicyError::new(
            "invalid_path",
            "registration path must be a directory",
        ));
    }
    CheckoutIdentity::discover(path)
        .await
        .map_err(|_| PolicyError::new("invalid_path", "cannot discover registration identity"))?;
    prepare()
        .await
        .map_err(|_| failure("cannot open preparation connection"))?
        .prepare_public()
        .await
        .map_err(|_| failure("public preparation failed; committed migrations remain retryable"))?;
    let reservation = reserve(client, path, input, creation).await?;
    let id = reservation.family.id;
    finish(client, &prepare, path, reservation)
        .await
        .map_err(|mut error| {
            // Reservation may already be committed. An error must not imply rollback
            // of prior Kryzhen blocks or authorize deleting the reserved family.
            error.details["family_id"] = json!(id);
            error.details["reservation_persisted"] = json!(true);
            error.details["retry"] =
                json!("retry add without input; no automatic rollback or deletion");
            error
        })
}

async fn finish<F, Fut>(
    client: &mut Client,
    prepare: &F,
    path: &Path,
    reservation: Reservation,
) -> Result<Value>
where
    F: Fn() -> Fut,
    Fut: Future<Output = anyhow::Result<PreparationConnection>>,
{
    let id = reservation.family.id;
    let graph = if reservation.intent.is_some() {
        GraphRequirement::RegistrationIntent
    } else {
        GraphRequirement::Existing
    };
    let prepared = prepare()
        .await
        .map_err(|_| failure("cannot open family preparation connection"))?
        .prepare_family_guarded(id, graph)
        .await
        .map_err(|_| failure("family preparation failed; inspect readiness and retry add"))?;
    // A legacy/bound family without a creation intent must have its own policy;
    // this route must never manufacture defaults for it.
    if reservation.intent.is_none() {
        super::inspect(client, id).await?;
    }
    family_store::register_checkout(client, id, &reservation.identity)
        .await
        .map_err(|_| failure("cannot register checkout; inspect identity and root ownership"))?;
    let tx = client.transaction().await?;
    family_store::lock_registry(&tx)
        .await
        .map_err(|_| failure("cannot lock registration completion"))?;
    let (current_identity, current) = readonly::identify(&tx, path).await?;
    if current.as_ref().map(|f| f.id) != Some(id) || current_identity != reservation.identity {
        return Err(PolicyError::new(
            "family_conflict",
            "registration identity changed before completion",
        ));
    }
    let (stored, complete) = intent(&tx, current.as_ref().unwrap()).await?;
    if let Some(stored) = stored {
        if !complete {
            let request = InitialRequest {
                api_version: 1,
                policy: stored.policy,
            };
            // Initial policy and completion marker commit atomically. Concurrent
            // add retries cannot reset a policy changed after completion.
            store::initialize_locked(&tx, id, &stored.defaults, &request).await?;
            tx.execute("UPDATE public.repos SET registration_completed_at=now() WHERE id=$1 AND registration_completed_at IS NULL", &[&id]).await?;
        }
    }
    let context = readonly::resolve(&tx, path).await?;
    let mut data = context.document();
    let (policy, defaults) = context.policy_and_defaults();
    tx.commit().await?;
    drop(prepared);
    data["family_created"] = json!(reservation.created);
    data["recovered_registration"] = json!(reservation.recovering);
    data["registration_complete"] = json!(true);
    data["reconciliation_scheduled"] = json!(false);
    // A post-commit inventory failure is a diagnostic on a successful receipt,
    // never a claim that registration rolled back.
    let report = tokio::task::spawn_blocking(move || {
        preflight::scan(
            &context.root,
            &policy,
            &defaults,
            preflight::Budget::default(),
        )
    })
    .await;
    match report {
        Ok(Ok(report)) => data["preflight"] = json!(report),
        Ok(Err(error)) => data["preflight_error"] = json!(error),
        Err(_) => {
            data["preflight_error"] = json!(failure("post-registration inventory worker failed"))
        }
    }
    Ok(data)
}
