//! Read-only path resolution. No schema preparation, registration or fallback
//! to legacy TOML. Call inside a read-only repeatable-read transaction.
use super::{preflight::ReportPath, *};
use crate::family_store::{
    self, CheckoutIdentity, FamilyIdentity, FamilyKind, SchemaState, StoredPath,
};
use serde_json::{json, Value};
use std::path::{Path, PathBuf};
use tokio_postgres::GenericClient;

pub struct Context {
    pub root: PathBuf,
    pub view: Option<PolicyView>,
    pub checkout: Value,
    pub kind: &'static str,
}
fn lookup_error() -> PolicyError {
    PolicyError::new("database_error", "cannot resolve registered family")
}
fn identity_error() -> PolicyError {
    PolicyError::new("invalid_path", "cannot discover directory identity")
}

/// Refuse an unmigrated registry rather than performing read-time migration.
async fn registry_ready(client: &impl GenericClient) -> Result<()> {
    let ready: bool = client.query_one(
        "SELECT count(*) = 10 FROM information_schema.columns WHERE table_schema='public' AND table_name='repos' AND column_name = ANY($1)",
        &[&vec!["family_kind", "path_encoding", "family_key", "retired_at", "schema_state", "schema_error", "storage_generation", "indexing_enabled_at", "indexing_enable_origin", "embedding_dim"]],
    ).await?.get(0);
    if !ready {
        return Err(PolicyError::new(
            "schema_not_ready",
            "family registry requires separately authorized preparation; no migration was run",
        ));
    }
    Ok(())
}

pub async fn resolve(client: &impl GenericClient, path: &Path) -> Result<Context> {
    let (identity, family) = identify(client, path).await?;
    context(client, identity, family).await
}

/// Resolve identity without requiring prepared family tables. Registration uses
/// this under the registry lock so nearest-ancestor ownership cannot race.
pub(crate) async fn identify(
    client: &impl GenericClient,
    path: &Path,
) -> Result<(CheckoutIdentity, Option<family_store::Family>)> {
    registry_ready(client).await?;
    if !tokio::fs::metadata(path)
        .await
        .map_err(|_| identity_error())?
        .is_dir()
    {
        return Err(identity_error());
    }
    let mut identity = CheckoutIdentity::discover(path)
        .await
        .map_err(|_| identity_error())?;
    let mut family = family_store::lookup_family(client, &identity.family)
        .await
        .map_err(|_| lookup_error())?;
    // For plain directories, the nearest registered ancestor owns the context.
    // Git discovery already resolves a nested path to its checkout root.
    if family.is_none() && identity.family.kind == FamilyKind::Directory {
        let root = identity.root.to_path_buf().map_err(|_| identity_error())?;
        for ancestor in root.ancestors().skip(1) {
            let key = StoredPath::canonicalize(ancestor)
                .await
                .map_err(|_| identity_error())?;
            let candidate = FamilyIdentity {
                kind: FamilyKind::Directory,
                key: key.clone(),
            };
            if let Some(found) = family_store::lookup_family(client, &candidate)
                .await
                .map_err(|_| lookup_error())?
            {
                identity.family = candidate;
                identity.root = key;
                family = Some(found);
                break;
            }
        }
    }
    if family.is_none() {
        // Unimported legacy paths cannot establish a new-family identity. Check
        // known live locators without adopting their rows or reading their TOML.
        // An inaccessible locator leaves identity uncertain, so fail closed.
        for row in client
            .query(
                "SELECT path FROM public.repos WHERE family_key IS NULL AND retired_at IS NULL",
                &[],
            )
            .await?
        {
            let legacy_path: String = row.get(0);
            let legacy = CheckoutIdentity::discover(Path::new(&legacy_path)).await.map_err(|_| PolicyError::new("legacy_identity_unresolved", "an unimported registration cannot be identified; review legacy registrations before using creation defaults"))?;
            let legacy_root = legacy.root.to_path_buf().map_err(|_| identity_error())?;
            let root = identity.root.to_path_buf().map_err(|_| identity_error())?;
            if legacy.family == identity.family
                || (legacy.family.kind == FamilyKind::Directory && root.starts_with(&legacy_root))
            {
                return Err(PolicyError::new("policy_not_initialized", "matching legacy registration requires explicit policy import; no defaults substituted"));
            }
        }
    }
    Ok((identity, family))
}

async fn context(
    client: &impl GenericClient,
    identity: CheckoutIdentity,
    family: Option<family_store::Family>,
) -> Result<Context> {
    let root = identity.root.to_path_buf().map_err(|_| identity_error())?;
    let mut checkout = json!({"root":ReportPath::new(&root), "checkout_id":null, "registration_state":"unregistered", "paused":null});
    let view = if let Some(family) = family {
        if family.schema_state != SchemaState::Ready {
            return Err(PolicyError::new(
                "schema_not_ready",
                "family schema pair is not ready",
            ));
        }
        // Check the tables before using the typed service; never bootstrap them.
        let schema = crate::store::repo_schema(family.id);
        for table in [
            "checkouts",
            "family_policy",
            "policy_versions",
            "policy_defaults",
        ] {
            let exists: bool = client
                .query_one(
                    "SELECT to_regclass($1) IS NOT NULL",
                    &[&format!("{schema}.{table}")],
                )
                .await?
                .get(0);
            if !exists {
                return Err(PolicyError::new(
                    "schema_not_ready",
                    "family policy tables require separately authorized preparation",
                ));
            }
        }
        let view = inspect(client, family.id).await?;
        if let Some(resolved) = family_store::lookup_checkout(client, family.id, &identity.root)
            .await
            .map_err(|_| lookup_error())?
        {
            checkout["checkout_id"] = json!(resolved.checkout.token.id);
            checkout["registration_state"] = json!(resolved.checkout.registration_state.as_str());
            checkout["paused"] = json!(resolved.checkout.paused);
        }
        Some(view)
    } else {
        None
    };
    Ok(Context {
        root,
        view,
        checkout,
        kind: identity.family.kind.as_str(),
    })
}

impl Context {
    /// Materialize creation defaults only after successful registry resolution.
    pub fn policy_and_defaults(&self) -> (Policy, Defaults) {
        match &self.view {
            Some(view) => (view.policy.clone(), view.defaults.clone()),
            None => (
                Policy::shipped(
                    self.root
                        .file_name()
                        .unwrap_or(self.root.as_os_str())
                        .to_string_lossy()
                        .into_owned(),
                ),
                Defaults::shipped(),
            ),
        }
    }
    pub fn document(&self) -> Value {
        let mut data = match &self.view {
            Some(view) => serde_json::to_value(view).expect("typed policy view serializes"),
            None => {
                let (policy, defaults) = self.policy_and_defaults();
                json!({"family_id":null,"revision":null,"defaults_revision":defaults.revision,
                    "effective_policy":policy.effective(&defaults),"effective_rules":EffectiveRules::resolve(&policy,&defaults),
                    "dimension":policy.embeddings.backend.dimension(),"policy":policy,"defaults":defaults,
                    "indexing_enabled":false,"paused":false,"schema_state":"unregistered","capabilities":capabilities()})
            }
        };
        data["checkout_id"] = self.checkout["checkout_id"].clone();
        data["checkout"] = self.checkout.clone();
        data["family_kind"] = json!(self.kind);
        data["policy_source"] = json!(if self.view.is_some() {
            "stored"
        } else {
            "creation_defaults"
        });
        data["capabilities"]["command_operations"] =
            json!(["inspect", "check", "preflight", "add", "apply"]);
        data
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Operation {
    Inspect,
    Check,
    Preflight,
}

/// Shared command service: one read-only, repeatable snapshot for resolution and
/// candidate guards, released before scanning. No call path prepares or writes.
pub async fn query(
    client: &mut tokio_postgres::Client,
    path: &Path,
    operation: Operation,
    input: Option<&str>,
) -> Result<Value> {
    query_with_creation(client, path, operation, input, |root| {
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

pub async fn query_with_creation(
    client: &mut tokio_postgres::Client,
    path: &Path,
    operation: Operation,
    input: Option<&str>,
    creation: impl FnOnce(&Path) -> Result<(Policy, Defaults)>,
) -> Result<Value> {
    let tx = client
        .build_transaction()
        .isolation_level(tokio_postgres::IsolationLevel::RepeatableRead)
        .read_only(true)
        .start()
        .await?;
    tx.batch_execute("SET LOCAL statement_timeout='5s'; SET LOCAL lock_timeout='1s'")
        .await?;
    let context = resolve(&tx, path).await?;
    if operation == Operation::Inspect && context.view.is_none() {
        return Err(PolicyError::new(
            "not_registered",
            "directory has no registered family; use preflight to inspect creation defaults",
        ));
    }
    let mut data = context.document();
    let (mut selected, defaults) = if context.view.is_some() {
        context.policy_and_defaults()
    } else {
        let (policy, defaults) = creation(&context.root)?;
        policy.validate()?;
        defaults.validate()?;
        data["policy"] = json!(policy);
        data["defaults"] = json!(defaults);
        data["defaults_revision"] = json!(defaults.revision);
        data["effective_policy"] = json!(policy.effective(&defaults));
        data["effective_rules"] = json!(EffectiveRules::resolve(&policy, &defaults));
        data["dimension"] = json!(policy.embeddings.backend.dimension());
        (policy, defaults)
    };
    if operation == Operation::Check {
        let input = input
            .ok_or_else(|| PolicyError::new("invalid_request", "candidate JSON is required"))?;
        let candidate = if let Some(view) = &context.view {
            let request = ApplyRequest::parse(input)?;
            let result = validate_candidate(&tx, view.family_id, &request).await?;
            selected = request.policy;
            json!(result)
        } else {
            selected = InitialRequest::parse(input)?.policy;
            json!({"family_id":null,"revision":null,"changed":null,"impact":"initial_policy",
                "requires_reindex_acknowledgement":false,"apply_supported":false,
                "registration_required":true})
        };
        data["candidate"] = json!({"policy":selected,"effective_policy":selected.effective(&defaults),
            "effective_rules":EffectiveRules::resolve(&selected,&defaults),"validation":candidate});
    }
    tx.rollback().await?;
    if operation != Operation::Inspect {
        let root = context.root;
        let report = tokio::task::spawn_blocking(move || {
            preflight::scan(&root, &selected, &defaults, preflight::Budget::default())
        })
        .await
        .map_err(|_| PolicyError::new("inventory_error", "inventory worker failed"))??;
        data["preflight"] = json!(report);
    }
    Ok(data)
}
