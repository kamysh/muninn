use super::*;
use crate::family_store::{self, Family, SchemaState};
use serde_json::{json, Value};
use tokio_postgres::{Client, GenericClient};
use uuid::Uuid;

fn schema(id: Uuid) -> String {
    format!("\"{}\"", crate::store::repo_schema(id))
}
fn invalid_storage() -> PolicyError {
    PolicyError::new(
        "invalid_stored_policy",
        "stored policy cannot be decoded or validated",
    )
}
async fn family(client: &impl GenericClient, id: Uuid) -> Result<Family> {
    let family = family_store::get_family(client, id)
        .await
        .map_err(|_| PolicyError::new("database_error", "cannot read family registry"))?
        .ok_or_else(|| PolicyError::new("not_registered", "family is not registered"))?;
    if family.retired_at.is_some() {
        return Err(PolicyError::new("not_registered", "family is retired"));
    }
    if family.schema_state != SchemaState::Ready || family.identity.is_none() {
        return Err(PolicyError::new(
            "schema_not_ready",
            "family schema pair is not ready",
        ));
    }
    Ok(family)
}
async fn read(client: &impl GenericClient, family: &Family) -> Result<Option<PolicyView>> {
    let schema = schema(family.id);
    let row=client.query_opt(&format!("SELECT v.revision,v.policy,d.document FROM {schema}.family_policy c JOIN {schema}.policy_versions v ON v.revision=c.current_revision JOIN {schema}.policy_defaults d ON d.revision=v.defaults_revision WHERE c.singleton AND EXISTS(SELECT 1 FROM public.repos WHERE id=$1 AND retired_at IS NULL AND schema_state='ready')"),&[&family.id]).await?;
    row.map(|row| {
        let revision: i64 = row.try_get(0)?;
        if !(1..=MAX_REVISION as i64).contains(&revision) {
            return Err(invalid_storage());
        }
        let policy: Policy =
            serde_json::from_value(row.try_get::<_, Value>(1)?).map_err(|_| invalid_storage())?;
        let defaults: Defaults =
            serde_json::from_value(row.try_get::<_, Value>(2)?).map_err(|_| invalid_storage())?;
        policy.validate().map_err(|_| invalid_storage())?;
        defaults.validate().map_err(|_| invalid_storage())?;
        check_dimension(&policy, family)?;
        Ok(PolicyView {
            family_id: family.id,
            revision: revision as u64,
            defaults_revision: defaults.revision.clone(),
            effective_policy: policy.effective(&defaults),
            effective_rules: EffectiveRules::resolve(&policy, &defaults),
            policy,
            defaults,
            dimension: family.embedding_dim,
            indexing_enabled: family.indexing_enabled_at.is_some(),
            paused: family.paused,
            schema_state: "ready",
            capabilities: capabilities(),
        })
    })
    .transpose()
}
fn check_dimension(policy: &Policy, family: &Family) -> Result<()> {
    if policy.embeddings.backend.dimension() != family.embedding_dim {
        Err(PolicyError::new(
            "dimension_migration_required",
            "embedding selection differs from the registered dimension",
        ))
    } else {
        Ok(())
    }
}
async fn lock(tx: &tokio_postgres::Transaction<'_>) -> Result<()> {
    family_store::lock_registry(tx)
        .await
        .map_err(|_| PolicyError::new("database_error", "cannot acquire registry lock"))
}
fn guards(view: &PolicyView, request: &ApplyRequest) -> Result<()> {
    if request.expected_family_id != view.family_id {
        return Err(PolicyError {
            code: "family_conflict",
            message: "path or target resolves to a different family",
            details: json!({"family_id":view.family_id,"revision":view.revision}),
        });
    }
    if request.expected_revision != view.revision {
        return Err(PolicyError {
            code: "revision_conflict",
            message: "policy revision has changed",
            details: json!({"family_id":view.family_id,"revision":view.revision}),
        });
    }
    Ok(())
}
fn changed(view: &PolicyView, request: &ApplyRequest) -> Option<Impact> {
    (view.policy != request.policy).then(|| view.policy.impact(&request.policy))
}
async fn wake(tx: &tokio_postgres::Transaction<'_>, id: Uuid) -> Result<()> {
    tx.execute(
        "SELECT pg_notify('muninn_family_policy_changed',$1)",
        &[&id.to_string()],
    )
    .await?;
    Ok(())
}

/// Explicit initialization after schema preparation, never a read-time fallback.
pub async fn initialize(
    client: &mut Client,
    id: Uuid,
    defaults: &Defaults,
    request: &InitialRequest,
) -> Result<PolicyView> {
    request.validate()?;
    defaults.validate()?;
    let tx = client.transaction().await?;
    lock(&tx).await?;
    let view = initialize_locked(&tx, id, defaults, request).await?;
    tx.commit().await?;
    Ok(view)
}

pub(super) async fn initialize_locked(
    tx: &tokio_postgres::Transaction<'_>,
    id: Uuid,
    defaults: &Defaults,
    request: &InitialRequest,
) -> Result<PolicyView> {
    request.validate()?;
    defaults.validate()?;
    let family = family(tx, id).await?;
    check_dimension(&request.policy, &family)?;
    if let Some(view) = read(tx, &family).await? {
        if view.policy != request.policy || view.defaults != *defaults {
            return Err(PolicyError::new(
                "policy_already_initialized",
                "family already has a different initial policy",
            ));
        }
        return Ok(view);
    }
    let schema = schema(id);
    let document = serde_json::to_value(defaults).map_err(|_| invalid_storage())?;
    // An existing defaults ID must describe the same immutable document.
    tx.execute(&format!("INSERT INTO {schema}.policy_defaults(revision,format_version,document) VALUES($1,1,$2) ON CONFLICT(revision) DO NOTHING"),&[&defaults.revision,&document]).await?;
    if tx
        .query_one(
            &format!("SELECT document FROM {schema}.policy_defaults WHERE revision=$1"),
            &[&defaults.revision],
        )
        .await?
        .get::<_, Value>(0)
        != document
    {
        return Err(PolicyError::new(
            "defaults_conflict",
            "defaults revision already describes different rules",
        ));
    }
    let policy = serde_json::to_value(&request.policy).map_err(|_| invalid_storage())?;
    tx.execute(&format!("INSERT INTO {schema}.policy_versions(revision,format_version,defaults_revision,policy) VALUES(1,1,$1,$2)"),&[&defaults.revision,&policy]).await?;
    tx.execute(
        &format!("INSERT INTO {schema}.family_policy(singleton,current_revision) VALUES(true,1)"),
        &[],
    )
    .await?;
    let view = read(tx, &family).await?.ok_or_else(invalid_storage)?;
    wake(tx, id).await?;
    Ok(view)
}

/// Read-only. Never initializes policy, migrates schemas or loads local secrets.
pub async fn inspect(client: &impl GenericClient, id: Uuid) -> Result<PolicyView> {
    let family = family(client, id).await?;
    read(client, &family).await?.ok_or_else(|| {
        PolicyError::new(
            "policy_not_initialized",
            "family policy has not been initialized",
        )
    })
}

/// No preflight yet: this primitive only validates stored-policy compatibility.
pub async fn validate_candidate(
    client: &impl GenericClient,
    id: Uuid,
    request: &ApplyRequest,
) -> Result<CandidateResult> {
    request.validate()?;
    let view = inspect(client, id).await?;
    guards(&view, request)?;
    let impact = changed(&view, request);
    Ok(CandidateResult {
        family_id: id,
        revision: view.revision,
        changed: impact.is_some(),
        impact,
        requires_reindex_acknowledgement: view.indexing_enabled
            && impact == Some(Impact::EmbeddingProfile)
            && !request.acknowledge_reindex,
        apply_supported: impact != Some(Impact::EmbeddingProfile)
            && request.policy.embeddings.backend.dimension() == view.dimension,
    })
}

/// Compare-and-swap under the registry lock. A failed/no-op request does not
/// write history, advance generations, notify, enable indexing or change pauses.
pub async fn apply(client: &mut Client, id: Uuid, request: &ApplyRequest) -> Result<ApplyResult> {
    request.validate()?;
    let tx = client.transaction().await?;
    lock(&tx).await?;
    apply_locked(tx, id, request).await
}

/// Path-based command guard: resolve the current family while holding the same
/// registry lock used by lifecycle changes, then compare family AND revision.
/// No preparation or registration is performed on this route.
pub async fn apply_path(
    client: &mut Client,
    path: &std::path::Path,
    request: &ApplyRequest,
) -> Result<Value> {
    request.validate()?;
    let tx = client.transaction().await?;
    lock(&tx).await?;
    let ready: bool = tx.query_one("SELECT count(*)=2 FROM information_schema.columns WHERE table_schema='public' AND table_name='repos' AND column_name IN ('registration_intent','registration_completed_at')", &[]).await?.get(0);
    if !ready {
        return Err(PolicyError::new("schema_not_ready", "registration metadata requires separately authorized preparation; apply runs no migrations"));
    }
    let mut context = super::readonly::resolve(&tx, path).await?;
    let id = context
        .view
        .as_ref()
        .ok_or_else(|| PolicyError::new("not_registered", "directory has no registered family"))?
        .family_id;
    let incomplete: bool = tx.query_one("SELECT registration_intent IS NOT NULL AND registration_completed_at IS NULL FROM public.repos WHERE id=$1", &[&id]).await?.get(0);
    if incomplete {
        return Err(PolicyError::new(
            "registration_incomplete",
            "finish the interrupted add before changing policy",
        ));
    }
    let result = apply_locked(tx, id, request).await?;
    let scheduled = result.reconciliation_needed && result.view.indexing_enabled;
    context.view = Some(result.view);
    let mut document = context.document();
    document["changed"] = json!(result.changed);
    document["impact"] = json!(result.impact);
    document["reconciliation_needed"] = json!(result.reconciliation_needed);
    document["reconciliation_scheduled"] = json!(scheduled);
    Ok(document)
}

async fn apply_locked(
    tx: tokio_postgres::Transaction<'_>,
    id: Uuid,
    request: &ApplyRequest,
) -> Result<ApplyResult> {
    tx.query_one(
        &format!(
            "SELECT current_revision FROM {}.family_policy WHERE singleton FOR UPDATE",
            schema(id)
        ),
        &[],
    )
    .await
    .map_err(|_| PolicyError::new("database_error", "cannot lock policy revision"))?;
    let family = family(&tx, id).await?;
    let view = read(&tx, &family).await?.ok_or_else(|| {
        PolicyError::new(
            "policy_not_initialized",
            "family policy has not been initialized",
        )
    })?;
    guards(&view, request)?;
    let impact = changed(&view, request);
    if impact.is_none() {
        tx.commit().await?;
        return Ok(ApplyResult {
            view,
            changed: false,
            impact: None,
            reconciliation_needed: false,
        });
    }
    check_dimension(&request.policy, &family)?;
    if impact == Some(Impact::EmbeddingProfile) {
        if view.indexing_enabled && !request.acknowledge_reindex {
            return Err(PolicyError::new(
                "reindex_required",
                "embedding profile changes require explicit reindex acknowledgement",
            ));
        }
        return Err(PolicyError::new(
            "profile_change_not_supported",
            "profile-aware runtime migration is not enabled",
        ));
    }
    if view.revision == MAX_REVISION {
        return Err(PolicyError::new(
            "revision_exhausted",
            "policy revision cannot advance",
        ));
    }
    let revision = (view.revision + 1) as i64;
    let policy = serde_json::to_value(&request.policy).map_err(|_| invalid_storage())?;
    let schema = schema(id);
    tx.execute(&format!("INSERT INTO {schema}.policy_versions(revision,format_version,defaults_revision,policy) VALUES($1,1,$2,$3)"),&[&revision,&view.defaults_revision,&policy]).await?;
    tx.execute(
        &format!("UPDATE {schema}.family_policy SET current_revision=$1 WHERE singleton"),
        &[&revision],
    )
    .await?;
    tx.execute(&format!("UPDATE {schema}.checkouts SET dirty_generation=dirty_generation+1 WHERE registration_state<>'retired'"),&[]).await?;
    if view.indexing_enabled && impact == Some(Impact::Selection) {
        tx.execute(
            "UPDATE public.repos SET indexed_at=NULL WHERE id=$1",
            &[&id],
        )
        .await?;
    }
    if impact == Some(Impact::Selection) && view.indexing_enabled {
        crate::maintenance::request_family(&tx, id)
            .await
            .map_err(|_| {
                PolicyError::new("database_error", "cannot record selection maintenance")
            })?;
    }
    wake(&tx, id).await?;
    let view = read(&tx, &family).await?.ok_or_else(invalid_storage)?;
    tx.commit().await?;
    Ok(ApplyResult {
        view,
        changed: true,
        impact,
        reconciliation_needed: true,
    })
}

/// Explicit recreation preserves the registration, policy history and notes.
/// The current profile and the empty derived index become visible together.
pub async fn recreate_profile(
    client: &mut Client,
    id: Uuid,
    request: &RecreateProfile,
) -> anyhow::Result<Value> {
    anyhow::ensure!(request.api_version == 1, "unsupported API version");
    anyhow::ensure!(
        id == request.expected_family_id,
        "repository family has changed"
    );
    crate::db::run_repo_migrations(client, &crate::store::repo_schema(id)).await?;
    let tx = client.transaction().await?;
    lock(&tx).await?;
    crate::worktrees::lock(&tx, id).await?;
    tx.query_one(
        "SELECT id FROM public.repos WHERE id=$1 AND retired_at IS NULL FOR UPDATE",
        &[&id],
    )
    .await?;
    let family = family(&tx, id).await?;
    let view = read(&tx, &family).await?.ok_or_else(invalid_storage)?;
    if view.policy.embeddings.backend == request.backend
        && view.policy.embeddings.model == request.model
    {
        return Ok(json!({"recreated": false, "family_id": id, "revision": view.revision}));
    }
    anyhow::ensure!(
        view.revision == request.expected_revision,
        "policy revision has changed"
    );
    anyhow::ensure!(
        view.revision < MAX_REVISION,
        "policy revision cannot advance"
    );
    let mut policy = view.policy;
    policy.embeddings.backend = request.backend;
    policy.embeddings.model = request.model.clone();
    policy.validate()?;
    let revision = (view.revision + 1) as i64;
    let dimension = request.backend.dimension() as i32;
    let policy = serde_json::to_value(&policy)?;
    let s = schema(id);

    for row in tx
        .query(
            &format!("SELECT id FROM {s}.checkouts WHERE id <> $1"),
            &[&id],
        )
        .await?
    {
        crate::graph::drop_graph(tx.client(), row.get(0)).await?;
    }
    crate::graph::drop_graph(tx.client(), id).await?;
    crate::store::ensure_graph(tx.client(), id).await?;
    tx.batch_execute(&format!(
        "DELETE FROM {s}.checkout_structural_snapshots;
         DELETE FROM {s}.checkout_file_versions;
         DELETE FROM {s}.checkout_prepared_files;
         DELETE FROM {s}.file_versions;
         DELETE FROM {s}.chunks;
         UPDATE {s}.checkouts SET indexed_at=NULL, indexed_git_head=NULL,
            publication_generation=publication_generation+1, oversized_paths='{{}}', unreadable_paths='{{}}';
         ALTER TABLE {s}.chunks ALTER COLUMN embedding TYPE public.vector({dimension});"
    )).await?;
    tx.execute(
        "UPDATE public.knowledge SET embedding=NULL WHERE family_id=$1",
        &[&id],
    )
    .await?;
    tx.execute(
        "UPDATE public.repos SET embedding_dim=$2,indexed_at=NULL WHERE id=$1",
        &[&id, &dimension],
    )
    .await?;
    tx.execute(
        &format!("INSERT INTO {s}.policy_versions(revision,format_version,defaults_revision,policy) VALUES($1,1,$2,$3)"),
        &[&revision, &view.defaults_revision, &policy],
    ).await?;
    tx.execute(
        &format!("UPDATE {s}.family_policy SET current_revision=$1 WHERE singleton"),
        &[&revision],
    )
    .await?;
    wake(&tx, id).await?;
    tx.commit().await?;
    Ok(json!({"recreated": true, "family_id": id, "revision": revision}))
}

/// Convert the registered directory in place when it becomes a primary Git
/// checkout. The existing index remains available until its Git view publishes.
pub async fn convert_directory(
    client: &mut Client,
    id: Uuid,
    path: &std::path::Path,
    request: &super::start::Request,
) -> anyhow::Result<Value> {
    use crate::family_store::{CheckoutIdentity, FamilyKind};
    anyhow::ensure!(request.api_version == 1, "unsupported API version");
    anyhow::ensure!(
        id == request.expected_family_id,
        "repository family has changed"
    );
    let observed = CheckoutIdentity::discover(path).await?;
    anyhow::ensure!(
        observed.family.kind == FamilyKind::Git
            && observed.git_dir.as_ref() == Some(&observed.family.key),
        "conversion requires the primary Git checkout"
    );
    let tx = client.transaction().await?;
    lock(&tx).await?;
    crate::worktrees::lock(&tx, id).await?;
    tx.query_one(
        "SELECT id FROM public.repos WHERE id=$1 AND retired_at IS NULL FOR UPDATE",
        &[&id],
    )
    .await?;
    observed.revalidate().await?;
    let family = family(&tx, id).await?;
    let saved = family.identity.as_ref().ok_or_else(invalid_storage)?;
    let view = read(&tx, &family).await?.ok_or_else(invalid_storage)?;
    if saved == &observed.family {
        return Ok(json!({"converted": false, "family_id": id, "revision": view.revision}));
    }
    anyhow::ensure!(
        saved.kind == FamilyKind::Directory && saved.key == observed.root,
        "selected Git root does not match the registered directory"
    );
    anyhow::ensure!(
        view.revision == request.expected_revision,
        "policy revision has changed"
    );
    anyhow::ensure!(
        family_store::lookup_family(&tx, &observed.family)
            .await?
            .is_none(),
        "the Git repository belongs to another registered family"
    );
    let s = schema(id);
    let checkout = tx
        .query_one(
            &format!(
                "UPDATE {s}.checkouts SET git_dir=$2, git_state='unknown',
                    merge_in_progress=NULL,rebase_merge_in_progress=NULL,
                    rebase_apply_in_progress=NULL,unmerged_index=NULL
                 WHERE root=$1 AND git_dir IS NULL AND registration_state='active' RETURNING id"
            ),
            &[&observed.root.bytes(), &observed.family.key.bytes()],
        )
        .await?
        .get::<_, Uuid>(0);
    tx.execute(
        &format!("INSERT INTO {s}.worktree_base(singleton,checkout) VALUES (true,$1)"),
        &[&checkout],
    )
    .await?;
    tx.execute(
        "UPDATE public.repos SET family_kind='git',family_key=$2,indexed_at=NULL WHERE id=$1",
        &[&id, &observed.family.key.bytes()],
    )
    .await?;
    if view.indexing_enabled {
        crate::maintenance::request_family(&tx, id).await?;
    }
    wake(&tx, id).await?;
    tx.commit().await?;
    Ok(json!({"converted": true, "family_id": id, "revision": view.revision}))
}
