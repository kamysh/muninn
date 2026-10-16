//! Additive family/checkout metadata and explicit preparation coordination.
//! Not connected to legacy callers. Metadata access never prepares schemas;
//! PreparationConnection owns that separate operation. Neither enables indexing
//! nor publishes snapshots. Coverage lives in tests/family_persistence.rs.
mod path;
mod preparation;
mod types;
pub use path::StoredPath;
pub use preparation::{GraphRequirement, PreparationConnection, PreparedFamily};
pub use types::*;

use anyhow::{ensure, Context, Result};
use std::io::ErrorKind;
use std::path::Path;
use tokio_postgres::{Client, GenericClient, Row, Transaction};
use uuid::Uuid;

const FAMILY_COLUMNS: &str = "id, path, name, embedding_dim, paused, family_kind, path_encoding, family_key, retired_at, schema_state, schema_error, storage_generation, indexing_enabled_at, indexing_enable_origin";
const CHECKOUT_COLUMNS: &str = "id, root, git_dir, incarnation, registration_state, paused, created_at, retired_at, dirty_generation, availability, git_state, merge_in_progress, rebase_merge_in_progress, rebase_apply_in_progress, unmerged_index, observed_at, last_seen_at, observation_error";

// Two-int advisory key space does not overlap the existing bigint job locks.
// Namespace ASCII MUNI; purpose 1 is registry mutations. Reserve purpose 2 for
// migration coordination in preparation.rs.
const LOCK_NAMESPACE: i32 = 0x4d554e49;
const REGISTRY_LOCK: i32 = 1;

pub(crate) async fn lock_registry(tx: &Transaction<'_>) -> Result<()> {
    tx.execute(
        "SELECT pg_advisory_xact_lock($1, $2)",
        &[&LOCK_NAMESPACE, &REGISTRY_LOCK],
    )
    .await?;
    Ok(())
}

fn checkouts_table(id: Uuid) -> String {
    format!("\"{}\".\"checkouts\"", crate::store::repo_schema(id))
}

/// Lookup includes a full-byte comparison even though the index is on a digest.
/// Legacy rows without imported identity are deliberately not guessed by path.
pub async fn lookup_family(
    client: &impl GenericClient,
    identity: &FamilyIdentity,
) -> Result<Option<Family>> {
    let row = client.query_opt(&format!(
        "SELECT {FAMILY_COLUMNS} FROM public.repos WHERE retired_at IS NULL AND family_kind = $1 AND path_encoding = $2 AND pg_catalog.sha256(family_key) = pg_catalog.sha256($3::bytea)"
    ), &[&identity.kind.as_str(), &identity.key.encoding(), &identity.key.bytes()]).await?;
    let family = row.map(family_from_row).transpose()?;
    if let Some(family) = &family {
        ensure!(
            family.identity.as_ref() == Some(identity),
            "family identity digest collision"
        );
    }
    Ok(family)
}

pub async fn get_family(client: &impl GenericClient, id: Uuid) -> Result<Option<Family>> {
    client
        .query_opt(
            &format!("SELECT {FAMILY_COLUMNS} FROM public.repos WHERE id = $1"),
            &[&id],
        )
        .await?
        .map(family_from_row)
        .transpose()
}

/// Retire a family only when its stored local identity is confirmed absent.
/// Other filesystem errors and Git discovery failures are not proof of removal.
/// The family row and its schema remain available for explicit recovery/removal.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MissingState {
    Present,
    Pending,
    Retired,
}

pub async fn retire_if_missing(client: &mut Client, id: Uuid) -> Result<MissingState> {
    let tx = client.transaction().await?;
    lock_registry(&tx).await?;
    let Some(family) = get_family(&tx, id).await? else {
        return Ok(MissingState::Present);
    };
    if family.retired_at.is_some() {
        return Ok(MissingState::Present);
    }
    let path = match &family.identity {
        Some(identity) => identity.key.to_path_buf()?,
        None => Path::new(&family.legacy_path).to_path_buf(),
    };
    let absent = matches!(tokio::fs::metadata(&path).await, Err(ref error) if error.kind() == ErrorKind::NotFound);
    if !absent {
        tx.execute(
            "UPDATE public.repos SET missing_since=NULL WHERE id=$1 AND missing_since IS NOT NULL",
            &[&id],
        )
        .await?;
        tx.commit().await?;
        return Ok(MissingState::Present);
    }
    let elapsed: Option<bool> = tx
        .query_one(
            "SELECT missing_since <= now() - interval '60 seconds' FROM public.repos WHERE id=$1",
            &[&id],
        )
        .await?
        .get(0);
    if elapsed.is_none() {
        tx.execute(
            "UPDATE public.repos SET missing_since=now() WHERE id=$1 AND missing_since IS NULL",
            &[&id],
        )
        .await?;
        tx.commit().await?;
        return Ok(MissingState::Pending);
    }
    if elapsed == Some(false) {
        return Ok(MissingState::Pending);
    }
    tx.query_one(
        "SELECT pg_advisory_xact_lock(hashtextextended($1,771913))",
        &[&id.to_string()],
    )
    .await?;
    // A checkout can be recreated while we wait for an indexing lock.
    if !matches!(tokio::fs::metadata(&path).await, Err(ref error) if error.kind() == ErrorKind::NotFound)
    {
        tx.execute(
            "UPDATE public.repos SET missing_since=NULL WHERE id=$1",
            &[&id],
        )
        .await?;
        tx.commit().await?;
        return Ok(MissingState::Present);
    }
    let changed = tx
        .execute(
            "UPDATE public.repos SET retired_at=now() WHERE id=$1 AND retired_at IS NULL",
            &[&id],
        )
        .await?;
    tx.commit().await?;
    Ok(if changed == 1 {
        MissingState::Retired
    } else {
        MissingState::Present
    })
}

/// Reserve a new, pending family or return the existing matching reservation.
/// This commits its registry row only; no schema/graph is created. Existing legacy
/// path ownership must be imported explicitly, never adopted by this operation.
pub async fn reserve_family(
    client: &mut Client,
    identity: &CheckoutIdentity,
    legacy_path: &str,
    name: &str,
    embedding_dim: u32,
) -> Result<Family> {
    let tx = client.transaction().await?;
    lock_registry(&tx).await?;
    let family =
        reserve_family_in_tx(&tx, identity, legacy_path, name, embedding_dim, None).await?;
    tx.commit().await?;
    Ok(family)
}

/// Used by registration to atomically reserve identity and its recovery intent.
/// The caller holds the registry lock; this helper never commits or prepares.
pub(crate) async fn reserve_family_in_tx(
    tx: &Transaction<'_>,
    identity: &CheckoutIdentity,
    legacy_path: &str,
    name: &str,
    embedding_dim: u32,
    intent: Option<&serde_json::Value>,
) -> Result<Family> {
    let dim = i32::try_from(embedding_dim).context("embedding dimension exceeds SQL integer")?;
    ensure!(dim > 0, "embedding dimension must be positive");
    ensure!(
        !legacy_path.is_empty() && !name.is_empty(),
        "family path/name must not be empty"
    );
    identity.revalidate().await?;
    if let Some(family) = lookup_family(tx, &identity.family).await? {
        ensure!(
            family.embedding_dim == embedding_dim,
            "family embedding dimension differs; explicit migration required"
        );
        return Ok(family);
    }
    ensure!(
        tx.query_opt(
            "SELECT id FROM public.repos WHERE path = $1 AND retired_at IS NULL",
            &[&legacy_path]
        )
        .await?
        .is_none(),
        "legacy path is already registered; import or resolve that registration explicitly"
    );
    // An unimported main checkout may have a different path from this linked
    // checkout but already own the family's UUID/schema pair. Discover those
    // identities before reserving a new UUID; never silently duplicate the family.
    for row in tx
        .query(
            "SELECT path FROM public.repos WHERE family_key IS NULL AND retired_at IS NULL",
            &[],
        )
        .await?
    {
        let path: &str = row.try_get("path")?;
        let legacy = CheckoutIdentity::discover(Path::new(path))
            .await
            .context("cannot establish legacy family identity; complete inventory first")?;
        ensure!(
            legacy.family != identity.family && legacy.root != identity.root,
            "family has an unresolved legacy registration; import its existing ID first"
        );
    }
    let row = tx.query_one(&format!(
        "INSERT INTO public.repos (id, path, name, embedding_dim, family_kind, path_encoding, family_key, registration_intent) VALUES ($1,$2,$3,$4,$5,$6,$7,$8) RETURNING {FAMILY_COLUMNS}"
    ), &[&Uuid::new_v4(), &legacy_path, &name, &dim, &identity.family.kind.as_str(),
        &identity.family.key.encoding(), &identity.family.key.bytes(), &intent]).await?;
    let family = family_from_row(row)?;
    Ok(family)
}

fn ready_identity(family: &Family) -> Result<&FamilyIdentity> {
    ensure!(family.retired_at.is_none(), "family is retired");
    ensure!(
        family.schema_state == SchemaState::Ready,
        "family schema pair is not ready"
    );
    family
        .identity
        .as_ref()
        .context("family identity has not been imported")
}

async fn checkout_by_key(
    client: &impl GenericClient,
    family: &Family,
    path: &StoredPath,
    column: &str,
) -> Result<Option<Checkout>> {
    // Column is selected only by the private callers below, never user input.
    ensure!(
        column == "root" || column == "git_dir",
        "invalid checkout lookup column"
    );
    let identity = ready_identity(family)?;
    ensure!(
        path.encoding() == identity.key.encoding(),
        "checkout path encoding differs from family"
    );
    let table = checkouts_table(family.id);
    let row = client.query_opt(&format!(
        "SELECT {CHECKOUT_COLUMNS} FROM {table} WHERE registration_state <> 'retired' AND pg_catalog.sha256({column}) = pg_catalog.sha256($1::bytea)"
    ), &[&path.bytes()]).await?;
    let checkout = row
        .map(|row| checkout_from_row(row, identity.key.encoding()))
        .transpose()?;
    if let Some(checkout) = &checkout {
        let stored = if column == "root" {
            Some(&checkout.root)
        } else {
            checkout.git_dir.as_ref()
        };
        ensure!(stored == Some(path), "checkout identity digest collision");
    }
    Ok(checkout)
}

/// Resolves existing metadata only. The caller must inspect current filesystem
/// identity and Git state before using this record for scheduling or publication.
pub async fn lookup_checkout(
    client: &impl GenericClient,
    family_id: Uuid,
    root: &StoredPath,
) -> Result<Option<ResolvedCheckout>> {
    let family = get_family(client, family_id)
        .await?
        .context("family not registered")?;
    let checkout = checkout_by_key(client, &family, root, "root").await?;
    Ok(checkout.map(|checkout| ResolvedCheckout { family, checkout }))
}

/// Idempotent discovery: a suppressed checkout remains suppressed. Explicit
/// reactivation/relocation and legacy import are separate lifecycle operations.
pub async fn register_checkout(
    client: &mut Client,
    family_id: Uuid,
    discovered: &CheckoutIdentity,
) -> Result<Checkout> {
    let tx = client.transaction().await?;
    lock_registry(&tx).await?;
    discovered.revalidate().await?;
    let family = get_family(&tx, family_id)
        .await?
        .context("family not registered")?;
    let identity = ready_identity(&family)?;
    ensure!(
        identity == &discovered.family,
        "checkout belongs to a different family"
    );
    if let Some(checkout) = checkout_by_key(&tx, &family, &discovered.root, "root").await? {
        ensure!(
            checkout.git_dir == discovered.git_dir,
            "checkout identity changed; explicit reconciliation required"
        );
        tx.commit().await?;
        return Ok(checkout);
    }
    if let Some(git_dir) = &discovered.git_dir {
        ensure!(
            checkout_by_key(&tx, &family, git_dir, "git_dir")
                .await?
                .is_none(),
            "checkout moved; explicit reconciliation required"
        );
    } else {
        let table = checkouts_table(family_id);
        ensure!(
            !tx.query_one(
                &format!(
                    "SELECT EXISTS(SELECT 1 FROM {table} WHERE registration_state <> 'retired')"
                ),
                &[]
            )
            .await?
            .get::<_, bool>(0),
            "directory family already has a checkout"
        );
    }
    // Cross-schema root ownership is an application invariant serialized by the
    // registry lock. Unprepared bound families cannot be silently skipped.
    for row in tx
        .query(
            &format!(
                "SELECT {FAMILY_COLUMNS} FROM public.repos WHERE retired_at IS NULL AND id <> $1"
            ),
            &[&family_id],
        )
        .await?
    {
        let other = family_from_row(row)?;
        if let Some(other_identity) = &other.identity {
            if other_identity.key.encoding() != discovered.root.encoding() {
                continue;
            }
            ensure!(
                checkout_by_key(&tx, &other, &discovered.root, "root")
                    .await?
                    .is_none(),
                "checkout root belongs to another family"
            );
        } else {
            // Canonicalize legacy paths too: symlink aliases cannot bypass the
            // ownership check. Missing/inaccessible legacy paths are unresolved.
            let root = StoredPath::canonicalize(Path::new(&other.legacy_path))
                .await
                .context("cannot establish legacy root ownership; complete inventory first")?;
            ensure!(
                root != discovered.root,
                "checkout root has an unresolved legacy registration"
            );
        }
    }
    let table = checkouts_table(family_id);
    let git_dir = discovered.git_dir.as_ref().map(StoredPath::bytes);
    let row = tx
        .query_one(
            &format!(
                "INSERT INTO {table} (root, git_dir) VALUES ($1,$2) RETURNING {CHECKOUT_COLUMNS}"
            ),
            &[&discovered.root.bytes(), &git_dir],
        )
        .await?;
    let checkout = checkout_from_row(row, identity.key.encoding())?;
    tx.commit().await?;
    Ok(checkout)
}

/// Compare-and-swap an observation. False means the checkout was retired,
/// suppressed, replaced, invalidated, or is inconsistent with the observation.
/// This neither increments the dirty generation nor authorizes a build.
pub async fn record_checkout_observation(
    client: &impl GenericClient,
    family_id: Uuid,
    token: CheckoutToken,
    observation: &CheckoutObservation,
) -> Result<bool> {
    observation.validate()?;
    ensure!(token.dirty_generation >= 0, "negative checkout generation");
    let (state, flags) = observation.git_state.columns();
    let table = checkouts_table(family_id);
    let count = client.execute(&format!(
        "UPDATE {table} SET availability=$4, git_state=$5, merge_in_progress=$6,
         rebase_merge_in_progress=$7, rebase_apply_in_progress=$8, unmerged_index=$9,
         observation_error=$10, observed_at=now(),
         last_seen_at=CASE WHEN $4='available' THEN now() ELSE last_seen_at END
         WHERE id=$1 AND incarnation=$2 AND dirty_generation=$3 AND registration_state='active'
         AND ($5='unknown' OR ($5='not-git' AND git_dir IS NULL) OR ($5 IN ('clear','blocked') AND git_dir IS NOT NULL))
         AND EXISTS (SELECT 1 FROM public.repos WHERE id=$11 AND retired_at IS NULL AND schema_state='ready')"
    ), &[&token.id, &token.incarnation, &token.dirty_generation, &observation.availability.as_str(),
        &state, &flags[0], &flags[1], &flags[2], &flags[3], &observation.error, &family_id]).await?;
    Ok(count == 1)
}

/// Invalidate work captured at the supplied generation. Returns None for an
/// outdated token or inactive checkout. PostgreSQL overflow errors propagate;
/// the generation is never reset or wrapped. No snapshot pointer is changed.
pub async fn invalidate_checkout(
    client: &impl GenericClient,
    family_id: Uuid,
    token: CheckoutToken,
) -> Result<Option<CheckoutToken>> {
    ensure!(token.dirty_generation >= 0, "negative checkout generation");
    let table = checkouts_table(family_id);
    let row = client.query_opt(&format!(
        "UPDATE {table} SET dirty_generation=dirty_generation+1
         WHERE id=$1 AND incarnation=$2 AND dirty_generation=$3 AND registration_state='active'
         AND EXISTS (SELECT 1 FROM public.repos WHERE id=$4 AND retired_at IS NULL AND schema_state='ready')
         RETURNING id, incarnation, dirty_generation"
    ), &[&token.id, &token.incarnation, &token.dirty_generation, &family_id]).await?;
    row.map(|row| {
        Ok(CheckoutToken {
            id: row.try_get("id")?,
            incarnation: row.try_get("incarnation")?,
            dirty_generation: row.try_get("dirty_generation")?,
        })
    })
    .transpose()
}

fn family_from_row(row: Row) -> Result<Family> {
    let kind: Option<String> = row.try_get("family_kind")?;
    let encoding: Option<String> = row.try_get("path_encoding")?;
    let key: Option<Vec<u8>> = row.try_get("family_key")?;
    let identity = match (kind, encoding, key) {
        (None, None, None) => None,
        (Some(kind), Some(encoding), Some(key)) => Some(FamilyIdentity {
            kind: FamilyKind::from_db(&kind)?,
            key: StoredPath::from_db(&encoding, key)?,
        }),
        _ => anyhow::bail!("incomplete stored family identity"),
    };
    let dim: i32 = row.try_get("embedding_dim")?;
    ensure!(dim > 0, "invalid stored embedding dimension");
    let origin: Option<String> = row.try_get("indexing_enable_origin")?;
    Ok(Family {
        id: row.try_get("id")?,
        legacy_path: row.try_get("path")?,
        name: row.try_get("name")?,
        embedding_dim: dim as u32,
        paused: row.try_get("paused")?,
        identity,
        retired_at: row.try_get("retired_at")?,
        schema_state: SchemaState::from_db(row.try_get("schema_state")?)?,
        schema_error: row.try_get("schema_error")?,
        storage_generation: StorageGeneration::from_db(row.try_get("storage_generation")?)?,
        indexing_enabled_at: row.try_get("indexing_enabled_at")?,
        indexing_enable_origin: origin.as_deref().map(EnableOrigin::from_db).transpose()?,
    })
}

fn checkout_from_row(row: Row, encoding: &str) -> Result<Checkout> {
    let git_dir: Option<Vec<u8>> = row.try_get("git_dir")?;
    Ok(Checkout {
        token: CheckoutToken {
            id: row.try_get("id")?,
            incarnation: row.try_get("incarnation")?,
            dirty_generation: row.try_get("dirty_generation")?,
        },
        root: StoredPath::from_db(encoding, row.try_get("root")?)?,
        git_dir: git_dir
            .map(|bytes| StoredPath::from_db(encoding, bytes))
            .transpose()?,
        registration_state: RegistrationState::from_db(row.try_get("registration_state")?)?,
        paused: row.try_get("paused")?,
        created_at: row.try_get("created_at")?,
        retired_at: row.try_get("retired_at")?,
        availability: Availability::from_db(row.try_get("availability")?)?,
        git_state: ObservedGitState::from_db(
            row.try_get("git_state")?,
            [
                row.try_get("merge_in_progress")?,
                row.try_get("rebase_merge_in_progress")?,
                row.try_get("rebase_apply_in_progress")?,
                row.try_get("unmerged_index")?,
            ],
        )?,
        observed_at: row.try_get("observed_at")?,
        last_seen_at: row.try_get("last_seen_at")?,
        observation_error: row.try_get("observation_error")?,
    })
}
