//! Dedicated, cancellation-safe family preparation for explicit registration.
use super::{get_family, lock_registry, Family};
use crate::{db, store};
use anyhow::{ensure, Context, Result};
use std::future::Future;
use std::pin::Pin;
use tokio::task::JoinHandle;
use tokio_postgres::Client;
use uuid::Uuid;

// Two-integer namespace MUNI, purpose 2. Registry mutations use purpose 1.
// Order: family job lock (when applicable), this lock, registry transaction lock.
const MIGRATION_LOCK: i32 = 2;

/// Provenance supplied by the registration/import caller, never inferred from
/// storage_generation (both old registrations and new reservations use legacy).
#[derive(Debug, Clone, Copy)]
pub enum GraphRequirement {
    /// Import, upgrade or revalidation: absence is an error, never permission
    /// to create an empty replacement for previously indexed graph data.
    Existing,
    /// Only for a newly reserved family and retries of its initial preparation.
    /// A valid graph from a partially completed attempt is preserved.
    NewReservation,
    /// JSON add: verify persistent creation intent under the registry lock.
    /// Completed registrations require their existing graph; never replace it.
    RegistrationIntent,
}

/// Own both halves of a dedicated connection. Dropping an in-flight preparation
/// aborts its driver, closes the socket and releases its session advisory lock.
/// Do not use a pooled/shared connection or an independently spawned driver.
pub struct PreparationConnection {
    client: Client,
    driver: JoinHandle<()>,
    cancel: Option<
        Pin<Box<dyn Future<Output = std::result::Result<(), tokio_postgres::Error>> + Send>>,
    >,
    completed: bool,
}

/// Holds the preparation lock until registration has finished using the ready
/// schema pair. Another preparer cannot mark it migrating between these steps.
pub struct PreparedFamily {
    pub family: Family,
    _connection: PreparationConnection,
}

impl Drop for PreparationConnection {
    fn drop(&mut self) {
        self.driver.abort();
        // PostgreSQL can remain inside a lock wait after the TCP peer closes.
        // Send its cancellation protocol as well, using the caller's transport
        // (including TLS policy). Never substitute NoTls for a TLS connection.
        if !self.completed {
            if let (Some(cancel), Ok(runtime)) =
                (self.cancel.take(), tokio::runtime::Handle::try_current())
            {
                runtime.spawn(async move {
                    let _ = tokio::time::timeout(std::time::Duration::from_secs(5), cancel).await;
                });
            }
        }
    }
}

impl PreparationConnection {
    /// Pass the client and unspawned connection future returned by connect(),
    /// plus an unpolled cancellation future made from this client's cancel_token
    /// and the same transport/TLS policy. It is used only on interruption.
    pub fn new(
        client: Client,
        connection: impl Future<Output = std::result::Result<(), tokio_postgres::Error>>
            + Send
            + 'static,
        cancel: impl Future<Output = std::result::Result<(), tokio_postgres::Error>> + Send + 'static,
    ) -> Self {
        let driver = tokio::spawn(async move {
            // Query callers receive connection errors. Do not persist/log raw
            // connection diagnostics, which can contain credentials or SQL data.
            let _ = connection.await;
        });
        Self {
            client,
            driver,
            cancel: Some(Box::pin(cancel)),
            completed: false,
        }
    }

    async fn lock(&mut self) -> Result<()> {
        self.client
            .execute(
                "SELECT pg_advisory_lock($1,$2)",
                &[&super::LOCK_NAMESPACE, &MIGRATION_LOCK],
            )
            .await?;
        Ok(())
    }

    /// Public/ledger bootstrap has the same lock as family preparation.
    /// Consumes the connection even on error or cancellation.
    pub async fn prepare_public(mut self) -> Result<()> {
        self.lock().await?;
        let result = db::run_migrations(&mut self.client).await;
        self.completed = true;
        result
    }

    /// Recheck the required templates and graph even if metadata says ready.
    /// Does not enable indexing, change the storage selector, import identity,
    /// register checkouts, clear graph data, or publish snapshots.
    pub async fn prepare_family(self, id: Uuid, graph: GraphRequirement) -> Result<Family> {
        Ok(self.prepare_family_guarded(id, graph).await?.family.clone())
    }

    pub async fn prepare_family_guarded(
        mut self,
        id: Uuid,
        graph: GraphRequirement,
    ) -> Result<PreparedFamily> {
        self.lock().await?;
        {
            let tx = self.client.transaction().await?;
            lock_registry(&tx).await?;
            let family = get_family(&tx, id)
                .await?
                .context("family not registered")?;
            ensure!(family.retired_at.is_none(), "family is retired");
            ensure!(
                family.identity.is_some(),
                "family identity has not been imported"
            );
            tx.execute(
                "UPDATE public.repos SET schema_state='migrating',schema_error=NULL WHERE id=$1",
                &[&id],
            )
            .await?;
            tx.commit().await?;
        }
        let mut diagnostic = "public migration preparation failed";
        let result: Result<()> = async {
            db::run_migrations(&mut self.client).await?;
            diagnostic = "application migration preparation failed";
            let schema = store::repo_schema(id);
            db::run_repo_migrations(&mut self.client, &schema).await?;
            // Kryzhen verifies canonical checksums while migrating. Confirm
            // this target has every required association, and physically exists.
            let applied = kryzhen::postgres::load_applied_for_schema(&self.client, &schema).await?;
            for migration in db::embedded_repo_migrations()? {
                ensure!(
                    applied.contains(&migration.name),
                    "required application migration missing"
                );
            }
            ensure!(
                self.client
                    .query_one(
                        "SELECT EXISTS(SELECT 1 FROM pg_namespace WHERE nspname=$1)",
                        &[&schema]
                    )
                    .await?
                    .get::<_, bool>(0),
                "application namespace missing"
            );
            diagnostic = "AGE graph preparation or mapping validation failed";
            let tx = self.client.transaction().await?;
            lock_registry(&tx).await?;
            prepare_graph(&tx, id, graph).await?;
            tx.commit().await?;
            Ok(())
        }
        .await;
        if let Err(error) = result {
            // Fixed stage diagnostics only; raw DB errors can include user data.
            // A broken connection can leave migrating, which is also non-ready.
            if self.finish(id, "failed", Some(diagnostic)).await.is_err() {
                return Err(error.context(
                    "preparation failed; could not persist failure state, family remains non-ready",
                ));
            }
            return Err(error.context(diagnostic));
        }
        self.finish(id, "ready", None).await?;
        let family = get_family(&self.client, id)
            .await?
            .context("prepared family disappeared")?;
        self.completed = true;
        Ok(PreparedFamily {
            family,
            _connection: self,
        })
    }

    async fn finish(&mut self, id: Uuid, state: &str, diagnostic: Option<&str>) -> Result<()> {
        let tx = self.client.transaction().await?;
        lock_registry(&tx).await?;
        ensure!(tx.execute("UPDATE public.repos SET schema_state=$2,schema_error=$3 WHERE id=$1 AND schema_state='migrating' AND retired_at IS NULL AND family_key IS NOT NULL",
            &[&id,&state,&diagnostic]).await? == 1, "family lifecycle changed during preparation");
        tx.commit().await?;
        Ok(())
    }
}

async fn prepare_graph(
    client: &impl tokio_postgres::GenericClient,
    id: Uuid,
    requirement: GraphRequirement,
) -> Result<()> {
    let requirement = if matches!(requirement, GraphRequirement::RegistrationIntent) {
        let row = client.query_one("SELECT registration_intent IS NOT NULL, registration_completed_at IS NULL, NOT ever_indexed AND indexing_enabled_at IS NULL FROM public.repos WHERE id=$1 AND retired_at IS NULL", &[&id]).await?;
        ensure!(
            row.get::<_, bool>(0),
            "new-family creation provenance is absent"
        );
        if row.get::<_, bool>(1) && row.get::<_, bool>(2) {
            GraphRequirement::NewReservation
        } else {
            GraphRequirement::Existing
        }
    } else {
        requirement
    };
    let name = store::graph_name(id);
    let mapping = client.query_opt("SELECT n.nspname FROM ag_catalog.ag_graph g LEFT JOIN pg_namespace n ON n.oid=g.namespace WHERE g.name=$1", &[&name]).await?;
    match mapping {
        Some(row) => ensure!(
            row.get::<_, Option<String>>(0).as_deref() == Some(&name),
            "AGE graph namespace does not match family"
        ),
        None => {
            ensure!(
                matches!(requirement, GraphRequirement::NewReservation),
                "expected existing family graph is missing"
            );
            ensure!(
                !client
                    .query_one(
                        "SELECT EXISTS(SELECT 1 FROM pg_namespace WHERE nspname=$1)",
                        &[&name]
                    )
                    .await?
                    .get::<_, bool>(0),
                "orphan graph namespace requires diagnosis"
            );
            // Identifier is derived only from a UUID. AGE alone creates its schema.
            client
                .query_one(&format!("SELECT ag_catalog.create_graph('{name}')"), &[])
                .await?;
        }
    }
    // Reobserve the AGE name -> namespace association after creation or reuse.
    ensure!(client.query_one("SELECT EXISTS(SELECT 1 FROM ag_catalog.ag_graph g JOIN pg_namespace n ON n.oid=g.namespace WHERE g.name=$1 AND n.nspname=$1)",&[&name]).await?.get::<_,bool>(0), "AGE graph mapping validation failed");
    Ok(())
}
