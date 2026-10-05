use anyhow::Result;
use include_dir::{include_dir, Dir};
use native_tls::TlsConnector;
use postgres_native_tls::MakeTlsConnector;
use std::sync::Arc;
use tokio::sync::mpsc;
use tokio_postgres::{AsyncMessage, Client, NoTls};

use crate::config::{DatabaseConfig, SslMode};

// search_path for all muninn connections:
//   public     — default schema; unqualified table creates land here
//   ag_catalog — needed for AGE operator resolution (agtype @>, etc.)
const SEARCH_PATH: &str = "public,ag_catalog";

// Embed the two migration sets at compile time.
// Each directory is one dependency graph applied to one target schema.
// The current sets have top-level SQL files, read in deterministic path order.
//
// public/ — the static, single-schema migration chain (repos, knowledge,
// mcp_usage, ...), applied via kryzhen::migrate(..., Some("public"), ...).
// repo/   — the per-repo schema template, applied once per repo via
// kryzhen::migrate(..., Some(schema), ...). See run_repo_migrations.
// AGE graph lifecycle is handled separately through its API in store::register_repo.
static PUBLIC_MIGRATIONS_DIR: Dir<'static> =
    include_dir!("$CARGO_MANIFEST_DIR/../../migrations/public");
static REPO_MIGRATIONS_DIR: Dir<'static> =
    include_dir!("$CARGO_MANIFEST_DIR/../../migrations/repo");

fn parse_migrations_dir(dir: &Dir<'static>) -> anyhow::Result<Vec<kryzhen::Migration>> {
    // Sort for deterministic loading. Kryzhen orders execution by dependencies,
    // including each block's implicit dependency on its in-file predecessor.
    let mut files: Vec<_> = dir
        .files()
        .filter(|f| f.path().extension().and_then(|e| e.to_str()) == Some("sql"))
        .collect();
    files.sort_by_key(|f| f.path());

    let mut all = Vec::new();
    for file in files {
        let label = file
            .path()
            .file_name()
            .and_then(|n| n.to_str())
            .unwrap_or("unknown.sql");
        let text = file
            .contents_utf8()
            .ok_or_else(|| anyhow::anyhow!("migration {label} is not valid UTF-8"))?;
        let blocks = kryzhen::parser::parse_file(text, label)?;
        all.extend(kryzhen::file::apply_implicit_deps(blocks));
    }
    Ok(all)
}

fn embedded_migrations() -> anyhow::Result<Vec<kryzhen::Migration>> {
    parse_migrations_dir(&PUBLIC_MIGRATIONS_DIR)
}

pub(crate) fn embedded_repo_migrations() -> anyhow::Result<Vec<kryzhen::Migration>> {
    parse_migrations_dir(&REPO_MIGRATIONS_DIR)
}

/// Read password for (host, port, dbname, user) from ~/.pgpass.
fn pgpass_lookup(host: &str, port: u16, dbname: &str, user: &str) -> Option<String> {
    let home = std::env::var("HOME").ok()?;
    let path = std::path::Path::new(&home).join(".pgpass");
    let content = std::fs::read_to_string(path).ok()?;
    let port_s = port.to_string();
    for line in content.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let parts: Vec<&str> = line.splitn(5, ':').collect();
        if parts.len() != 5 {
            continue;
        }
        let m = |pat: &str, val: &str| pat == "*" || pat == val;
        if m(parts[0], host) && m(parts[1], &port_s) && m(parts[2], dbname) && m(parts[3], user) {
            return Some(parts[4].to_owned());
        }
    }
    None
}

fn make_pg_config(cfg: &DatabaseConfig) -> tokio_postgres::Config {
    let mut c = tokio_postgres::Config::new();
    c.host(&cfg.host);
    c.port(cfg.port);
    c.user(&cfg.user);
    c.dbname(&cfg.dbname);
    c.options(format!("-c search_path={SEARCH_PATH}"));
    if let Some(secs) = cfg.connect_timeout {
        c.connect_timeout(std::time::Duration::from_secs(secs));
    }
    if let Some(pw) = pgpass_lookup(&cfg.host, cfg.port, &cfg.dbname, &cfg.user) {
        c.password(pw);
    }
    c
}

async fn connect_with_config(
    pg_cfg: tokio_postgres::Config,
    ssl_mode: Option<SslMode>,
    ssl_root_cert: Option<&str>,
    ssl_client_cert: Option<&str>,
    ssl_client_key: Option<&str>,
) -> Result<Client> {
    match ssl_mode {
        None | Some(SslMode::Disable) | Some(SslMode::Allow) | Some(SslMode::Prefer) => {
            let (client, conn) = pg_cfg.connect(NoTls).await?;
            tokio::spawn(async move {
                if let Err(e) = conn.await {
                    tracing::warn!("db connection error: {e}");
                }
            });
            Ok(client)
        }
        Some(mode) => {
            let tls = tls_connector(mode, ssl_root_cert, ssl_client_cert, ssl_client_key)?;
            let (client, conn) = pg_cfg.connect(tls).await?;
            tokio::spawn(async move {
                if let Err(e) = conn.await {
                    tracing::warn!("db connection error: {e}");
                }
            });
            Ok(client)
        }
    }
}

fn tls_connector(
    mode: SslMode,
    root: Option<&str>,
    cert: Option<&str>,
    key: Option<&str>,
) -> Result<MakeTlsConnector> {
    let mut builder = TlsConnector::builder();
    if matches!(mode, SslMode::Require) {
        builder.danger_accept_invalid_certs(true);
    }
    if let Some(path) = root {
        builder.add_root_certificate(native_tls::Certificate::from_pem(&std::fs::read(path)?)?);
    }
    if let (Some(cert), Some(key)) = (cert, key) {
        builder.identity(native_tls::Identity::from_pkcs8(
            &std::fs::read(cert)?,
            &std::fs::read(key)?,
        )?);
    }
    Ok(MakeTlsConnector::new(builder.build()?))
}

/// Dedicated coordinator transport, including cancellation with identical TLS
/// policy. No migration happens merely by opening this connection.
pub async fn connect_for_preparation(
    cfg: &DatabaseConfig,
) -> Result<crate::family_store::PreparationConnection> {
    use crate::family_store::PreparationConnection;
    let mut pg = make_pg_config(cfg);
    pg.application_name("muninn-family-preparation");
    // Index migrations can exceed a minute on existing repositories. Inherit
    // the server's statement limit while keeping lock waits bounded.
    pg.options(format!("-c search_path={SEARCH_PATH} -c lock_timeout=15000"));
    if cfg.connect_timeout.is_none() {
        pg.connect_timeout(std::time::Duration::from_secs(10));
    }
    match cfg.ssl_mode {
        None | Some(SslMode::Disable) | Some(SslMode::Allow) | Some(SslMode::Prefer) => {
            let (client, connection) = pg.connect(NoTls).await?;
            let token = client.cancel_token();
            Ok(PreparationConnection::new(client, connection, async move {
                token.cancel_query(NoTls).await
            }))
        }
        Some(mode) => {
            let tls = tls_connector(
                mode,
                cfg.ssl_root_cert.as_deref(),
                cfg.ssl_client_cert.as_deref(),
                cfg.ssl_client_key.as_deref(),
            )?;
            let (client, connection) = pg.connect(tls.clone()).await?;
            let token = client.cancel_token();
            Ok(PreparationConnection::new(client, connection, async move {
                token.cancel_query(tls).await
            }))
        }
    }
}

/// Connect using the given config.
pub async fn connect(cfg: &DatabaseConfig) -> Result<Client> {
    connect_internal(cfg, None).await
}

/// Connect with an explicit application name shown in pg_stat_activity.
pub async fn connect_with_app_name(cfg: &DatabaseConfig, app_name: &str) -> Result<Client> {
    connect_internal(cfg, Some(app_name)).await
}

async fn connect_internal(cfg: &DatabaseConfig, override_app_name: Option<&str>) -> Result<Client> {
    let mut pg_cfg = make_pg_config(cfg);
    let app_name = override_app_name.or(cfg.application_name.as_deref());
    if let Some(name) = app_name {
        pg_cfg.application_name(name);
    }
    connect_with_config(
        pg_cfg,
        cfg.ssl_mode,
        cfg.ssl_root_cert.as_deref(),
        cfg.ssl_client_cert.as_deref(),
        cfg.ssl_client_key.as_deref(),
    )
    .await
}

/// Apply pending public migrations, regardless of the connection's search_path.
/// Kryzhen tracks application per target schema and skips completed migrations.
pub async fn run_migrations(client: &mut Client) -> anyhow::Result<()> {
    let migrations = embedded_migrations()?;
    kryzhen::migrate(client, &migrations, Some("public"), false).await?;
    Ok(())
}

/// Apply the per-repo schema template (`migrations/repo/`) to `schema`.
/// Safe to call repeatedly — kryzhen tracks per-schema application, so an
/// already-up-to-date schema is a no-op and a schema missing only the newest
/// migration picks up just that one. This is what fixes the old
/// hand-rolled-`ALTER TABLE`-in-`register_repo` backfill gap: any call site
/// that touches a repo (not just first registration) can call this to bring
/// that repo's schema current.
///
/// Kryzhen creates the target application schema as part of applying a pending
/// migration. Each block and its application record commit in one transaction;
/// a later failure leaves earlier blocks committed for retry. AGE graph schemas
/// are managed separately through AGE's API.
pub async fn run_repo_migrations(client: &mut Client, schema: &str) -> anyhow::Result<()> {
    let migrations = embedded_repo_migrations()?;
    kryzhen::migrate(client, &migrations, Some(schema), false).await?;
    Ok(())
}

#[cfg(test)]
mod migration_tests {
    use super::{embedded_migrations, embedded_repo_migrations};
    use sha2::{Digest, Sha256};

    #[test]
    fn historical_files_remain_immutable() {
        for (contents, expected) in [
            (
                include_bytes!("../../../migrations/public/001_init.sql").as_slice(),
                "d6b3afd665da9f5d1df7c745896249ebbe38298693e507c554f160915f71d81a",
            ),
            (
                include_bytes!("../../../migrations/repo/001_chunks.sql").as_slice(),
                "c75635b98918fa12f08a2e219e8732873f4bb1f05c1677b5e19d240096659db8",
            ),
        ] {
            assert_eq!(format!("{:x}", Sha256::digest(contents)), expected);
        }
    }

    #[test]
    fn additive_blocks_follow_their_own_schema_history() {
        for (migrations, expected) in [
            (
                embedded_migrations().unwrap(),
                vec![
                    "init",
                    "public-family-identity",
                    "public-family-lifecycle",
                    "public-family-registration-intent",
                ],
            ),
            (
                embedded_repo_migrations().unwrap(),
                vec![
                    "repo-chunks",
                    "repo-checkout-registry",
                    "repo-checkout-observations",
                    "repo-family-policy",
                    "repo-worktree-file-deltas",
                    "repo-worktree-base-indexes",
                ],
            ),
        ] {
            let ordered = kryzhen::graph::topo_sort(migrations).unwrap();
            let names: Vec<_> = ordered.iter().map(|m| m.name.0.as_str()).collect();
            assert_eq!(
                names
                    .iter()
                    .copied()
                    .collect::<std::collections::BTreeSet<_>>(),
                expected.into_iter().collect()
            );
            for (index, migration) in ordered.iter().enumerate() {
                for dependency in &migration.requires {
                    assert!(ordered[..index]
                        .iter()
                        .any(|prior| prior.name == *dependency));
                }
            }
        }
    }

    #[test]
    fn embedded_sets_have_independent_dependency_graphs() {
        let public = embedded_migrations().expect("parse public migrations");
        let repo = embedded_repo_migrations().expect("parse repository template");

        for migrations in [&public, &repo] {
            assert!(!migrations.is_empty(), "embedded migration set is empty");
            kryzhen::validation::check_duplicate_names(migrations).unwrap();
            // Sorting each set independently rejects cross-set dependencies.
            kryzhen::graph::topo_sort(migrations.to_vec()).unwrap();
        }

        // Bodies/checksums are stored by name across all target schemas.
        let all: Vec<_> = public.into_iter().chain(repo).collect();
        kryzhen::validation::check_duplicate_names(&all).unwrap();
    }
}

/// Open a dedicated connection for LISTEN/NOTIFY.
/// Returns the `Client` (used for the LISTEN command) and a channel that
/// delivers notifications as they arrive. The connection is driven on a
/// spawned task for its lifetime.
pub async fn connect_listener(
    cfg: &DatabaseConfig,
) -> Result<(
    Client,
    mpsc::UnboundedReceiver<tokio_postgres::Notification>,
)> {
    let mut pg_cfg = make_pg_config(cfg);
    pg_cfg.application_name("muninn-index-listener");

    let (client, mut conn) = pg_cfg.connect(NoTls).await?;

    let (tx, rx) = mpsc::unbounded_channel();
    tokio::spawn(async move {
        loop {
            match std::future::poll_fn(|cx| conn.poll_message(cx)).await {
                Some(Ok(AsyncMessage::Notification(n))) => {
                    let _ = tx.send(n);
                }
                Some(Ok(_)) => {}
                Some(Err(e)) => {
                    tracing::warn!("listener connection error: {e}");
                    break;
                }
                None => break,
            }
        }
    });

    Ok((client, rx))
}

/// Open a dedicated `Client` for holding a PostgreSQL advisory lock.
/// The lock lives as long as the returned `Arc<Client>` has references.
/// When all references drop, the TCP connection closes and PostgreSQL frees
/// the lock automatically.
pub async fn connect_for_lock(cfg: &DatabaseConfig) -> Result<Arc<Client>> {
    let client = connect_internal(cfg, Some("muninn-advisory-lock")).await?;
    Ok(Arc::new(client))
}
