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
// include_dir! embeds all files recursively; we iterate .files() sorted by name.
//
// public/ — the static, single-schema migration chain (repos, knowledge,
// mcp_usage, ...), applied once via kryzhen::migrate(..., None, ...).
// repo/   — the per-repo schema template, applied once per repo via
// kryzhen::migrate(..., Some(schema), ...). See run_repo_migrations.
static PUBLIC_MIGRATIONS_DIR: Dir<'static> =
    include_dir!("$CARGO_MANIFEST_DIR/../../migrations/public");
static REPO_MIGRATIONS_DIR: Dir<'static> =
    include_dir!("$CARGO_MANIFEST_DIR/../../migrations/repo");

fn parse_migrations_dir(dir: &Dir<'static>) -> anyhow::Result<Vec<kryzhen::Migration>> {
    // Collect .sql files sorted by name (001_, 002_, … ordering).
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

fn embedded_repo_migrations() -> anyhow::Result<Vec<kryzhen::Migration>> {
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
            let mut builder = TlsConnector::builder();
            if matches!(mode, SslMode::Require) {
                builder.danger_accept_invalid_certs(true);
            }
            if let Some(path) = ssl_root_cert {
                let pem = std::fs::read(path)?;
                let cert = native_tls::Certificate::from_pem(&pem)?;
                builder.add_root_certificate(cert);
            }
            if let (Some(cert_path), Some(key_path)) = (ssl_client_cert, ssl_client_key) {
                let cert_pem = std::fs::read(cert_path)?;
                let key_pem = std::fs::read(key_path)?;
                let identity = native_tls::Identity::from_pkcs8(&cert_pem, &key_pem)?;
                builder.identity(identity);
            }
            let tls = MakeTlsConnector::new(builder.build()?);
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

/// Apply all pending migrations (embedded at compile time via include_dir!).
/// Safe to call repeatedly — kryzhen tracks applied migrations in its own table.
pub async fn run_migrations(client: &mut Client) -> anyhow::Result<()> {
    let migrations = embedded_migrations()?;
    kryzhen::migrate(client, &migrations, None, false).await?;
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
/// kryzhen's `migrate` does not create `schema` itself (verified: the only
/// `CREATE SCHEMA` in kryzhen is for its own `mallard` bookkeeping schema,
/// not the caller-supplied template target) — that looks like a gap in
/// kryzhen's own schema-templating feature, worth fixing upstream, but this
/// works around it here for now rather than blocking on that fix.
pub async fn run_repo_migrations(client: &mut Client, schema: &str) -> anyhow::Result<()> {
    client
        .execute(&format!(r#"CREATE SCHEMA IF NOT EXISTS "{schema}""#), &[])
        .await?;
    let migrations = embedded_repo_migrations()?;
    kryzhen::migrate(client, &migrations, Some(schema), false).await?;
    Ok(())
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
