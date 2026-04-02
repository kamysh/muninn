use sqlx::{PgPool, postgres::{PgConnectOptions, PgListener, PgPoolOptions, PgSslMode}};
use anyhow::Result;
use std::str::FromStr;

use crate::config::{DatabaseConfig, SslMode};

// search_path for all muninn connections:
//   public     — default schema; unqualified table creates land here
//   ag_catalog — needed for AGE operator resolution (agtype @>, etc.)
//
// Operator resolution requires ag_catalog to be in the path but NOT necessarily first.
// public must come first so that CREATE TABLE without schema qualification targets public,
// not ag_catalog (where muninn has no CREATE privilege).
const SEARCH_PATH: &str = "public,ag_catalog";

/// Connect using the given config.  Password is never stored in config —
/// sqlx reads it from ~/.pgpass after parsing the URL.
pub async fn connect(cfg: &DatabaseConfig) -> Result<PgPool> {
    connect_internal(cfg, None).await
}

/// Connect with an explicit application name shown in pg_stat_activity.
/// The provided name takes priority over `cfg.application_name`.
pub async fn connect_with_app_name(cfg: &DatabaseConfig, app_name: &str) -> Result<PgPool> {
    connect_internal(cfg, Some(app_name)).await
}

async fn connect_internal(cfg: &DatabaseConfig, override_app_name: Option<&str>) -> Result<PgPool> {
    // Build PgConnectOptions.  If dsn_override is set, use it for host/port/user/dbname;
    // otherwise build a properly-encoded URL so that ~/.pgpass lookup works correctly
    // (PgConnectOptions::from_str applies pgpass after parsing, unlike ::new() which
    // runs it at construction time before builder values take effect).
    let mut opts = if let Some(ref dsn) = cfg.dsn_override {
        PgConnectOptions::from_str(dsn)?
    } else {
        let url = pg_url(cfg)?;
        let mut o = PgConnectOptions::from_str(&url)?;

        if let Some(mode) = cfg.ssl_mode {
            o = o.ssl_mode(to_pg_ssl_mode(mode));
        }
        if let Some(ref path) = cfg.ssl_root_cert {
            o = o.ssl_root_cert(path);
        }
        if let Some(ref path) = cfg.ssl_client_cert {
            o = o.ssl_client_cert(path);
        }
        if let Some(ref path) = cfg.ssl_client_key {
            o = o.ssl_client_key(path);
        }

        o = o.statement_cache_capacity(1024);
        o
    };

    opts = opts.options([("search_path", SEARCH_PATH)]);

    let app_name = override_app_name.or(cfg.application_name.as_deref());
    if let Some(name) = app_name {
        opts = opts.application_name(name);
    }

    let max_connections = cfg.max_connections.unwrap_or(10);
    let mut pool_opts = PgPoolOptions::new().max_connections(max_connections);
    if let Some(secs) = cfg.connect_timeout {
        pool_opts = pool_opts.acquire_timeout(std::time::Duration::from_secs(secs));
    }

    Ok(pool_opts.connect_with(opts).await?)
}

/// Create a `PgListener` connected to the given database.
/// Uses a dedicated internal pool (max 2 connections) so the caller does not need to
/// manage a separate pool — PgListener clones the pool Arc internally.
pub async fn connect_listener(cfg: &DatabaseConfig) -> Result<PgListener> {
    let opts = pg_connect_options(cfg)?;
    let pool = PgPoolOptions::new()
        .max_connections(2)
        .connect_with(opts)
        .await?;
    let listener = PgListener::connect_with(&pool).await?;
    Ok(listener)
    // `pool` goes out of scope here, but PgListener clones the Arc<Pool> internally
    // and keeps it alive as long as the listener is alive.
}

/// Build a `PgConnectOptions` suitable for use with `PgListener`.
/// PgListener requires its own dedicated connection (cannot share the pool).
pub fn pg_connect_options(cfg: &DatabaseConfig) -> Result<PgConnectOptions> {
    let mut opts = if let Some(ref dsn) = cfg.dsn_override {
        PgConnectOptions::from_str(dsn)?
    } else {
        let url = pg_url(cfg)?;
        let mut o = PgConnectOptions::from_str(&url)?;
        if let Some(mode) = cfg.ssl_mode {
            o = o.ssl_mode(to_pg_ssl_mode(mode));
        }
        if let Some(ref path) = cfg.ssl_root_cert {
            o = o.ssl_root_cert(path);
        }
        if let Some(ref path) = cfg.ssl_client_cert {
            o = o.ssl_client_cert(path);
        }
        if let Some(ref path) = cfg.ssl_client_key {
            o = o.ssl_client_key(path);
        }
        o
    };
    opts = opts.options([("search_path", SEARCH_PATH)]);
    if let Some(name) = cfg.application_name.as_deref() {
        opts = opts.application_name(name);
    }
    Ok(opts)
}

/// Build a properly percent-encoded postgres:// URL from config fields.
/// No password: sqlx reads it from ~/.pgpass after URL parsing.
fn pg_url(cfg: &DatabaseConfig) -> Result<String> {
    let mut url = url::Url::parse("postgres://placeholder/placeholder")
        .expect("static URL is valid");
    url.set_username(&cfg.user)
        .map_err(|()| anyhow::anyhow!("invalid postgres username: {:?}", cfg.user))?;
    url.set_host(Some(&cfg.host))
        .map_err(|e| anyhow::anyhow!("invalid postgres host {:?}: {e}", cfg.host))?;
    url.set_port(Some(cfg.port))
        .map_err(|()| anyhow::anyhow!("invalid postgres port: {}", cfg.port))?;
    url.path_segments_mut()
        .map_err(|()| anyhow::anyhow!("cannot build URL path"))?
        .clear()
        .push(&cfg.dbname);
    Ok(url.to_string())
}

fn to_pg_ssl_mode(mode: SslMode) -> PgSslMode {
    match mode {
        SslMode::Disable    => PgSslMode::Disable,
        SslMode::Allow      => PgSslMode::Allow,
        SslMode::Prefer     => PgSslMode::Prefer,
        SslMode::Require    => PgSslMode::Require,
        SslMode::VerifyCa   => PgSslMode::VerifyCa,
        SslMode::VerifyFull => PgSslMode::VerifyFull,
    }
}