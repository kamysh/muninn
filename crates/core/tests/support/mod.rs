//! Connections to the identity-checked disposable persistence fixture only.
use anyhow::{ensure, Context, Result};
use serde::Deserialize;
use tokio_postgres::{Client, NoTls};

#[derive(Deserialize)]
struct Target {
    host: String,
    port: u16,
    database: String,
    user: String,
    password: String,
    run_id: String,
}

pub async fn connect() -> Result<Client> {
    let path = std::env::var_os("MUNINN_PERSISTENCE_TEST_CONFIG")
        .context("run through muninn-setup/test-all.sh; no live database fallback")?;
    let target: Target = serde_json::from_slice(&std::fs::read(path)?)?;
    ensure!(
        target.host == "127.0.0.1"
            && target.port == 5451
            && target.database == "muninn_persistence_test"
            && target.user == target.database,
        "refusing a database outside the disposable harness"
    );
    let mut config = tokio_postgres::Config::new();
    config
        .host(&target.host)
        .port(target.port)
        .dbname(&target.database)
        .user(&target.user)
        .password(&target.password)
        .connect_timeout(std::time::Duration::from_secs(5))
        .options("-c search_path=public,ag_catalog -c statement_timeout=60000");
    let (client, connection) = config.connect(NoTls).await?;
    tokio::spawn(connection);
    let identity = client
        .query_one(
            "SELECT current_database(), current_user, rolsuper, rolcreatedb, rolcreaterole FROM pg_roles WHERE rolname=current_user",
            &[],
        )
        .await?;
    ensure!(identity.get::<_, String>(0) == target.database);
    ensure!(identity.get::<_, String>(1) == target.user);
    ensure!(!identity.get::<_, bool>(2));
    ensure!(!identity.get::<_, bool>(3));
    ensure!(!identity.get::<_, bool>(4));
    ensure!(
        client
            .query_one("SELECT run_id FROM public.muninn_persistence_test_run", &[])
            .await?
            .get::<_, String>(0)
            == target.run_id,
        "disposable database ownership marker mismatch"
    );
    Ok(client)
}
