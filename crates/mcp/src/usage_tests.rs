//! Run only through the guarded disposable persistence harness.
use super::record_usage;
use anyhow::{ensure, Result};
use serde::Deserialize;

#[derive(Deserialize)]
struct Target {
    host: String,
    port: u16,
    database: String,
    user: String,
    password: String,
    run_id: String,
}

#[tokio::test]
#[ignore]
async fn records_usage_with_existing_integer_columns() -> Result<()> {
    let path = std::env::var("MUNINN_PERSISTENCE_TEST_CONFIG")?;
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
        .connect_timeout(std::time::Duration::from_secs(5));
    let (mut client, connection) = config.connect(tokio_postgres::NoTls).await?;
    tokio::spawn(connection);
    let identity = client
        .query_one(
            "SELECT current_database(), current_user, rolsuper FROM pg_roles WHERE rolname=current_user",
            &[],
        )
        .await?;
    ensure!(identity.get::<_, String>(0) == target.database);
    ensure!(identity.get::<_, String>(1) == target.user);
    ensure!(!identity.get::<_, bool>(2));
    ensure!(
        client
            .query_one("SELECT run_id FROM public.muninn_persistence_test_run", &[])
            .await?
            .get::<_, String>(0)
            == target.run_id
    );
    muninn_core::db::run_migrations(&mut client).await?;
    let types = client
        .query(
            "SELECT data_type FROM information_schema.columns WHERE table_schema='public' AND table_name='mcp_usage' AND column_name IN ('duration_ms', 'result_count')",
            &[],
        )
        .await?;
    ensure!(types.len() == 2);
    ensure!(types.iter().all(|row| row.get::<_, String>(0) == "integer"));

    record_usage(
        &client,
        "search_fulltext",
        Some("/fixture/repo"),
        12,
        Some(3),
    )
    .await?;
    record_usage(&client, "list_knowledge", None, 0, None).await?;
    let rows = client
        .query(
            "SELECT tool, repo_path, duration_ms, result_count FROM mcp_usage ORDER BY id",
            &[],
        )
        .await?;
    ensure!(rows.len() == 2);
    ensure!(rows[0].get::<_, String>(0) == "search_fulltext");
    ensure!(rows[0].get::<_, Option<String>>(1).as_deref() == Some("/fixture/repo"));
    ensure!(rows[0].get::<_, i32>(2) == 12);
    ensure!(rows[0].get::<_, Option<i32>>(3) == Some(3));
    ensure!(rows[1].get::<_, Option<String>>(1).is_none());
    ensure!(rows[1].get::<_, Option<i32>>(3).is_none());
    ensure!(record_usage(&client, "overflow", None, i64::MAX, Some(0))
        .await
        .is_err());
    ensure!(record_usage(&client, "overflow", None, 0, Some(i64::MAX))
        .await
        .is_err());
    let total: i64 = client
        .query_one(
            "SELECT COUNT(*) FROM mcp_usage WHERE ts >= now() - interval '30 days'",
            &[],
        )
        .await?
        .get(0);
    ensure!(total == 2);
    Ok(())
}
