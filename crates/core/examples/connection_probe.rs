//! Exercised by tests/database-connections.py against a disposable server.
use anyhow::{ensure, Result};
use muninn_core::{config::GlobalConfig, db};
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<()> {
    let path = std::env::args().nth(1).expect("config path");
    let cfg = GlobalConfig::from_toml_str(&std::fs::read_to_string(path)?)?;
    let mode = std::env::args().nth(2).unwrap_or_else(|| "query".into());
    let client = db::connect(&cfg.database).await?;
    let ssl: bool = client
        .query_one(
            "SELECT ssl FROM pg_stat_ssl WHERE pid=pg_backend_pid()",
            &[],
        )
        .await?
        .get(0);
    match mode.as_str() {
        "listener" => {
            let (listener, mut notifications) = db::connect_listener(&cfg.database).await?;
            ensure!(
                listener
                    .query_one(
                        "SELECT ssl FROM pg_stat_ssl WHERE pid=pg_backend_pid()",
                        &[]
                    )
                    .await?
                    .get::<_, bool>(0)
                    == ssl
            );
            listener.batch_execute("LISTEN connection_test").await?;
            client
                .batch_execute("NOTIFY connection_test, 'received'")
                .await?;
            let notification = tokio::time::timeout(Duration::from_secs(5), notifications.recv())
                .await?
                .expect("notification");
            ensure!(notification.payload() == "received");
        }
        "lock" => {
            let lock = db::connect_for_lock(&cfg.database).await?;
            ensure!(
                lock.query_one(
                    "SELECT ssl FROM pg_stat_ssl WHERE pid=pg_backend_pid()",
                    &[]
                )
                .await?
                .get::<_, bool>(0)
                    == ssl
            );
            lock.batch_execute("SELECT pg_advisory_lock(123456789)")
                .await?;
        }
        "preparation" => {
            // Hold the actual preparation lock so dropping the preparer must
            // cancel a server-side wait, before it can apply any migrations.
            client
                .execute("SELECT pg_advisory_lock($1,$2)", &[&0x4d554e49_i32, &2_i32])
                .await?;
            let preparation = db::connect_for_preparation(&cfg.database).await?;
            let task = tokio::spawn(preparation.prepare_public());
            let pid = tokio::time::timeout(Duration::from_secs(5), async {
                loop {
                    if let Some(row) = client.query_opt("SELECT a.pid,s.ssl FROM pg_stat_activity a JOIN pg_stat_ssl s USING(pid) WHERE application_name='muninn-family-preparation' AND wait_event_type='Lock'", &[]).await? {
                        ensure!(row.get::<_, bool>(1) == ssl);
                        break Ok::<i32, anyhow::Error>(row.get(0));
                    }
                    tokio::time::sleep(Duration::from_millis(20)).await;
                }
            }).await??;
            task.abort();
            let _ = task.await;
            tokio::time::timeout(Duration::from_secs(5), async {
                while client
                    .query_one(
                        "SELECT EXISTS(SELECT 1 FROM pg_stat_activity WHERE pid=$1)",
                        &[&pid],
                    )
                    .await?
                    .get::<_, bool>(0)
                {
                    tokio::time::sleep(Duration::from_millis(20)).await;
                }
                Ok::<_, anyhow::Error>(())
            })
            .await??;
        }
        "query" => (),
        _ => anyhow::bail!("unknown connection path"),
    }
    println!("ssl={ssl}");
    Ok(())
}
