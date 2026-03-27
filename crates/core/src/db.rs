use sqlx::{PgPool, postgres::PgPoolOptions};
use anyhow::Result;

pub async fn connect(dsn: &str) -> Result<PgPool> {
    let pool = PgPoolOptions::new()
        .max_connections(10)
        .connect(dsn)
        .await?;
    Ok(pool)
}