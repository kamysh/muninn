//! First search of a linked checkout must register and publish it on demand.
use super::tools::{self, SearchContext, StructuralParams};
use anyhow::{ensure, Result};
use muninn_core::{
    config::GlobalConfig,
    db,
    embeddings::{EmbedFuture, EmbeddingBackend},
    store, worktrees,
};
use serde::Deserialize;
use std::{fs, path::Path, process::Command, sync::Arc};
use tokio_postgres::NoTls;
use uuid::Uuid;

#[derive(Deserialize)]
struct Target {
    host: String,
    port: u16,
    database: String,
    user: String,
    password: String,
    run_id: String,
    fixture_root: std::path::PathBuf,
}

struct Dummy;
impl EmbeddingBackend for Dummy {
    fn embed<'a>(&'a self, texts: &'a [String]) -> EmbedFuture<'a> {
        Box::pin(async move { Ok(texts.iter().map(|_| vec![1.0; 32]).collect()) })
    }
}

fn git(path: &Path, args: &[&str]) -> Result<()> {
    let result = Command::new("git")
        .current_dir(path)
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .env("GIT_CONFIG_GLOBAL", "/dev/null")
        .args(args)
        .output()?;
    ensure!(
        result.status.success(),
        "git failed: {}",
        String::from_utf8_lossy(&result.stderr)
    );
    Ok(())
}

#[tokio::test]
#[ignore = "requires the guarded disposable PostgreSQL harness"]
async fn first_structural_query_indexes_new_worktree() -> Result<()> {
    let config_path = std::env::var("MUNINN_PERSISTENCE_TEST_CONFIG")?;
    let target: Target = serde_json::from_slice(&fs::read(config_path)?)?;
    ensure!(
        target.host == "127.0.0.1"
            && target.port == 5451
            && target.database == "muninn_persistence_test"
            && target.user == target.database,
        "refusing a database outside the disposable harness"
    );
    let mut pg = tokio_postgres::Config::new();
    pg.host(&target.host)
        .port(target.port)
        .dbname(&target.database)
        .user(&target.user)
        .password(&target.password)
        .options("-c search_path=public,ag_catalog");
    let (mut client, connection) = pg.connect(NoTls).await?;
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
    db::run_migrations(&mut client).await?;

    let fixture = target
        .fixture_root
        .join(format!("first-query-{}", Uuid::new_v4()));
    let main = fixture.join("main");
    let linked = fixture.join("linked");
    fs::create_dir_all(&main)?;
    git(&main, &["init", "-b", "main"])?;
    git(&main, &["config", "user.name", "Fixture"])?;
    git(&main, &["config", "user.email", "fixture@example.invalid"])?;
    fs::write(main.join("a.rs"), "fn alpha() { beta(); }\nfn beta() {}\n")?;
    git(&main, &["add", "."])?;
    git(&main, &["commit", "-m", "base"])?;
    let repo = store::register_repo(&mut client, main.to_str().unwrap(), "fixture", 32).await?;
    let embedder: Arc<dyn EmbeddingBackend> = Arc::new(Dummy);
    worktrees::reconcile_family(
        &mut client,
        repo.id,
        &main,
        embedder.clone(),
        16,
        32,
        &[],
        &[],
        |_, _, _| {},
    )
    .await?;
    git(
        &main,
        &["worktree", "add", "-b", "linked", linked.to_str().unwrap()],
    )?;
    ensure!(worktrees::resolve(&client, &linked).await?.is_none());

    let mut config = GlobalConfig::default();
    config.database.host = target.host;
    config.database.port = target.port;
    config.database.dbname = target.database;
    config.database.user = target.user;
    let context = SearchContext {
        client: Arc::new(client),
        embedder,
        embedding_dim: 32,
        config,
        family_embedders: Default::default(),
        record_usage: false,
    };
    let response = tools::search_structural(
        &context,
        StructuralParams {
            symbol: "alpha".into(),
            relation: "callees".into(),
            repo: Some(linked.to_string_lossy().into_owned()),
            cwd: None,
        },
    )
    .await?;
    let symbols = response["symbols"].as_array().unwrap();
    ensure!(
        symbols.len() == 1
            && symbols[0]["name"] == "beta"
            && symbols[0]["file_path"]
                .as_str()
                .unwrap()
                .starts_with(linked.to_str().unwrap()),
        "first search returned the wrong checkout's structural results: {response}"
    );
    let resolved = worktrees::resolve(&context.client, &linked).await?.unwrap();
    let s = format!("\"{}\"", store::repo_schema(repo.id));
    let count: i64 = context
        .client
        .query_one(
            &format!("SELECT count(*) FROM {s}.checkout_structural_snapshots WHERE checkout=$1"),
            &[&resolved.checkout],
        )
        .await?
        .get(0);
    ensure!(
        count == 1,
        "first query did not publish a structural snapshot"
    );
    let mut client = Arc::try_unwrap(context.client)
        .map_err(|_| anyhow::anyhow!("test client is still shared"))?;
    store::delete_repo(&mut client, repo.id).await?;
    Ok(())
}
