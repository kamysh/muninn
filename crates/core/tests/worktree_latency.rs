//! Run only through the disposable PostgreSQL harness with a focused verifier.
use anyhow::{ensure, Context, Result};
use muninn_core::{
    db,
    embeddings::{EmbedFuture, EmbeddingBackend},
    store,
    types::StructuralRelation,
    worktrees,
};
use serde::Deserialize;
use std::{fs, path::Path, process::Command, sync::Arc, time::Instant};
use tokio_postgres::NoTls;

#[derive(Deserialize)]
struct TestTarget {
    host: String,
    port: u16,
    database: String,
    user: String,
    password: String,
    fixture_root: std::path::PathBuf,
}

struct Dummy;
impl EmbeddingBackend for Dummy {
    fn embed<'a>(&'a self, texts: &'a [String]) -> EmbedFuture<'a> {
        Box::pin(async move { Ok(texts.iter().map(|_| vec![1.0; 32]).collect()) })
    }
}

fn git(root: &Path, args: &[&str]) -> Result<()> {
    let output = Command::new("git")
        .current_dir(root)
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .env("GIT_CONFIG_GLOBAL", "/dev/null")
        .args(args)
        .output()?;
    ensure!(
        output.status.success(),
        "git: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    Ok(())
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
#[ignore = "requires the disposable PostgreSQL harness and intentionally measures a large fixture"]
async fn worktree_latency() -> Result<()> {
    let _ = tracing_subscriber::fmt()
        .with_max_level(tracing::Level::INFO)
        .with_test_writer()
        .try_init();
    let config = std::env::var_os("MUNINN_PERSISTENCE_TEST_CONFIG")
        .context("run through muninn-setup/test-persistence.sh")?;
    let target: TestTarget = serde_json::from_slice(&fs::read(config)?)?;
    ensure!(
        target.host == "127.0.0.1"
            && target.port == 5451
            && target.database == "muninn_persistence_test"
            && target.user == target.database,
        "refusing non-disposable database"
    );
    let mut cfg = tokio_postgres::Config::new();
    cfg.host(&target.host)
        .port(target.port)
        .dbname(&target.database)
        .user(&target.user)
        .password(&target.password)
        .options("-c search_path=public,ag_catalog -c statement_timeout=60000");
    let (mut client, connection) = cfg.connect(NoTls).await?;
    tokio::spawn(async move {
        let _ = connection.await;
    });
    db::run_migrations(&mut client).await?;

    let fixture = tempfile::tempdir_in(&target.fixture_root)?;
    let main = fixture.path().join("main");
    let identical = fixture.path().join("identical");
    let child = fixture.path().join("child");
    fs::create_dir(&main)?;
    git(&main, &["init", "-b", "main"])?;
    git(&main, &["config", "user.name", "Fixture"])?;
    git(&main, &["config", "user.email", "fixture@example.invalid"])?;
    fs::write(main.join("anchor.rs"), "pub fn anchor() {}\n")?;
    for n in 0..4_000 {
        let body = if n < 1_600 { "anchor();" } else { "" };
        fs::write(
            main.join(format!("file_{n:04}.rs")),
            format!("pub fn f_{n:04}() {{ {body} }}\n"),
        )?;
    }
    git(&main, &["add", "."])?;
    git(&main, &["commit", "-m", "base"])?;
    let repo = store::register_repo(&mut client, main.to_str().unwrap(), "latency", 32).await?;
    let base_start = Instant::now();
    let embedder: Arc<dyn EmbeddingBackend> = Arc::new(Dummy);
    worktrees::reconcile_family(
        &mut client,
        repo.id,
        &main,
        embedder.clone(),
        32,
        32,
        &[],
        &[],
        |_, _, _| {},
    )
    .await?;
    println!("base_index_ms={}", base_start.elapsed().as_millis());

    git(
        &main,
        &[
            "worktree",
            "add",
            "-b",
            "identical",
            identical.to_str().unwrap(),
        ],
    )?;
    let identical_start = Instant::now();
    worktrees::reconcile_requested_checkout(
        &mut client,
        repo.id,
        &main,
        &identical,
        embedder.clone(),
        32,
        32,
        &[],
        &[],
    )
    .await?;
    println!(
        "identical_worktree_index_ms={}",
        identical_start.elapsed().as_millis()
    );

    git(
        &main,
        &["worktree", "add", "-b", "child", child.to_str().unwrap()],
    )?;
    for n in 0..170 {
        let body = "let _value = 1;\n".repeat(160);
        fs::write(
            child.join(format!("file_{n:04}.rs")),
            format!("pub fn f_{n:04}() {{ anchor();\n{body}}}\n"),
        )?;
    }
    let start = Instant::now();
    worktrees::reconcile_requested_checkout(
        &mut client,
        repo.id,
        &main,
        &child,
        embedder,
        32,
        32,
        &[],
        &[],
    )
    .await?;
    println!("changed_worktree_index_ms={}", start.elapsed().as_millis());
    let target = worktrees::resolve(&client, &child)
        .await?
        .context("child not indexed")?;
    let related =
        worktrees::query_related(&client, &target, "anchor", StructuralRelation::Calls, true)
            .await?;
    ensure!(
        !related.is_empty(),
        "missing callers after first publication"
    );
    ensure!(
        related
            .iter()
            .all(|symbol| symbol.file_path.starts_with(child.to_str().unwrap())),
        "wrong checkout path"
    );
    store::delete_repo(&mut client, repo.id).await?;
    Ok(())
}
