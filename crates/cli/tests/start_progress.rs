//! Real CLI streaming checks. Only the identity-checked disposable DB is allowed.
use anyhow::{ensure, Context, Result};
use muninn_core::{config::GlobalConfig, db, store};
use serde_json::{json, Value};
use std::{path::Path, process::Stdio, time::Duration};
use tokio::{
    io::{AsyncBufReadExt, AsyncWriteExt, BufReader},
    process::Command,
};

fn cli() -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_muninn"));
    command.kill_on_drop(true);
    command
}

async fn json_command(args: &[&str], input: Option<Value>) -> Result<Value> {
    let mut child = cli()
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    if let Some(input) = input {
        child
            .stdin
            .take()
            .unwrap()
            .write_all(input.to_string().as_bytes())
            .await?;
    } else {
        drop(child.stdin.take());
    }
    let output = child.wait_with_output().await?;
    eprintln!(
        "JSON command {args:?}: {}",
        String::from_utf8_lossy(&output.stdout)
    );
    eprintln!("stderr: {}", String::from_utf8_lossy(&output.stderr));
    ensure!(output.status.success(), "CLI exited {}", output.status);
    ensure!(output.stderr.is_empty(), "JSON mode must not emit progress");
    // from_slice also rejects a second JSON document or trailing progress text.
    let document: Value = serde_json::from_slice(&output.stdout)?;
    ensure!(document["ok"] == true);
    Ok(document["data"].clone())
}

#[tokio::test]
#[ignore = "requires muninn-setup/test-start-progress.sh disposable fixture"]
async fn start_reports_live_wait_and_file_progress_without_changing_json() -> Result<()> {
    let target_path = std::env::var_os("MUNINN_PERSISTENCE_TEST_CONFIG")
        .context("use the disposable runner; no live database fallback")?;
    let target: Value = serde_json::from_slice(&std::fs::read(target_path)?)?;
    let cfg = GlobalConfig::load()?;
    ensure!(
        target["host"] == "127.0.0.1"
            && target["port"] == 5451
            && target["database"] == "muninn_persistence_test"
            && target["user"] == "muninn_persistence_test"
    );
    ensure!(
        cfg.database.host == "127.0.0.1"
            && cfg.database.port == 5451
            && cfg.database.dbname == "muninn_persistence_test"
            && cfg.database.user == "muninn_persistence_test"
            && cfg.database.dsn_override.is_none(),
        "CLI configuration is not the disposable target"
    );
    let mut client = db::connect(&cfg.database).await?;
    let row = client.query_one("SELECT current_database(), current_user, run_id FROM public.muninn_persistence_test_run", &[]).await?;
    ensure!(
        row.get::<_, String>(0) == "muninn_persistence_test"
            && row.get::<_, String>(1) == "muninn_persistence_test"
            && row.get::<_, String>(2)
                == target["run_id"].as_str().context("missing run identity")?
    );
    db::run_migrations(&mut client).await?;
    let fixtures = tempfile::tempdir_in(
        target["fixture_root"]
            .as_str()
            .context("missing fixture root")?,
    )?;

    for git in [false, true] {
        let root = fixtures.path().join(if git { "git" } else { "directory" });
        std::fs::create_dir(&root)?;
        if git {
            ensure!(Command::new("git")
                .args(["init", "--quiet"])
                .arg(&root)
                .status()
                .await?
                .success());
        }
        for name in ["first.rs", "second.rs"] {
            std::fs::write(root.join(name), "pub fn progress_fixture() -> u32 { 42 }\n")?;
        }
        let path = root.to_str().context("non UTF-8 test path")?;
        let added = json_command(
            &["add", path, "--json", "--input", "-"],
            Some(json!({
                "api_version": 1,
                "policy": {
                    "name": "start-progress-fixture",
                    "index": {"exclude": [], "vendor": ["**"]},
                    "watcher": {"debounce_ms": 300},
                    "embeddings": {"backend": "local", "model": null, "batch_size": 16}
                }
            })),
        )
        .await?;
        // All test sources are vendor files: real parsing/storage, no model downloads.
        let family = added["family_id"]
            .as_str()
            .context("missing family id")?
            .parse()?;
        let lock = store::try_lock(&cfg.database, family)
            .await?
            .context("unexpected fixture lock contention")?;
        let mut child = cli()
            .args(["start", "."])
            .current_dir(&root)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()?;
        let mut lines = BufReader::new(child.stderr.take().unwrap()).lines();
        let mut transcript = String::new();
        loop {
            let line = tokio::time::timeout(Duration::from_secs(20), lines.next_line())
                .await??
                .context("CLI ended without reporting its lock wait")?;
            eprintln!("plain CLI: {line}");
            transcript.push_str(&line);
            transcript.push('\n');
            if line.contains("waiting for the indexing lock") {
                break;
            }
        }
        ensure!(transcript.starts_with("Starting indexing for ."));
        ensure!(
            child.try_wait()?.is_none(),
            "wait was not observed on a running command"
        );
        ensure!(!transcript.contains("Processed ["));
        let waiting = json_command(&["config", path, "--json"], None).await?;
        ensure!(
            waiting["indexing_enabled"] == false,
            "wait must precede start authorization"
        );
        store::unlock(&lock, family).await?;
        while let Some(line) = lines.next_line().await? {
            eprintln!("plain CLI: {line}");
            transcript.push_str(&line);
            transcript.push('\n');
        }
        let output = child.wait_with_output().await?;
        eprintln!("plain stdout: {}", String::from_utf8_lossy(&output.stdout));
        ensure!(output.status.success());
        ensure!(transcript.contains("Processed [1/2]") && transcript.contains("Processed [2/2]"));
        ensure!(transcript.contains("first.rs") && transcript.contains("second.rs"));
        ensure!(String::from_utf8_lossy(&output.stdout).contains("Pass completed: true"));
        let count: i64 = client
            .query_one(
                &format!("SELECT count(*) FROM {}.chunks", store::repo_schema(family)),
                &[],
            )
            .await?
            .get(0);
        ensure!(
            count > 0,
            "index completion must include real stored chunks"
        );
        let started = json_command(&["start", path, "--json"], None).await?;
        ensure!(started["indexing_completed"] == true);
        let guarded = json_command(&["start", path, "--json", "--input", "-"], Some(json!({
            "api_version": 1, "expected_family_id": family, "expected_revision": added["revision"]
        }))).await?;
        ensure!(guarded["indexing_completed"] == true);
    }

    let absent = fixtures.path().join("not-registered");
    std::fs::create_dir(&absent)?;
    let failed = cli().arg("start").arg(Path::new(&absent)).output().await?;
    eprintln!(
        "failed CLI stderr: {}",
        String::from_utf8_lossy(&failed.stderr)
    );
    ensure!(!failed.status.success() && failed.stdout.is_empty());
    ensure!(String::from_utf8_lossy(&failed.stderr).contains("not_registered"));
    Ok(())
}
