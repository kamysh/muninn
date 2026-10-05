use super::*;
use muninn_core::family_policy::{self as policy, Defaults, Policy};
use serde_json::{json, Value};

fn snapshot(registered: bool) -> Value {
    json!({"family_id":if registered {Some("01234567-89ab-cdef-0123-456789abcdef")}else{None},
        "revision":if registered {Some(1)}else{None}, "policy":Policy::shipped("Fixture".into()),
        "defaults":Defaults::shipped(),"indexing_enabled":false,"paused":false,
        "checkout":{"paused":false},"preflight":{"advice":"start","complete":true}})
}
#[test]
fn native_rules_preserve_order_validate_and_invalidate_inventory() {
    let mut draft = Draft::new(snapshot(false)).unwrap();
    draft.edit(Field::AddExclude, "build/".into()).unwrap();
    draft
        .edit(Field::AddExclude, "!build/keep.rs".into())
        .unwrap();
    assert!(draft.checked.is_none());
    draft.selected = draft
        .fields()
        .iter()
        .position(|f| *f == Field::Exclude(1))
        .unwrap();
    draft.move_rule(true);
    assert_eq!(draft.policy.index.exclude, ["!build/keep.rs", "build/"]);
    draft.remove();
    assert_eq!(draft.policy.index.exclude, ["build/"]);
    let before = draft.policy.clone();
    assert!(draft.edit(Field::Debounce, "-1".into()).is_err());
    assert!(draft.edit(Field::Batch, "0".into()).is_err());
    assert!(draft.edit(Field::AddExclude, "[".into()).is_err());
    assert_eq!(draft.policy, before);
    draft.edit(Field::Backend, "local".into()).unwrap();
    assert_eq!(draft.policy.embeddings.model, None);
    let mut existing = Draft::new(snapshot(true)).unwrap();
    assert!(existing.edit(Field::Backend, "local".into()).is_err());
}
#[test]
fn reviewing_conflicts_never_silently_rebases_a_draft() {
    let mut draft = Draft::new(snapshot(true)).unwrap();
    draft.edit(Field::Name, "My draft".into()).unwrap();
    let mut latest = snapshot(true);
    latest["revision"] = json!(2);
    latest["policy"]["name"] = json!("Concurrent edit");
    report_error(
        &mut draft,
        crate::readonly::error("revision_conflict", "stale revision"),
    );
    draft.receive_latest(latest);
    assert_eq!(draft.request()["expected_revision"], 1);
    assert_eq!(draft.policy.name, "My draft");
    draft.keep_draft_on_latest().unwrap();
    assert_eq!(draft.request()["expected_revision"], 2);
    assert_eq!(draft.policy.name, "My draft");
    assert!(draft.checked.is_none());
    let mut replacement = snapshot(true);
    replacement["family_id"] = json!(uuid::Uuid::new_v4());
    draft.receive_latest(replacement);
    assert!(draft.keep_draft_on_latest().is_err());
    assert_eq!(draft.request()["expected_revision"], 2);
}
#[test]
fn long_rules_and_terminal_controls_remain_inspectable() {
    assert_eq!(visible("a\x1b[31m\nb"), "a\\u{1b}[31m\\nb");
    let source = "日本語".repeat(50) + "\x1b";
    let wrapped = wrap_lines(vec![source.clone()], 20);
    assert_eq!(wrapped.concat(), visible(&source));
    assert!(wrapped.iter().all(|s| console::measure_text_width(s) <= 20));
    let chars: Vec<_> = source.chars().collect();
    let window = edit_window(&chars, chars.len(), 30);
    assert!(window.contains('|'));
    assert!(console::measure_text_width(&window) <= 30);
    assert_eq!(shell_path(Path::new("/a'b")), "'/a'\\''b'");
    #[cfg(unix)]
    {
        use std::os::unix::ffi::OsStrExt;
        assert_eq!(
            shell_path(Path::new(std::ffi::OsStr::from_bytes(b"a\xff\n"))),
            "$'\\x61\\xff\\x0a'"
        );
    }
}

struct Fake {
    value: Value,
    saves: usize,
}
impl Backend for Fake {
    async fn start(&mut self, _: &Draft) -> policy::Result<Value> {
        self.value["indexing_enabled"] = json!(true);
        Ok(
            json!({"indexing_enabled":true,"indexing_completed":true,"skipped_checkouts_or_files":0}),
        )
    }
    async fn load(&mut self) -> policy::Result<Value> {
        Ok(self.value.clone())
    }
    async fn check(&mut self, draft: &Draft) -> policy::Result<Value> {
        let mut value = self.value.clone();
        value["policy"] = json!(draft.policy);
        Ok(value)
    }
    async fn save(&mut self, draft: &Draft) -> policy::Result<Value> {
        self.saves += 1;
        self.value["policy"] = json!(draft.policy);
        self.value["revision"] = json!(2);
        Ok(self.value.clone())
    }
}

/// Invoked by the real PTY test below, never by the disposable DB runner.
#[tokio::test]
#[ignore]
async fn terminal_session() {
    let scenario = std::env::var("MUNINN_TUI_PTY_CHILD").expect("PTY child only");
    let screen = Screen::enter(Term::stdout()).unwrap();
    let mut backend = Fake {
        value: snapshot(true),
        saves: 0,
    };
    drive(&screen.0, &mut backend, Path::new("/fixture"), false)
        .await
        .unwrap();
    drop(screen);
    match scenario.as_str() {
        "save" | "start" => {
            assert_eq!(backend.saves, 1);
            assert_eq!(backend.value["policy"]["name"], "Edited");
        }
        "cancel" | "interrupt" => assert_eq!(backend.saves, 0),
        _ => panic!("unknown scenario"),
    }
    assert_eq!(backend.value["indexing_enabled"], scenario == "start");
}

#[test]
#[cfg(target_os = "linux")]
fn pseudoterminal_save_cancel_and_terminal_restoration() {
    use std::{
        io::{Read, Write},
        process::{Command, Stdio},
        sync::mpsc,
        time::{Duration, Instant},
    };
    for scenario in ["save", "start", "cancel", "interrupt"] {
        let executable = shell_path(&std::env::current_exe().unwrap());
        let command=format!("stty cols 80 rows 24; before=$(stty -g); timeout --foreground --kill-after=1s 15s {executable} --exact tui::tests::terminal_session --ignored --nocapture; result=$?; after=$(stty -g); if [ \"$before\" = \"$after\" ]; then echo TERMIOS_RESTORED; else exit 99; fi; exit $result");
        let mut child = Command::new("script")
            .args(["-q", "-e", "-c", &command, "/dev/null"])
            .env("MUNINN_TUI_PTY_CHILD", scenario)
            .env("TERM", "xterm-256color")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()
            .unwrap();
        let mut output = child.stdout.take().unwrap();
        let (tx, rx) = mpsc::channel();
        let reader = std::thread::spawn(move || {
            let mut chunk = [0; 4096];
            while let Ok(n) = output.read(&mut chunk) {
                if n == 0 {
                    break;
                }
                if tx.send(chunk[..n].to_vec()).is_err() {
                    break;
                }
            }
        });
        let mut transcript = Vec::new();
        let mut await_text = |needle: &str| {
            let deadline = Instant::now() + Duration::from_secs(8);
            while !String::from_utf8_lossy(&transcript).contains(needle) {
                let part = rx
                    .recv_timeout(deadline.saturating_duration_since(Instant::now()))
                    .unwrap_or_else(|error| {
                        panic!(
                            "PTY waiting for {needle:?}: {error}; transcript: {}",
                            String::from_utf8_lossy(&transcript)
                        )
                    });
                transcript.extend(part);
            }
            // The screen is flushed just before switching into the key reader.
            std::thread::sleep(Duration::from_millis(75));
        };
        let input = child.stdin.as_mut().unwrap();
        await_text("1 Policy");
        input.write_all(b"\r").unwrap();
        await_text("Edit Name");
        input.write_all(b"\x15Edited\r").unwrap();
        await_text("[unsaved draft]");
        if scenario == "save" || scenario == "start" {
            input.write_all(b"s").unwrap();
            await_text("SAVE CONFIGURATION?");
            input.write_all(b"\r").unwrap();
            await_text("START INDEXING THIS FAMILY?");
            if scenario == "start" {
                input.write_all(b"\r").unwrap();
                await_text("Indexing enabled. Pass completed: true");
            }
            input.write_all(b"q").unwrap();
        } else if scenario == "interrupt" {
            input.write_all(b"\x03").unwrap();
        } else {
            input.write_all(b"q").unwrap();
            await_text("Discard unsaved draft");
            input.write_all(b"\r").unwrap();
        }
        let deadline = Instant::now() + Duration::from_secs(10);
        let status = loop {
            if let Some(status) = child.try_wait().unwrap() {
                break status;
            }
            if Instant::now() > deadline {
                child.kill().unwrap();
                panic!("PTY failed to exit");
            }
            std::thread::sleep(Duration::from_millis(20));
        };
        reader.join().unwrap();
        for part in rx.try_iter() {
            transcript.extend(part);
        }
        let text = String::from_utf8_lossy(&transcript);
        assert!(status.success(), "{text}");
        assert!(text.contains("TERMIOS_RESTORED"));
        assert!(text.contains("\x1b[?1049h"));
        assert!(text.contains("\x1b[?25h\x1b[?1049l"));
    }
}

/// Run only through the disposable harness; never loads global configuration.
#[tokio::test]
#[ignore]
async fn persistence() -> anyhow::Result<()> {
    use muninn_core::{family_store::PreparationConnection, store};
    use std::{fs, path::PathBuf, process::Command};
    use tokio_postgres::NoTls;
    let filename = std::env::var_os("MUNINN_PERSISTENCE_TEST_CONFIG")
        .expect("explicit disposable target required");
    let target: Value = serde_json::from_slice(&fs::read(filename)?)?;
    anyhow::ensure!(
        target["host"] == "127.0.0.1"
            && target["port"] == 5451
            && target["database"] == "muninn_persistence_test"
            && target["user"] == "muninn_persistence_test",
        "refusing non-test endpoint"
    );
    let fixture_root = PathBuf::from(target["fixture_root"].as_str().unwrap());
    anyhow::ensure!(
        fixture_root.parent() == Some(Path::new("/tmp"))
            && fixture_root
                .file_name()
                .unwrap()
                .to_string_lossy()
                .starts_with("muninn-persistence-test-")
    );
    let mut connection_config = tokio_postgres::Config::new();
    connection_config
        .host("127.0.0.1")
        .port(5451)
        .dbname("muninn_persistence_test")
        .user("muninn_persistence_test")
        .password(target["password"].as_str().unwrap())
        .connect_timeout(std::time::Duration::from_secs(5))
        .options(
            "-c search_path=public,ag_catalog -c statement_timeout=15000 -c lock_timeout=5000",
        );
    let (client, connection) = connection_config.connect(NoTls).await?;
    tokio::spawn(async move {
        let _ = connection.await;
    });
    let row=client.query_one("SELECT current_database(),current_user,rolsuper,rolcreatedb,rolcreaterole FROM pg_roles WHERE rolname=current_user",&[]).await?;
    anyhow::ensure!(
        row.get::<_, String>(0) == "muninn_persistence_test"
            && row.get::<_, String>(1) == "muninn_persistence_test"
            && !row.get::<_, bool>(2)
            && !row.get::<_, bool>(3)
            && !row.get::<_, bool>(4)
    );
    let run_id = target["run_id"].as_str().unwrap().to_owned();
    anyhow::ensure!(
        client
            .query_one("SELECT run_id FROM public.muninn_persistence_test_run", &[])
            .await?
            .get::<_, String>(0)
            == run_id
    );
    let prepare = move || {
        let config = connection_config.clone();
        let run_id = run_id.clone();
        async move {
            let (client, mut connection) = config.connect(NoTls).await?;
            tokio::select! {
                result=client.query_one("SELECT run_id FROM public.muninn_persistence_test_run",&[])=>anyhow::ensure!(result?.get::<_,String>(0)==run_id),
                result=&mut connection=>{result?;anyhow::bail!("test preparation connection closed");}
            }
            let token = client.cancel_token();
            Ok(PreparationConnection::new(client, connection, async move {
                token.cancel_query(NoTls).await
            }))
        }
    };
    let fixtures = tempfile::tempdir_in(&fixture_root)?;
    let root = fixtures.path().join("repo");
    fs::create_dir(&root)?;
    let git = |args: &[&str]| -> anyhow::Result<()> {
        let output = Command::new("git")
            .arg("-C")
            .arg(&root)
            .args(args)
            .output()?;
        anyhow::ensure!(
            output.status.success(),
            "fixture git failed: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        Ok(())
    };
    git(&["init", "-b", "main"])?;
    git(&[
        "-c",
        "user.name=Fixture",
        "-c",
        "user.email=fixture@example.invalid",
        "commit",
        "--allow-empty",
        "-m",
        "fixture",
    ])?;
    fs::write(root.join("main.rs"), "fn main() {}\n")?;
    fs::create_dir(root.join("bulk"))?;
    fs::write(root.join("bulk/generated.rs"), "generated")?;
    let mut config = GlobalConfig::from_toml_str(GlobalConfig::template_content())?;
    config.database.host = "127.0.0.1".into();
    config.database.port = 5451;
    config.database.dbname = "muninn_persistence_test".into();
    config.database.user = "muninn_persistence_test".into();
    config.database.dsn_override = None;
    let credential_path = PathBuf::from(std::env::var_os("HOME").expect("HOME")).join(".pgpass");
    anyhow::ensure!(
        fs::read(credential_path)? == fs::read(fixture_root.join("client-pgpass"))?,
        "disposable credential mount required"
    );
    let mut backend = Database {
        client,
        config,
        path: root.clone(),
        add_mode: true,
        prepare,
    };
    let count_before: i64 = backend
        .client
        .query_one("SELECT count(*) FROM public.repos", &[])
        .await?
        .get(0);
    let mut draft = Draft::new(backend.load().await?)?;
    assert!(draft.family_id().is_none());
    draft.edit(Field::Name, "TUI fixture".into())?;
    draft.edit(Field::Backend, "local".into())?;
    draft.edit(Field::AddExclude, "bulk/".into())?;
    let check = backend.check(&draft).await?;
    assert_eq!(check["preflight"]["tier1"]["files"], 1);
    assert_eq!(
        backend
            .client
            .query_one("SELECT count(*) FROM public.repos", &[])
            .await?
            .get::<_, i64>(0),
        count_before,
        "opening/editing/checking must not register"
    );
    let saved = backend.save(&draft).await?;
    assert_eq!(saved["policy"]["name"], "TUI fixture");
    assert_eq!(saved["revision"], 1);
    assert_eq!(saved["indexing_enabled"], false);
    draft = Draft::new(saved)?;
    let id = draft.family_id().unwrap();
    let schema = store::repo_schema(id);
    assert_eq!(
        backend
            .client
            .query_one(&format!("SELECT count(*) FROM \"{schema}\".chunks"), &[])
            .await?
            .get::<_, i64>(0),
        0
    );
    assert!(!root.join(".muninn.toml").exists());
    // A concurrent JSON edit makes both check and save reject the stale guard.
    backend.add_mode = false;
    let mut concurrent: policy::ApplyRequest = serde_json::from_value(draft.request())?;
    concurrent.policy.name = "Concurrent JSON edit".into();
    policy::apply_path(&mut backend.client, &root, &concurrent).await?;
    draft.edit(Field::Name, "Retained TUI draft".into())?;
    assert_eq!(
        backend.check(&draft).await.unwrap_err().code,
        "revision_conflict"
    );
    let error = backend.save(&draft).await.unwrap_err();
    assert_eq!(error.code, "revision_conflict");
    assert_eq!(
        backend.start(&draft).await.unwrap_err().code,
        "revision_conflict"
    );
    assert!(!backend.client.query_one("SELECT preempt_requested OR indexing_enabled_at IS NOT NULL FROM public.repos WHERE id=$1", &[&id]).await?.get::<_,bool>(0));
    report_error(&mut draft, error);
    assert_eq!(draft.revision(), Some(1));
    assert_eq!(draft.policy.name, "Retained TUI draft");
    draft.receive_latest(backend.load().await?);
    assert_eq!(draft.revision(), Some(1));
    draft.keep_draft_on_latest()?;
    assert_eq!(draft.revision(), Some(2));
    backend.check(&draft).await?;
    draft = Draft::new(backend.save(&draft).await?)?;
    assert_eq!(draft.revision(), Some(3));
    assert_eq!(
        backend.load().await?["policy"]["name"],
        "Retained TUI draft"
    );
    assert_eq!(backend.save(&draft).await?["changed"], false);
    // Add a checkout to the existing family without copying policy or starting.
    let linked = fixtures.path().join("linked");
    git(&["worktree", "add", "-b", "linked", linked.to_str().unwrap()])?;
    backend.path = linked;
    backend.add_mode = true;
    let linked_draft = Draft::new(backend.load().await?)?;
    assert_eq!(linked_draft.family_id(), Some(id));
    assert!(linked_draft.base["checkout_id"].is_null());
    let linked_receipt = backend.save(&linked_draft).await?;
    assert!(!linked_receipt["checkout_id"].is_null());
    assert!(linked_receipt.get("registration_error").is_none());
    assert_eq!(linked_receipt["revision"], 3);
    assert_eq!(linked_receipt["indexing_enabled"], false);
    assert_eq!(
        backend
            .client
            .query_one(&format!("SELECT count(*) FROM \"{schema}\".checkouts"), &[])
            .await?
            .get::<_, i64>(0),
        2
    );
    assert_eq!(
        backend
            .client
            .query_one("SELECT count(*) FROM public.repos", &[])
            .await?
            .get::<_, i64>(0),
        count_before + 1
    );
    assert!(!backend.path.join(".muninn.toml").exists());
    let mut start_draft = Draft::new(backend.load().await?)?;
    start_draft.edit(Field::AddExclude, "*".into())?;
    start_draft = Draft::new(backend.save(&start_draft).await?)?;
    assert_eq!(
        backend.check(&start_draft).await?["preflight"]["tier1"]["files"],
        0
    );
    let started = backend.start(&start_draft).await?;
    assert_eq!(started["indexing_enabled"], true);
    assert_eq!(started["indexing_completed"], true);
    assert_eq!(backend.load().await?["indexing_enabled"], true);
    assert_eq!(
        backend
            .client
            .query_one(
                &format!("SELECT count(*) FROM {schema}.checkouts WHERE indexed_at IS NOT NULL"),
                &[]
            )
            .await?
            .get::<_, i64>(0),
        2
    );
    println!("TUI persistence: read-only open/check, registration, CAS conflict/review, no-op save, worktree association, save without indexing, and explicit foreground start verified");
    Ok(())
}
