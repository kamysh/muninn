use super::*;
use muninn_core::family_policy::{self as policy, runtime};
use serde_json::Value;
use std::{
    path::{Path, PathBuf},
    time::Duration,
};

/// Only the guarded disposable harness may invoke this test.
#[tokio::test]
#[ignore]
async fn policy_dispatch() -> anyhow::Result<()> {
    let file =
        std::env::var_os("MUNINN_PERSISTENCE_TEST_CONFIG").expect("disposable fixture required");
    let target: Value = serde_json::from_slice(&std::fs::read(file)?)?;
    anyhow::ensure!(
        target["host"] == "127.0.0.1"
            && target["port"] == 5451
            && target["database"] == "muninn_persistence_test"
            && target["user"] == "muninn_persistence_test",
        "refusing non-test target"
    );
    let fixture = PathBuf::from(target["fixture_root"].as_str().unwrap());
    anyhow::ensure!(
        fixture.parent() == Some(Path::new("/var/tmp"))
            && fixture
                .file_name()
                .unwrap()
                .to_string_lossy()
                .starts_with("muninn-persistence-test-")
    );
    let credential_path = PathBuf::from(std::env::var_os("HOME").expect("HOME")).join(".pgpass");
    anyhow::ensure!(
        std::fs::read(credential_path)? == std::fs::read(fixture.join("client-pgpass"))?,
        "disposable credential mount required"
    );
    let mut cfg = GlobalConfig::default();
    cfg.database.host = "127.0.0.1".into();
    cfg.database.port = 5451;
    cfg.database.dbname = "muninn_persistence_test".into();
    cfg.database.user = "muninn_persistence_test".into();
    cfg.database.dsn_override = None;
    let mut client = db::connect(&cfg.database).await?;
    let row=client.query_one("SELECT current_database(),current_user,rolsuper,run_id FROM pg_roles CROSS JOIN public.muninn_persistence_test_run WHERE rolname=current_user",&[]).await?;
    anyhow::ensure!(
        row.get::<_, String>(0) == "muninn_persistence_test"
            && row.get::<_, String>(1) == "muninn_persistence_test"
            && !row.get::<_, bool>(2)
            && row.get::<_, String>(3) == target["run_id"].as_str().unwrap()
    );
    let root = fixture.join("daemon-directory");
    std::fs::create_dir(&root)?;
    let mut initial = policy::Policy::shipped("daemon fixture".into());
    initial.embeddings.backend = policy::Backend::Local;
    initial.embeddings.model = None;
    initial.index.exclude = vec!["*".into()];
    initial.watcher.debounce_ms = 10;
    let receipt = policy::registration::add(
        &mut client,
        || db::connect_for_preparation(&cfg.database),
        &root,
        Some(&policy::InitialRequest {
            api_version: 1,
            policy: initial.clone(),
        }),
    )
    .await?;
    let id: Uuid = receipt["family_id"].as_str().unwrap().parse()?;
    let mut watched = HashMap::new();
    let reindexing = Arc::new(Mutex::new(std::collections::HashSet::new()));
    scan_and_dispatch(&cfg, &mut client, &mut watched, &reindexing).await;
    assert!(!watched.contains_key(&id));
    assert!(!reindexing.lock().await.contains(&id));
    policy::start::authorize(
        &mut client,
        &root,
        &policy::start::Request {
            api_version: 1,
            expected_family_id: id,
            expected_revision: 1,
        },
        &cfg,
    )
    .await?;
    // Simulate an interrupted foreground start. The daemon must resume it.
    scan_and_dispatch(&cfg, &mut client, &mut watched, &reindexing).await;
    tokio::time::timeout(Duration::from_secs(10), async {
        loop {
            if client
                .query_one(
                    "SELECT indexed_at IS NOT NULL FROM public.repos WHERE id=$1",
                    &[&id],
                )
                .await?
                .get::<_, bool>(0)
                && !reindexing.lock().await.contains(&id)
            {
                break;
            }
            tokio::time::sleep(Duration::from_millis(20)).await;
        }
        Ok::<_, anyhow::Error>(())
    })
    .await??;
    scan_and_dispatch(&cfg, &mut client, &mut watched, &reindexing).await;
    assert!(watched.contains_key(&id));
    tokio::time::sleep(Duration::from_millis(150)).await;
    let before = client
        .query_one(
            "SELECT indexed_at::text FROM public.repos WHERE id=$1",
            &[&id],
        )
        .await?
        .get::<_, String>(0);
    std::fs::write(root.join("event.txt"), "")?;
    tokio::time::timeout(Duration::from_secs(10), async {
        loop {
            if client
                .query_one(
                    "SELECT indexed_at::text<>$2 FROM public.repos WHERE id=$1",
                    &[&id, &before],
                )
                .await?
                .get::<_, bool>(0)
            {
                break;
            }
            tokio::time::sleep(Duration::from_millis(20)).await;
        }
        Ok::<_, anyhow::Error>(())
    })
    .await??;
    let (listener, mut rx) = db::connect_listener(&cfg.database).await?;
    listener
        .batch_execute("LISTEN muninn_family_policy_changed")
        .await?;
    initial.watcher.debounce_ms = 35;
    policy::apply(
        &mut client,
        id,
        &policy::ApplyRequest {
            api_version: 1,
            expected_family_id: id,
            expected_revision: 1,
            acknowledge_reindex: false,
            policy: initial,
        },
    )
    .await?;
    assert!(tokio::time::timeout(Duration::from_secs(3), rx.recv())
        .await?
        .is_some());
    scan_and_dispatch(&cfg, &mut client, &mut watched, &reindexing).await;
    let signature = &watched.get(&id).unwrap().1;
    assert_eq!(signature.2, 35);
    assert_eq!(signature.4, Some(2));
    assert_eq!(runtime::policy(&client, id).await?.unwrap().revision, 2);
    for (_, (handle, _)) in watched.drain() {
        handle.abort();
        let _ = handle.await;
    }
    store::delete_repo(&mut client, id).await?;

    // A removed local repository is retired once, without dropping its schema.
    // A new clone/directory may then claim the same path with a new identity.
    let removed = fixture.join("daemon-removed-directory");
    std::fs::create_dir(&removed)?;
    let mut policy = policy::Policy::shipped("removed fixture".into());
    policy.embeddings.backend = policy::Backend::Local;
    policy.embeddings.model = None;
    policy.index.exclude = vec!["*".into()];
    let first = policy::registration::add(
        &mut client,
        || db::connect_for_preparation(&cfg.database),
        &removed,
        Some(&policy::InitialRequest {
            api_version: 1,
            policy: policy.clone(),
        }),
    )
    .await?;
    let first_id: Uuid = first["family_id"].as_str().unwrap().parse()?;
    std::fs::remove_dir(&removed)?;
    scan_and_dispatch(&cfg, &mut client, &mut watched, &reindexing).await;
    assert!(client
        .query_one(
            "SELECT missing_since IS NOT NULL AND retired_at IS NULL FROM public.repos WHERE id=$1",
            &[&first_id],
        )
        .await?
        .get::<_, bool>(0));
    std::fs::create_dir(&removed)?;
    scan_and_dispatch(&cfg, &mut client, &mut watched, &reindexing).await;
    assert!(client
        .query_one(
            "SELECT missing_since IS NULL AND retired_at IS NULL FROM public.repos WHERE id=$1",
            &[&first_id],
        )
        .await?
        .get::<_, bool>(0));
    std::fs::remove_dir(&removed)?;
    scan_and_dispatch(&cfg, &mut client, &mut watched, &reindexing).await;
    client
        .execute(
            "UPDATE public.repos SET missing_since=now()-interval '61 seconds' WHERE id=$1",
            &[&first_id],
        )
        .await?;
    scan_and_dispatch(&cfg, &mut client, &mut watched, &reindexing).await;
    assert!(client
        .query_one(
            "SELECT retired_at IS NOT NULL FROM public.repos WHERE id=$1",
            &[&first_id]
        )
        .await?
        .get::<_, bool>(0));
    assert!(store::list_repos(&client)
        .await?
        .iter()
        .all(|repo| repo.id != first_id));
    assert!(client
        .query_one(
            "SELECT to_regnamespace($1) IS NOT NULL",
            &[&store::repo_schema(first_id)],
        )
        .await?
        .get::<_, bool>(0));
    std::fs::create_dir(&removed)?;
    let second = policy::registration::add(
        &mut client,
        || db::connect_for_preparation(&cfg.database),
        &removed,
        Some(&policy::InitialRequest {
            api_version: 1,
            policy,
        }),
    )
    .await?;
    let second_id: Uuid = second["family_id"].as_str().unwrap().parse()?;
    assert_ne!(first_id, second_id);
    assert_eq!(
        store::get_repo_by_path(&client, &removed.to_string_lossy())
            .await?
            .unwrap()
            .id,
        second_id
    );
    store::delete_repo(&mut client, second_id).await?;
    store::delete_repo(&mut client, first_id).await?;
    println!("daemon: no automatic first start; interrupted explicit start resumed; directory file event reconciled; policy notification and watcher restart verified");
    Ok(())
}
