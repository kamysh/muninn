//! Invoke only through muninn-setup/test-persistence.sh. No global DB fallback.
use anyhow::{ensure, Context, Result};
use muninn_core::{
    db, family_store::*, graph, repo_resolver::GitOperationState, search, store, types::*,
};
use serde::Deserialize;
use std::{
    fs,
    io::Write,
    path::{Path, PathBuf},
    process::Command,
};
use tokio_postgres::{error::SqlState, Client, NoTls};
use uuid::Uuid;

#[derive(Deserialize)]
struct Target {
    host: String,
    port: u16,
    database: String,
    user: String,
    password: String,
    run_id: String,
    fixture_root: PathBuf,
}
impl Target {
    fn config(&self) -> Result<tokio_postgres::Config> {
        ensure!(
            self.host == "127.0.0.1"
                && self.port == 5451
                && self.database == "muninn_persistence_test"
                && self.user == self.database,
            "refusing any endpoint outside the disposable test target"
        );
        let mut config = tokio_postgres::Config::new();
        config
            .host(&self.host)
            .port(self.port)
            .dbname(&self.database)
            .user(&self.user)
            .password(&self.password)
            .application_name("muninn-persistence-test")
            .connect_timeout(std::time::Duration::from_secs(5))
            .options(
                "-c search_path=public,ag_catalog -c statement_timeout=15000 -c lock_timeout=5000",
            );
        Ok(config)
    }
    async fn preparation(&self) -> Result<PreparationConnection> {
        let (client, mut connection) = self.config()?.connect(NoTls).await?;
        // Drive the connection during validation, then transfer both halves.
        // No detached driver can outlive cancellation of the coordinator.
        tokio::select! {
            result = self.validate(&client) => result?,
            result = &mut connection => { result?; anyhow::bail!("connection closed during validation"); }
        }
        let token = client.cancel_token();
        Ok(PreparationConnection::new(client, connection, async move {
            token.cancel_query(NoTls).await
        }))
    }
    async fn connect(&self) -> Result<Client> {
        let (client, connection) = self.config()?.connect(NoTls).await?;
        tokio::spawn(async move {
            if let Err(e) = connection.await {
                eprintln!("test connection: {e}");
            }
        });
        self.validate(&client).await?;
        Ok(client)
    }
    async fn validate(&self, client: &Client) -> Result<()> {
        let row = client.query_one("SELECT current_database(), current_user, rolsuper, rolcreatedb, rolcreaterole FROM pg_roles WHERE rolname=current_user", &[]).await?;
        ensure!(row.get::<_, String>(0) == self.database && row.get::<_, String>(1) == self.user);
        ensure!(!row.get::<_, bool>(2) && !row.get::<_, bool>(3) && !row.get::<_, bool>(4));
        ensure!(
            client
                .query_one("SHOW server_version_num", &[])
                .await?
                .get::<_, String>(0)
                == "160011"
        );
        for (name, version) in [("age", "1.6.0"), ("vector", "0.8.1"), ("pgcrypto", "1.3")] {
            ensure!(
                client
                    .query_one(
                        "SELECT extversion FROM pg_extension WHERE extname=$1",
                        &[&name]
                    )
                    .await?
                    .get::<_, String>(0)
                    == version
            );
        }
        ensure!(
            client
                .query_one("SELECT run_id FROM public.muninn_persistence_test_run", &[])
                .await?
                .get::<_, String>(0)
                == self.run_id
        );
        Ok(())
    }
    fn record(&self, id: Uuid) -> Result<()> {
        let mut file = fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(self.fixture_root.join("families.jsonl"))?;
        writeln!(
            file,
            "{}",
            serde_json::json!({"family":id,"schema":store::repo_schema(id),"graph":store::graph_name(id)})
        )?;
        Ok(())
    }
}
fn git(path: &Path, args: &[&str]) -> Result<()> {
    let out = Command::new("git")
        .current_dir(path)
        .args(args)
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .env("GIT_CONFIG_GLOBAL", "/dev/null")
        .output()?;
    ensure!(
        out.status.success(),
        "git failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    Ok(())
}
fn historical(text: &str) -> Result<Vec<kryzhen::Migration>> {
    Ok(kryzhen::file::apply_implicit_deps(
        kryzhen::parser::parse_file(text, "historical.sql")?,
    ))
}
async fn count(client: &Client, sql: &str) -> Result<i64> {
    Ok(client.query_one(sql, &[]).await?.get(0))
}
async fn rejected(client: &Client, sql: &str, code: &SqlState) -> Result<()> {
    let error = client
        .batch_execute(sql)
        .await
        .expect_err("invalid SQL fixture unexpectedly accepted");
    ensure!(
        error.code() == Some(code),
        "unexpected constraint error: {error:?}"
    );
    Ok(())
}
async fn import_fixture(client: &Client, id: Uuid, identity: &CheckoutIdentity) -> Result<()> {
    client
        .execute(
            "UPDATE public.repos SET family_kind=$2,path_encoding=$3,family_key=$4 WHERE id=$1",
            &[
                &id,
                &identity.family.kind.as_str(),
                &identity.family.key.encoding(),
                &identity.family.key.bytes(),
            ],
        )
        .await?;
    Ok(())
}
// Fixture setup only: the runtime preparation coordinator is deliberately not implemented here.
async fn ready_fixture(client: &Client, id: Uuid) -> Result<()> {
    let schema = store::repo_schema(id);
    let graph = store::graph_name(id);
    ensure!(
        client
            .query_one(
                "SELECT count(*) FROM mallard.applied_migration_schemas WHERE schema=$1",
                &[&schema]
            )
            .await?
            .get::<_, i64>(0)
            >= 4
    );
    ensure!(client.query_one("SELECT EXISTS(SELECT 1 FROM ag_catalog.ag_graph g JOIN pg_namespace n ON n.oid=g.namespace WHERE g.name=$1 AND n.nspname=$1)", &[&graph]).await?.get::<_,bool>(0));
    client
        .execute(
            "UPDATE public.repos SET schema_state='ready',schema_error=NULL WHERE id=$1",
            &[&id],
        )
        .await?;
    Ok(())
}
async fn create_graph(client: &Client, id: Uuid) -> Result<()> {
    client
        .batch_execute(&format!(
            "SELECT ag_catalog.create_graph('{}')",
            store::graph_name(id)
        ))
        .await?;
    Ok(())
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
#[ignore = "requires explicit disposable container runner; never uses global configuration"]
async fn family_persistence() -> Result<()> {
    let config = std::env::var_os("MUNINN_PERSISTENCE_TEST_CONFIG")
        .context("use muninn-setup/test-persistence.sh")?;
    let target: Target = serde_json::from_slice(&fs::read(config)?)?;
    let mut client = target.connect().await?;
    ensure!(
        count(
            &client,
            "SELECT count(*) FROM pg_tables WHERE schemaname='public'"
        )
        .await?
            == 1
    );
    ensure!(count(&client, "SELECT count(*) FROM ag_catalog.ag_graph").await? == 0);
    let fixtures = tempfile::tempdir_in(&target.fixture_root)?;
    let main = fixtures.path().join("main");
    let linked = fixtures.path().join("linked\ncheckout");
    let detached = fixtures.path().join("detached");
    fs::create_dir(&main)?;
    git(&main, &["init", "-b", "main"])?;
    git(
        &main,
        &[
            "-c",
            "user.name=Fixture",
            "-c",
            "user.email=fixture@example.invalid",
            "commit",
            "--allow-empty",
            "-m",
            "fixture",
        ],
    )?;
    git(
        &main,
        &["worktree", "add", "-b", "linked", linked.to_str().unwrap()],
    )?;
    git(
        &main,
        &["worktree", "add", "--detach", detached.to_str().unwrap()],
    )?;
    let main_identity = CheckoutIdentity::discover(&main).await?;
    let linked_identity = CheckoutIdentity::discover(&linked).await?;
    let detached_identity = CheckoutIdentity::discover(&detached).await?;
    assert_eq!(main_identity.family, linked_identity.family);
    assert_eq!(main_identity.family, detached_identity.family);
    let old_public = historical(include_str!("../../../migrations/public/001_init.sql"))?;
    let old_repo = historical(include_str!("../../../migrations/repo/001_chunks.sql"))?;
    kryzhen::migrate(&mut client, &old_public, Some("public"), false).await?;
    let legacy_id = Uuid::new_v4();
    target.record(legacy_id)?;
    client.execute("INSERT INTO repos(id,path,name,embedding_dim,paused,ever_indexed) VALUES($1,$2,'legacy',64,true,true)", &[&legacy_id,&main.to_str().unwrap()]).await?;
    let legacy_schema = store::repo_schema(legacy_id);
    kryzhen::migrate(&mut client, &old_repo, Some(&legacy_schema), false).await?;
    create_graph(&client, legacy_id).await?;
    let chunk = Chunk {
        id: Uuid::new_v4(),
        repo_id: legacy_id,
        file_path: "sentinel.rs".into(),
        range: LineRange { start: 1, end: 1 },
        content: "persistence sentinel".into(),
        embedding: Some(vec![0.25; 64]),
        tier: Tier::Tier1,
        embedding_state: EmbeddingState::Embedded,
        content_hash: Some(vec![7; 32]),
    };
    store::upsert_chunk(&client, &chunk).await?;
    client.batch_execute(&format!("SELECT * FROM ag_catalog.cypher('{}', $$ CREATE (:Function {{name: 'sentinel', chunk_id: '{}'}}) $$) AS (v ag_catalog.agtype)",store::graph_name(legacy_id),chunk.id)).await?;
    assert_eq!(
        graph::all_symbol_chunk_ids(&client, legacy_id)
            .await?
            .get("sentinel"),
        Some(&chunk.id)
    );
    println!("Historical fixture seeded through Kryzhen and AGE API");
    let old_schema_request = muninn_core::family_policy::ApplyRequest {
        api_version: 1,
        expected_family_id: legacy_id,
        expected_revision: 1,
        acknowledge_reindex: false,
        policy: muninn_core::family_policy::Policy::shipped("fixture".into()),
    };
    assert_eq!(
        muninn_core::family_policy::apply_path(&mut client, &main, &old_schema_request)
            .await
            .unwrap_err()
            .code,
        "schema_not_ready"
    );

    // The actual read-command service refuses old storage without migrating it.
    assert_eq!(
        muninn_core::family_policy::readonly::query(
            &mut client,
            &main,
            muninn_core::family_policy::readonly::Operation::Inspect,
            None
        )
        .await
        .unwrap_err()
        .code,
        "schema_not_ready"
    );
    assert_eq!(count(&client, "SELECT count(*) FROM information_schema.columns WHERE table_schema='public' AND table_name='repos'").await?, 8);

    db::run_migrations(&mut client).await?;
    db::run_repo_migrations(&mut client, &legacy_schema).await?;
    let before = count(
        &client,
        "SELECT count(*) FROM mallard.applied_migration_schemas",
    )
    .await?;
    db::run_migrations(&mut client).await?;
    db::run_repo_migrations(&mut client, &legacy_schema).await?;
    assert_eq!(
        before,
        count(
            &client,
            "SELECT count(*) FROM mallard.applied_migration_schemas"
        )
        .await?
    );
    let family = get_family(&client, legacy_id).await?.unwrap();
    assert!(family.identity.is_none() && family.paused && family.indexing_enabled_at.is_none());
    assert_eq!(family.storage_generation, StorageGeneration::Legacy);
    assert_eq!(family.schema_state, SchemaState::Pending);
    for assignment in [
        "family_kind='git'",
        "schema_state='ready'",
        "storage_generation='snapshots'",
        "indexing_enable_origin='explicit-start'",
    ] {
        rejected(
            &client,
            &format!("UPDATE repos SET {assignment} WHERE id='{legacy_id}'"),
            &SqlState::CHECK_VIOLATION,
        )
        .await?;
    }
    assert!(reserve_family(
        &mut client,
        &linked_identity,
        linked.to_str().unwrap(),
        "duplicate",
        64
    )
    .await
    .unwrap_err()
    .to_string()
    .contains("unresolved legacy"));
    assert_eq!(count(&client, "SELECT count(*) FROM repos").await?, 1);
    import_fixture(&client, legacy_id, &main_identity).await?;
    ready_fixture(&client, legacy_id).await?;
    let main_checkout = register_checkout(&mut client, legacy_id, &main_identity).await?;
    let linked_checkout = register_checkout(&mut client, legacy_id, &linked_identity).await?;
    let detached_checkout = register_checkout(&mut client, legacy_id, &detached_identity).await?;
    assert_ne!(main_checkout.token.id, linked_checkout.token.id);
    assert_ne!(linked_checkout.token.id, detached_checkout.token.id);
    assert_eq!(linked_checkout.root.to_path_buf()?, linked.canonicalize()?);
    assert_eq!(linked_checkout.git_state, ObservedGitState::Unknown);
    assert!(linked_checkout.observed_at.is_none());
    assert_eq!(
        count(&client, "SELECT count(*) FROM ag_catalog.ag_graph").await?,
        1
    );
    assert_eq!(
        count(
            &client,
            &format!("SELECT count(*) FROM {}.chunks", legacy_schema)
        )
        .await?,
        1
    );
    assert_eq!(
        search::fulltext_search(&client, "sentinel", legacy_id, 10).await?[0]
            .chunk
            .id,
        chunk.id
    );
    let row = client
        .query_one(
            &format!(
                "SELECT content_hash, embedding::text FROM {}.chunks WHERE id=$1",
                legacy_schema
            ),
            &[&chunk.id],
        )
        .await?;
    assert_eq!(row.get::<_, Vec<u8>>(0), vec![7; 32]);
    assert_eq!(
        row.get::<_, String>(1),
        format!("[{}]", vec!["0.25"; 64].join(","))
    );
    assert_eq!(
        graph::all_symbol_chunk_ids(&client, legacy_id)
            .await?
            .get("sentinel"),
        Some(&chunk.id)
    );
    // The unchanged legacy registration path still uses ON CONFLICT(path).
    assert_eq!(
        store::register_repo(&mut client, main.to_str().unwrap(), "legacy renamed", 64)
            .await?
            .id,
        legacy_id
    );
    assert!(
        store::register_repo(&mut client, main.to_str().unwrap(), "legacy renamed", 32)
            .await
            .is_err()
    );
    println!("Legacy data, vectors, AGE graph, path upsert, and migration replay preserved");

    let mut other = target.connect().await?;
    let directory = fixtures.path().join("directory");
    fs::create_dir(&directory)?;
    let directory_identity = CheckoutIdentity::discover(&directory).await?;
    let (a, b) = tokio::join!(
        reserve_family(
            &mut client,
            &directory_identity,
            directory.to_str().unwrap(),
            "directory",
            64
        ),
        reserve_family(
            &mut other,
            &directory_identity,
            directory.to_str().unwrap(),
            "directory",
            64
        )
    );
    let directory_family = a?;
    assert_eq!(directory_family.id, b?.id);
    target.record(directory_family.id)?;
    assert!(
        register_checkout(&mut client, directory_family.id, &directory_identity)
            .await
            .is_err()
    );
    assert!(directory_family.indexing_enabled_at.is_none());
    let schema = store::repo_schema(directory_family.id);
    // Fail a separate, unchanged test suffix after the production blocks commit.
    client.batch_execute("CREATE TABLE public.persistence_retry_gate(value integer NOT NULL); INSERT INTO public.persistence_retry_gate VALUES(0)").await?;
    let repo_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../migrations/repo");
    let mut migrations = kryzhen::file::load_dir(&repo_dir)?;
    let production_count = migrations.len() as i64;
    let production_dependencies = migrations.iter().map(|m| m.name.clone()).collect();
    let body = "SELECT 1 / value FROM public.persistence_retry_gate;";
    migrations.push(kryzhen::Migration {
        name: kryzhen::MigrationName("persistence-test-retry".into()),
        description: "Test-only retry gate".into(),
        requires: production_dependencies,
        script: body.into(),
        checksum: kryzhen::checksum(body),
    });
    assert!(
        kryzhen::migrate(&mut client, &migrations, Some(&schema), false)
            .await
            .is_err()
    );
    assert_eq!(
        client
            .query_one(
                "SELECT count(*) FROM mallard.applied_migration_schemas WHERE schema=$1",
                &[&schema]
            )
            .await?
            .get::<_, i64>(0),
        production_count
    );
    assert_eq!(
        get_family(&client, directory_family.id)
            .await?
            .unwrap()
            .schema_state,
        SchemaState::Pending
    );
    assert!(
        register_checkout(&mut client, directory_family.id, &directory_identity)
            .await
            .is_err()
    );
    client
        .batch_execute("UPDATE public.persistence_retry_gate SET value=1")
        .await?;
    let report = kryzhen::migrate(&mut client, &migrations, Some(&schema), false).await?;
    assert_eq!(report.applied, vec!["persistence-test-retry"]);
    assert!(
        kryzhen::migrate(&mut client, &migrations, Some(&schema), false)
            .await?
            .applied
            .is_empty()
    );
    create_graph(&client, directory_family.id).await?;
    ready_fixture(&client, directory_family.id).await?;
    let (a, b) = tokio::join!(
        register_checkout(&mut client, directory_family.id, &directory_identity),
        register_checkout(&mut other, directory_family.id, &directory_identity)
    );
    let directory_checkout = a?;
    assert_eq!(directory_checkout.token, b?.token);
    assert_ne!(directory_family.id, legacy_id);
    assert!(
        register_checkout(&mut client, legacy_id, &directory_identity)
            .await
            .is_err()
    );
    assert_eq!(
        count(&client, "SELECT count(*) FROM ag_catalog.ag_graph").await?,
        2
    );
    assert_eq!(count(&client,"SELECT count(*) FROM mallard.applied_migration_schemas WHERE migration_name='repo-checkout-observations'").await?,2);
    assert_eq!(count(&client,"SELECT count(*) FROM mallard.applied_migration_schemas WHERE schema LIKE 'code_graph_%'").await?,0);
    println!("Concurrent reservation/registration and committed migration failure/retry verified");

    let token = linked_checkout.token;
    for state in [
        ObservedGitState::Known(GitOperationState {
            merge: false,
            rebase_merge: false,
            rebase_apply: false,
            unmerged_index: false,
        }),
        ObservedGitState::Known(GitOperationState {
            merge: true,
            rebase_merge: false,
            rebase_apply: false,
            unmerged_index: true,
        }),
        ObservedGitState::Unknown,
    ] {
        let observation = CheckoutObservation {
            availability: Availability::Available,
            git_state: state,
            error: None,
        };
        assert!(record_checkout_observation(&client, legacy_id, token, &observation).await?);
        assert_eq!(
            lookup_checkout(&client, legacy_id, &linked_identity.root)
                .await?
                .unwrap()
                .checkout
                .git_state,
            state
        );
    }
    let unavailable = CheckoutObservation {
        availability: Availability::Unavailable,
        git_state: ObservedGitState::Unknown,
        error: Some("fixture unavailable".into()),
    };
    assert!(record_checkout_observation(&client, legacy_id, token, &unavailable).await?);
    let current = invalidate_checkout(&client, legacy_id, token)
        .await?
        .unwrap();
    assert_eq!(current.dirty_generation, token.dirty_generation + 1);
    assert!(!record_checkout_observation(&client, legacy_id, token, &unavailable).await?);
    assert!(invalidate_checkout(&client, legacy_id, token)
        .await?
        .is_none());
    let wrong = CheckoutToken {
        incarnation: Uuid::new_v4(),
        ..current
    };
    assert!(!record_checkout_observation(&client, legacy_id, wrong, &unavailable).await?);
    assert!(invalidate_checkout(&client, legacy_id, wrong)
        .await?
        .is_none());
    let nongit = CheckoutObservation {
        availability: Availability::Available,
        git_state: ObservedGitState::NotGit,
        error: None,
    };
    assert!(
        record_checkout_observation(
            &client,
            directory_family.id,
            directory_checkout.token,
            &nongit
        )
        .await?
    );
    assert!(!record_checkout_observation(&client, legacy_id, current, &nongit).await?);
    let table = format!("{}.checkouts", legacy_schema);
    for assignment in [
        "dirty_generation=-1",
        "git_state='clear'",
        "registration_state='retired'",
        "merge_in_progress=false",
    ] {
        rejected(
            &client,
            &format!("UPDATE {table} SET {assignment} WHERE id='{}'", token.id),
            &SqlState::CHECK_VIOLATION,
        )
        .await?;
    }
    rejected(
        &client,
        &format!(
            "INSERT INTO {table}(root,git_dir) SELECT root,git_dir FROM {table} WHERE id='{}'",
            token.id
        ),
        &SqlState::UNIQUE_VIOLATION,
    )
    .await?;
    client.execute(&format!("UPDATE {table} SET registration_state='suppressed',dirty_generation=dirty_generation+1 WHERE id=$1"),&[&token.id]).await?;
    let suppressed = register_checkout(&mut client, legacy_id, &linked_identity).await?;
    assert_eq!(suppressed.registration_state, RegistrationState::Suppressed);
    assert_eq!(suppressed.token.id, token.id);
    assert!(
        !record_checkout_observation(&client, legacy_id, suppressed.token, &unavailable).await?
    );
    assert!(invalidate_checkout(&client, legacy_id, suppressed.token)
        .await?
        .is_none());
    client
        .execute(
            &format!(
                "UPDATE {table} SET registration_state='retired',retired_at=now() WHERE id=$1"
            ),
            &[&token.id],
        )
        .await?;
    let replacement = register_checkout(&mut client, legacy_id, &linked_identity).await?;
    assert_ne!(replacement.token.incarnation, token.incarnation);
    assert!(
        !record_checkout_observation(&client, legacy_id, suppressed.token, &unavailable).await?
    );
    assert_eq!(
        count(
            &client,
            &format!("SELECT count(*) FROM {table} WHERE registration_state='retired'")
        )
        .await?,
        1
    );
    assert_eq!(
        count(
            &client,
            &format!("SELECT count(*) FROM {legacy_schema}.chunks")
        )
        .await?,
        1
    );
    assert_eq!(
        graph::all_symbol_chunk_ids(&client, legacy_id).await?.len(),
        1
    );
    println!(
        "Observation constraints, suppression, retirement, and stale token rejection verified"
    );

    // Independent non-Git family, including native bytes that cannot be UTF-8.
    #[cfg(unix)]
    let extra_path = {
        use std::os::unix::ffi::OsStringExt;
        fixtures
            .path()
            .join(std::ffi::OsString::from_vec(b"directory-\xff\n".to_vec()))
    };
    #[cfg(not(unix))]
    let extra_path = fixtures.path().join("directory-extra");
    fs::create_dir(&extra_path)?;
    let extra_identity = CheckoutIdentity::discover(&extra_path).await?;
    let extra = reserve_family(
        &mut client,
        &extra_identity,
        "fixture display path",
        "extra",
        32,
    )
    .await?;
    target.record(extra.id)?;
    assert_ne!(extra.id, directory_family.id);
    db::run_repo_migrations(&mut client, &store::repo_schema(extra.id)).await?;
    create_graph(&client, extra.id).await?;
    ready_fixture(&client, extra.id).await?;
    register_checkout(&mut client, extra.id, &extra_identity).await?;
    let loaded = lookup_checkout(&client, extra.id, &extra_identity.root)
        .await?
        .unwrap();
    assert_eq!(
        loaded.checkout.root.to_path_buf()?,
        extra_path.canonicalize()?
    );
    assert_eq!(loaded.family.identity.unwrap(), extra_identity.family);
    assert_eq!(
        count(&client, "SELECT count(*) FROM ag_catalog.ag_graph").await?,
        3
    );
    assert_eq!(count(&client,"SELECT count(*) FROM mallard.applied_migration_schemas WHERE migration_name='repo-checkout-observations'").await?,3);
    assert_eq!(count(&client,"SELECT count(*) FROM mallard.applied_migration_schemas WHERE schema LIKE 'code_graph_%'").await?,0);
    println!("Independent directory families and lossless native path persistence verified");
    coordinator_verification(&target, &mut client, fixtures.path(), legacy_id).await?;
    policy_verification(&target, &mut client, fixtures.path()).await?;
    registration_verification(&target, &mut client, fixtures.path()).await?;
    worktree_runtime::verify(&target, &mut client, fixtures.path()).await?;
    policy_runtime::verify(&target, &mut client, fixtures.path()).await?;
    Ok(())
}

async fn reserve_fixture(
    target: &Target,
    client: &mut Client,
    root: &Path,
    name: &str,
) -> Result<Uuid> {
    let path = root.join(name);
    fs::create_dir(&path)?;
    let identity = CheckoutIdentity::discover(&path).await?;
    let family = reserve_family(client, &identity, path.to_str().unwrap(), name, 64).await?;
    target.record(family.id)?;
    Ok(family.id)
}
async fn wait_for(client: &Client, query: &str) -> Result<()> {
    tokio::time::timeout(std::time::Duration::from_secs(3), async {
        loop {
            if client.query_one(query, &[]).await?.get::<_, bool>(0) {
                return Ok::<_, anyhow::Error>(());
            }
            tokio::time::sleep(std::time::Duration::from_millis(10)).await;
        }
    })
    .await
    .with_context(|| format!("test observation deadline: {query}"))??;
    Ok(())
}
async fn coordinator_verification(
    target: &Target,
    client: &mut Client,
    root: &Path,
    legacy: Uuid,
) -> Result<()> {
    // Public bootstrap/replay and family preparations use the same session lock.
    target.preparation().await?.prepare_public().await?;
    let sentinel = graph::all_symbol_chunk_ids(client, legacy).await?;
    let family = target
        .preparation()
        .await?
        .prepare_family(legacy, GraphRequirement::Existing)
        .await?;
    assert_eq!(family.schema_state, SchemaState::Ready);
    assert_eq!(graph::all_symbol_chunk_ids(client, legacy).await?, sentinel);
    assert!(family.indexing_enabled_at.is_none() && family.paused);

    let id = reserve_fixture(target, client, root, "coordinator-new").await?;
    let (a, b) = (target.preparation().await?, target.preparation().await?);
    let (a, b) = tokio::join!(
        a.prepare_family(id, GraphRequirement::NewReservation),
        b.prepare_family(id, GraphRequirement::NewReservation)
    );
    assert_eq!(a?.id, b?.id);
    assert_eq!(
        get_family(client, id).await?.unwrap().schema_state,
        SchemaState::Ready
    );
    assert_eq!(
        client
            .query_one(
                "SELECT count(*) FROM ag_catalog.ag_graph WHERE name=$1",
                &[&store::graph_name(id)]
            )
            .await?
            .get::<_, i64>(0),
        1
    );
    println!("Coordinator revalidation preserves legacy graph; concurrent preparation shares one schema/graph pair");

    // Existing-family mode must not manufacture a missing graph.
    let missing = reserve_fixture(target, client, root, "coordinator-missing-legacy").await?;
    assert!(target
        .preparation()
        .await?
        .prepare_family(missing, GraphRequirement::Existing)
        .await
        .is_err());
    let failed = get_family(client, missing).await?.unwrap();
    assert_eq!(failed.schema_state, SchemaState::Failed);
    assert_eq!(
        failed.schema_error.as_deref(),
        Some("AGE graph preparation or mapping validation failed")
    );
    assert!(!client
        .query_one(
            "SELECT EXISTS(SELECT 1 FROM ag_catalog.ag_graph WHERE name=$1)",
            &[&store::graph_name(missing)]
        )
        .await?
        .get::<_, bool>(0));
    // Explicit fixture repair via AGE, then retry in existing-family mode.
    create_graph(client, missing).await?;
    target
        .preparation()
        .await?
        .prepare_family(missing, GraphRequirement::Existing)
        .await?;

    // Test-only conflicting table after the historical block. All application
    // schemas are still created through Kryzhen, never manually.
    let sql_failure = reserve_fixture(target, client, root, "coordinator-sql-failure").await?;
    let schema = store::repo_schema(sql_failure);
    let mut fixture_migrations =
        historical(include_str!("../../../migrations/repo/001_chunks.sql"))?;
    let body = "CREATE TABLE checkouts (fixture_conflict boolean);";
    fixture_migrations.push(kryzhen::Migration {
        name: kryzhen::MigrationName("persistence-test-conflict".into()),
        description: "Test-only conflicting prerequisite".into(),
        requires: vec![kryzhen::MigrationName("repo-chunks".into())],
        script: body.into(),
        checksum: kryzhen::checksum(body),
    });
    kryzhen::migrate(client, &fixture_migrations, Some(&schema), false).await?;
    assert!(target
        .preparation()
        .await?
        .prepare_family(sql_failure, GraphRequirement::NewReservation)
        .await
        .is_err());
    assert_eq!(
        get_family(client, sql_failure)
            .await?
            .unwrap()
            .schema_error
            .as_deref(),
        Some("application migration preparation failed")
    );
    assert_eq!(client.query_one("SELECT count(*) FROM mallard.applied_migration_schemas WHERE schema=$1 AND migration_name='repo-chunks'",&[&schema]).await?.get::<_,i64>(0),1);
    client
        .batch_execute(&format!("DROP TABLE {schema}.checkouts"))
        .await?;
    target
        .preparation()
        .await?
        .prepare_family(sql_failure, GraphRequirement::NewReservation)
        .await?;

    // Block the AGE catalog to force a real AGE-read failure after all app
    // migrations have committed. No production template is altered.
    let age_failure = reserve_fixture(target, client, root, "coordinator-age-failure").await?;
    let mut blocker = target.connect().await?;
    let tx = blocker.transaction().await?;
    tx.batch_execute("LOCK TABLE ag_catalog.ag_graph IN ACCESS EXCLUSIVE MODE")
        .await?;
    assert!(target
        .preparation()
        .await?
        .prepare_family(age_failure, GraphRequirement::NewReservation)
        .await
        .is_err());
    assert_eq!(
        get_family(client, age_failure).await?.unwrap().schema_state,
        SchemaState::Failed
    );
    assert_eq!(client.query_one("SELECT count(*) FROM mallard.applied_migration_schemas WHERE schema=$1 AND migration_name='repo-checkout-observations'",&[&store::repo_schema(age_failure)]).await?.get::<_,i64>(0),1);
    tx.rollback().await?;
    target
        .preparation()
        .await?
        .prepare_family(age_failure, GraphRequirement::NewReservation)
        .await?;
    assert!(get_family(client, age_failure)
        .await?
        .unwrap()
        .schema_error
        .is_none());
    println!("Coordinator persists migration/AGE failures, refuses missing legacy graph, and retries committed work");

    // Cancellation after migrating is committed must close the driver/socket,
    // release the session lock, and retain a retryable non-ready registry row.
    let canceled = reserve_fixture(target, client, root, "coordinator-canceled").await?;
    let preparation = target.preparation().await?;
    let tx = blocker.transaction().await?;
    tx.batch_execute("LOCK TABLE ag_catalog.ag_graph IN ACCESS EXCLUSIVE MODE")
        .await?;
    let job = tokio::spawn(preparation.prepare_family(canceled, GraphRequirement::NewReservation));
    wait_for(
        client,
        &format!("SELECT schema_state='migrating' FROM repos WHERE id='{canceled}'"),
    )
    .await?;
    wait_for(client,"SELECT EXISTS(SELECT 1 FROM pg_locks WHERE locktype='advisory' AND classid=1297436233 AND objid=2 AND objsubid=2 AND granted)").await?;
    wait_for(client,"SELECT EXISTS(SELECT 1 FROM pg_stat_activity a JOIN pg_locks l ON l.pid=a.pid WHERE l.locktype='advisory' AND l.classid=1297436233 AND l.objid=2 AND l.objsubid=2 AND l.granted AND a.wait_event_type='Lock' AND a.query LIKE '%ag_catalog.ag_graph%')").await?;
    job.abort();
    assert!(job.await.unwrap_err().is_cancelled());
    wait_for(client,"SELECT NOT EXISTS(SELECT 1 FROM pg_locks WHERE locktype='advisory' AND classid=1297436233 AND objid=2 AND objsubid=2)").await?;
    tx.rollback().await?;
    assert_eq!(
        get_family(client, canceled).await?.unwrap().schema_state,
        SchemaState::Migrating
    );
    target
        .preparation()
        .await?
        .prepare_family(canceled, GraphRequirement::NewReservation)
        .await?;

    // Cancellation while waiting for public migration lock must remove waiter.
    let lock = blocker.transaction().await?;
    lock.execute(
        "SELECT pg_advisory_xact_lock($1,$2)",
        &[&0x4d554e49_i32, &2_i32],
    )
    .await?;
    let preparation = target.preparation().await?;
    let job = tokio::spawn(preparation.prepare_public());
    wait_for(client,"SELECT EXISTS(SELECT 1 FROM pg_locks WHERE locktype='advisory' AND classid=1297436233 AND objid=2 AND objsubid=2 AND NOT granted)").await?;
    job.abort();
    assert!(job.await.unwrap_err().is_cancelled());
    wait_for(client,"SELECT NOT EXISTS(SELECT 1 FROM pg_locks WHERE locktype='advisory' AND classid=1297436233 AND objid=2 AND objsubid=2 AND NOT granted)").await?;
    lock.rollback().await?;
    target.preparation().await?.prepare_public().await?;
    assert_eq!(count(client,"SELECT count(*) FROM mallard.applied_migration_schemas WHERE schema LIKE 'code_graph_%'").await?,0);
    println!("Cancellation releases active and waiting migration connections; interrupted family preparation retries successfully");
    Ok(())
}

async fn policy_verification(target: &Target, client: &mut Client, root: &Path) -> Result<()> {
    use muninn_core::family_policy as policy;
    let a_path = root.join("policy-git");
    let b_path = root.join("policy-directory");
    fs::create_dir(&a_path)?;
    fs::create_dir(&b_path)?;
    git(&a_path, &["init", "-b", "main"])?;
    git(
        &a_path,
        &[
            "-c",
            "user.name=Fixture",
            "-c",
            "user.email=fixture@example.invalid",
            "commit",
            "--allow-empty",
            "-m",
            "fixture",
        ],
    )?;
    let suppressed_path = root.join("policy-suppressed");
    let retired_path = root.join("policy-retired");
    git(
        &a_path,
        &[
            "worktree",
            "add",
            "-b",
            "suppressed",
            suppressed_path.to_str().unwrap(),
        ],
    )?;
    git(
        &a_path,
        &[
            "worktree",
            "add",
            "-b",
            "retired",
            retired_path.to_str().unwrap(),
        ],
    )?;
    let a_identity = CheckoutIdentity::discover(&a_path).await?;
    let b_identity = CheckoutIdentity::discover(&b_path).await?;
    let a = reserve_family(
        client,
        &a_identity,
        a_path.to_str().unwrap(),
        "policy A",
        512,
    )
    .await?;
    let b = reserve_family(
        client,
        &b_identity,
        b_path.to_str().unwrap(),
        "policy B",
        512,
    )
    .await?;
    target.record(a.id)?;
    target.record(b.id)?;
    target
        .preparation()
        .await?
        .prepare_family(a.id, GraphRequirement::NewReservation)
        .await?;
    target
        .preparation()
        .await?
        .prepare_family(b.id, GraphRequirement::NewReservation)
        .await?;
    let active = register_checkout(client, a.id, &a_identity).await?;
    let suppressed_identity = CheckoutIdentity::discover(&suppressed_path).await?;
    let retired_identity = CheckoutIdentity::discover(&retired_path).await?;
    let suppressed = register_checkout(client, a.id, &suppressed_identity).await?;
    let retired = register_checkout(client, a.id, &retired_identity).await?;
    let a_schema = store::repo_schema(a.id);
    let b_schema = store::repo_schema(b.id);
    client.execute(&format!("UPDATE {a_schema}.checkouts SET registration_state='suppressed',paused=true WHERE id=$1"),&[&suppressed.token.id]).await?;
    client.execute(&format!("UPDATE {a_schema}.checkouts SET registration_state='retired',retired_at=now() WHERE id=$1"),&[&retired.token.id]).await?;
    client
        .execute("UPDATE repos SET paused=true WHERE id=$1", &[&a.id])
        .await?;
    assert_eq!(
        policy::inspect(client, a.id).await.unwrap_err().code,
        "policy_not_initialized"
    );
    let defaults = policy::Defaults::shipped();
    let mut initial = policy::InitialRequest {
        api_version: 1,
        policy: policy::Policy::shipped("policy fixture".into()),
    };
    initial.policy.embeddings.backend = policy::Backend::Local;
    initial.policy.embeddings.model = None;
    let mut other = target.connect().await?;
    let (one, two) = tokio::join!(
        policy::initialize(client, a.id, &defaults, &initial),
        policy::initialize(&mut other, a.id, &defaults, &initial)
    );
    assert_eq!(one?.revision, 1);
    assert_eq!(two?.revision, 1);
    policy::initialize(client, b.id, &defaults, &initial).await?;
    readonly_verification(
        client,
        root,
        &a_path,
        &b_path,
        &suppressed_path,
        a.id,
        b.id,
        &initial,
    )
    .await?;
    assert_eq!(
        count(
            client,
            &format!("SELECT count(*) FROM {a_schema}.policy_versions")
        )
        .await?,
        1
    );
    let mut wrong_initial = initial.clone();
    wrong_initial.policy.name = "different".into();
    assert_eq!(
        policy::initialize(client, a.id, &defaults, &wrong_initial)
            .await
            .unwrap_err()
            .code,
        "policy_already_initialized"
    );

    // Observe actual transactional notifications using a dedicated connection.
    let (listener, mut connection) = target.config()?.connect(NoTls).await?;
    let (send, mut notifications) = tokio::sync::mpsc::unbounded_channel();
    let listener_driver = tokio::spawn(async move {
        while let Some(message) = std::future::poll_fn(|cx| connection.poll_message(cx)).await {
            if let Ok(tokio_postgres::AsyncMessage::Notification(n)) = message {
                let _ = send.send(n);
            }
        }
    });
    target.validate(&listener).await?;
    listener
        .batch_execute("LISTEN muninn_family_policy_changed")
        .await?;
    let mut request = policy::ApplyRequest {
        api_version: 1,
        expected_family_id: a.id,
        expected_revision: 1,
        acknowledge_reindex: false,
        policy: initial.policy.clone(),
    };
    let no_change = policy::apply(client, a.id, &request).await?;
    assert!(!no_change.changed && no_change.view.revision == 1);
    assert!(
        tokio::time::timeout(std::time::Duration::from_millis(100), notifications.recv())
            .await
            .is_err()
    );
    request.expected_family_id = b.id;
    assert_eq!(
        policy::apply(client, a.id, &request)
            .await
            .unwrap_err()
            .code,
        "family_conflict"
    );
    request.expected_family_id = a.id;
    request.expected_revision = 2;
    assert_eq!(
        policy::apply(client, a.id, &request)
            .await
            .unwrap_err()
            .code,
        "revision_conflict"
    );
    request.expected_revision = 1;
    request
        .policy
        .index
        .exclude
        .push("**/node_modules/**".into());
    let checked = policy::validate_candidate(client, a.id, &request).await?;
    assert!(checked.changed && checked.apply_supported);
    assert_eq!(policy::inspect(client, a.id).await?.revision, 1);
    let (one, two) = tokio::join!(
        policy::apply(client, a.id, &request),
        policy::apply(&mut other, a.id, &request)
    );
    assert_eq!(usize::from(one.is_ok()) + usize::from(two.is_ok()), 1);
    let (winner, loser) = if one.is_ok() {
        (one?, two.unwrap_err())
    } else {
        (two?, one.unwrap_err())
    };
    assert_eq!(loser.code, "revision_conflict");
    assert_eq!(winner.view.revision, 2);
    assert_eq!(winner.impact, Some(policy::Impact::Selection));
    assert!(winner.view.paused && !winner.view.indexing_enabled);
    let notification =
        tokio::time::timeout(std::time::Duration::from_secs(2), notifications.recv())
            .await?
            .unwrap();
    assert_eq!(notification.payload(), a.id.to_string());
    assert!(
        tokio::time::timeout(std::time::Duration::from_millis(100), notifications.recv())
            .await
            .is_err()
    );
    assert_eq!(policy::inspect(client, b.id).await?.revision, 1);
    assert_eq!(
        count(
            client,
            &format!("SELECT count(*) FROM {b_schema}.policy_versions")
        )
        .await?,
        1
    );
    for (checkout, generation) in [
        (active.token.id, 1_i64),
        (suppressed.token.id, 1),
        (retired.token.id, 0),
    ] {
        assert_eq!(
            client
                .query_one(
                    &format!("SELECT dirty_generation FROM {a_schema}.checkouts WHERE id=$1"),
                    &[&checkout]
                )
                .await?
                .get::<_, i64>(0),
            generation
        );
    }
    assert_eq!(
        lookup_checkout(client, a.id, &suppressed_identity.root)
            .await?
            .unwrap()
            .checkout
            .registration_state,
        RegistrationState::Suppressed
    );
    assert!(
        lookup_checkout(client, a.id, &suppressed_identity.root)
            .await?
            .unwrap()
            .checkout
            .paused
    );
    assert!(
        !record_checkout_observation(
            client,
            a.id,
            active.token,
            &CheckoutObservation {
                availability: Availability::Unknown,
                git_state: ObservedGitState::Unknown,
                error: None
            }
        )
        .await?
    );
    println!("Policy initialization, concurrent CAS, notifications, generation invalidation and family isolation verified");

    request.expected_revision = 2;
    request.policy = winner.view.policy.clone();
    assert!(!policy::apply(client, a.id, &request).await?.changed);
    let mut defaults_changed = defaults.clone();
    defaults_changed.index.exclude.push("src/**".into());
    assert_eq!(policy::inspect(client, a.id).await?.defaults, defaults);
    assert_ne!(
        policy::inspect(client, a.id).await?.effective_policy,
        request.policy.effective(&defaults_changed)
    );
    // Both application API and SQL protect append-only history/defaults.
    for table in ["policy_versions", "policy_defaults"] {
        rejected(
            client,
            &format!("DELETE FROM {a_schema}.{table}"),
            &SqlState::INTEGRITY_CONSTRAINT_VIOLATION,
        )
        .await?;
    }
    rejected(
        client,
        &format!("UPDATE {a_schema}.policy_versions SET policy=policy"),
        &SqlState::INTEGRITY_CONSTRAINT_VIOLATION,
    )
    .await?;
    rejected(client,&format!("INSERT INTO {a_schema}.policy_versions(revision,format_version,defaults_revision,policy) SELECT 3,1,defaults_revision,policy || '{{\"api_key\":\"fixture\"}}'::jsonb FROM {a_schema}.policy_versions WHERE revision=2"),&SqlState::CHECK_VIOLATION).await?;
    rejected(
        client,
        &format!(
            "INSERT INTO {a_schema}.family_policy(singleton,current_revision) VALUES(false,1)"
        ),
        &SqlState::CHECK_VIOLATION,
    )
    .await?;
    // A generation overflow occurs after attempted history/pointer writes;
    // PostgreSQL must roll the whole transaction back, including NOTIFY.
    client
        .execute(
            &format!("UPDATE {a_schema}.checkouts SET dirty_generation=$2 WHERE id=$1"),
            &[&active.token.id, &i64::MAX],
        )
        .await?;
    request.policy.name = "changed display name".into();
    assert_eq!(
        policy::apply(client, a.id, &request)
            .await
            .unwrap_err()
            .code,
        "database_error"
    );
    assert_eq!(policy::inspect(client, a.id).await?.revision, 2);
    assert_eq!(
        count(
            client,
            &format!("SELECT count(*) FROM {a_schema}.policy_versions")
        )
        .await?,
        2
    );
    assert!(
        tokio::time::timeout(std::time::Duration::from_millis(100), notifications.recv())
            .await
            .is_err()
    );
    client
        .execute(
            &format!("UPDATE {a_schema}.checkouts SET dirty_generation=1 WHERE id=$1"),
            &[&active.token.id],
        )
        .await?;
    let applied = policy::apply(client, a.id, &request).await?;
    assert_eq!(applied.impact, Some(policy::Impact::Display));
    assert_eq!(applied.view.revision, 3);
    assert_eq!(
        client
            .query_one(
                &format!("SELECT dirty_generation FROM {a_schema}.checkouts WHERE id=$1"),
                &[&active.token.id]
            )
            .await?
            .get::<_, i64>(0),
        2
    );
    assert!(!applied.view.indexing_enabled && applied.view.paused);
    let _ = tokio::time::timeout(std::time::Duration::from_secs(2), notifications.recv())
        .await?
        .unwrap();
    // Validated adapter profile changes cannot silently change fixed vectors.
    request.expected_revision = 3;
    request.policy.embeddings.backend = policy::Backend::Voyage;
    request.policy.embeddings.model = Some("voyage-code-3".into());
    request.acknowledge_reindex = true;
    assert!(
        !policy::validate_candidate(client, a.id, &request)
            .await?
            .apply_supported
    );
    assert_eq!(
        policy::apply(client, a.id, &request)
            .await
            .unwrap_err()
            .code,
        "dimension_migration_required"
    );
    assert_eq!(policy::inspect(client, a.id).await?.revision, 3);
    // Bounded revisions never wrap. This setup is confined to test history.
    client.batch_execute(&format!("INSERT INTO {b_schema}.policy_versions(revision,format_version,defaults_revision,policy) SELECT {},format_version,defaults_revision,policy FROM {b_schema}.policy_versions WHERE revision=1; UPDATE {b_schema}.family_policy SET current_revision={}",policy::MAX_REVISION,policy::MAX_REVISION)).await?;
    request.expected_family_id = b.id;
    request.expected_revision = policy::MAX_REVISION;
    request.policy = initial.policy.clone();
    request.policy.name = "at limit".into();
    assert_eq!(
        policy::apply(client, b.id, &request)
            .await
            .unwrap_err()
            .code,
        "revision_exhausted"
    );
    assert_eq!(
        policy::inspect(client, b.id).await?.revision,
        policy::MAX_REVISION
    );
    listener_driver.abort();
    println!("Immutable history/defaults, atomic rollback, profile refusal and revision exhaustion verified");
    Ok(())
}

async fn readonly_verification(
    client: &mut Client,
    root: &Path,
    a_path: &Path,
    b_path: &Path,
    suppressed: &Path,
    a: Uuid,
    b: Uuid,
    initial: &muninn_core::family_policy::InitialRequest,
) -> Result<()> {
    use muninn_core::family_policy::{
        self as policy,
        readonly::{query, Operation},
    };
    use serde_json::{json, Value};
    let a_schema = store::repo_schema(a);
    let b_schema = store::repo_schema(b);
    let snapshot = format!("SELECT jsonb_build_object(
        'registry',(SELECT jsonb_agg(to_jsonb(r) ORDER BY id) FROM public.repos r),
        'a_checkouts',(SELECT jsonb_agg(to_jsonb(c) ORDER BY id) FROM {a_schema}.checkouts c),
        'b_checkouts',(SELECT jsonb_agg(to_jsonb(c) ORDER BY id) FROM {b_schema}.checkouts c),
        'a_history',(SELECT jsonb_agg(to_jsonb(p) ORDER BY revision) FROM {a_schema}.policy_versions p),
        'b_history',(SELECT jsonb_agg(to_jsonb(p) ORDER BY revision) FROM {b_schema}.policy_versions p),
        'a_pointer',(SELECT to_jsonb(p) FROM {a_schema}.family_policy p),
        'b_pointer',(SELECT to_jsonb(p) FROM {b_schema}.family_policy p),
        'migrations',(SELECT count(*) FROM mallard.applied_migration_schemas),
        'graphs',(SELECT count(*) FROM ag_catalog.ag_graph))");
    let before: Value = client.query_one(&snapshot, &[]).await?.get(0);
    fs::create_dir_all(a_path.join("src"))?;
    fs::create_dir_all(a_path.join("node_modules/pkg"))?;
    fs::write(a_path.join("src/main.rs"), "fn fixture() {}")?;
    fs::write(a_path.join("node_modules/pkg/file.js"), "fixture")?;
    fs::create_dir_all(b_path.join("nested/deep"))?;
    let fresh = root.join("read-only-new-directory");
    fs::create_dir(&fresh)?;
    let discovered = root.join("read-only-new-worktree");
    git(
        a_path,
        &["worktree", "add", "--detach", discovered.to_str().unwrap()],
    )?;
    client
        .batch_execute("SET default_transaction_read_only=on")
        .await?;
    let inspected = query(client, &a_path.join("src"), Operation::Inspect, None).await?;
    assert_eq!(inspected["family_id"], json!(a));
    assert_eq!(inspected["revision"], 1);
    assert_eq!(inspected["indexing_enabled"], false);
    assert_eq!(inspected["paused"], true);
    let unregistered_checkout = query(client, &discovered, Operation::Inspect, None).await?;
    assert_eq!(unregistered_checkout["family_id"], json!(a));
    assert_eq!(unregistered_checkout["checkout_id"], Value::Null);
    let suppressed = query(client, suppressed, Operation::Inspect, None).await?;
    assert_eq!(suppressed["checkout"]["registration_state"], "suppressed");
    assert_eq!(suppressed["checkout"]["paused"], true);
    let directory = query(
        client,
        &b_path.join("nested/deep"),
        Operation::Inspect,
        None,
    )
    .await?;
    assert_eq!(directory["family_id"], json!(b));
    let inventory = query(client, a_path, Operation::Preflight, None).await?;
    assert_eq!(inventory["preflight"]["scope"], "selected_checkout");
    assert_eq!(inventory["preflight"]["tier1"]["files"], 1);
    assert_eq!(inventory["preflight"]["tier2"]["files"], 1);
    let mut request = policy::ApplyRequest {
        api_version: 1,
        expected_family_id: a,
        expected_revision: 1,
        acknowledge_reindex: false,
        policy: initial.policy.clone(),
    };
    request.policy.index.exclude.push("node_modules/".into());
    let checked = query(
        client,
        a_path,
        Operation::Check,
        Some(&serde_json::to_string(&request)?),
    )
    .await?;
    assert_eq!(checked["candidate"]["validation"]["impact"], "selection");
    assert_eq!(checked["preflight"]["tier2"]["files"], 0);
    assert_eq!(checked["policy"], json!(initial.policy));
    request.expected_revision = 2;
    assert_eq!(
        query(
            client,
            a_path,
            Operation::Check,
            Some(&serde_json::to_string(&request)?)
        )
        .await
        .unwrap_err()
        .code,
        "revision_conflict"
    );
    request.expected_revision = 1;
    request.expected_family_id = b;
    assert_eq!(
        query(
            client,
            a_path,
            Operation::Check,
            Some(&serde_json::to_string(&request)?)
        )
        .await
        .unwrap_err()
        .code,
        "family_conflict"
    );
    assert_eq!(
        query(client, &fresh, Operation::Inspect, None)
            .await
            .unwrap_err()
            .code,
        "not_registered"
    );
    let initial_check = query(
        client,
        &fresh,
        Operation::Check,
        Some(&serde_json::to_string(initial)?),
    )
    .await?;
    assert_eq!(initial_check["policy_source"], "creation_defaults");
    assert_eq!(
        initial_check["candidate"]["validation"]["registration_required"],
        true
    );
    let fresh_inventory = query(client, &fresh, Operation::Preflight, None).await?;
    assert_eq!(fresh_inventory["family_id"], Value::Null);
    assert_eq!(fresh_inventory["preflight"]["advice"], "start");
    assert_eq!(
        query(
            client,
            a_path,
            Operation::Check,
            Some("{\"api_version\":1,\"api_version\":1}")
        )
        .await
        .unwrap_err()
        .code,
        "invalid_request"
    );
    let after: Value = client.query_one(&snapshot, &[]).await?.get(0);
    assert_eq!(before, after, "read commands changed persistent state");
    client
        .batch_execute("SET default_transaction_read_only=off")
        .await?;
    println!("Read-only inspect/check/preflight verified: family/worktree resolution, candidate guards, creation defaults and unchanged registry/policies/checkouts/migrations/graphs");
    Ok(())
}

async fn registration_verification(
    target: &Target,
    client: &mut Client,
    root: &Path,
) -> Result<()> {
    use muninn_core::family_policy::{self as policy, registration::add};
    use serde_json::{json, Value};
    use std::sync::atomic::{AtomicUsize, Ordering};
    let main = root.join("registration-main");
    let worktree = root.join("registration-worktree");
    fs::create_dir(&main)?;
    git(&main, &["init", "-b", "main"])?;
    git(
        &main,
        &[
            "-c",
            "user.name=Fixture",
            "-c",
            "user.email=fixture@example.invalid",
            "commit",
            "--allow-empty",
            "-m",
            "fixture",
        ],
    )?;
    git(
        &main,
        &["worktree", "add", "--detach", worktree.to_str().unwrap()],
    )?;
    let mut other = target.connect().await?;
    let (a, b) = tokio::join!(
        add(client, || target.preparation(), &main, None),
        add(&mut other, || target.preparation(), &worktree, None)
    );
    let a = a?;
    let b = b?;
    assert_eq!(a["family_id"], b["family_id"]);
    assert_ne!(a["checkout_id"], b["checkout_id"]);
    assert_ne!(a["family_created"], b["family_created"]);
    assert_eq!(a["revision"], 1);
    assert_eq!(b["revision"], 1);
    assert_eq!(a["indexing_enabled"], false);
    assert_eq!(b["indexing_enabled"], false);
    let id = Uuid::parse_str(a["family_id"].as_str().unwrap())?;
    target.record(id)?;
    let schema = store::repo_schema(id);
    assert_eq!(
        count(client, &format!("SELECT count(*) FROM {schema}.checkouts")).await?,
        2
    );
    assert_eq!(
        count(
            client,
            &format!("SELECT count(*) FROM {schema}.policy_versions")
        )
        .await?,
        1
    );
    assert_eq!(
        count(client, &format!("SELECT count(*) FROM {schema}.chunks")).await?,
        0
    );
    assert!(!main.join(".muninn.toml").exists());
    assert!(!worktree.join(".muninn.toml").exists());
    assert!(client.query_one("SELECT NOT ever_indexed AND indexed_at IS NULL AND indexing_enabled_at IS NULL AND registration_completed_at IS NOT NULL FROM repos WHERE id=$1", &[&id]).await?.get::<_,bool>(0));
    let initial = policy::InitialRequest {
        api_version: 1,
        policy: serde_json::from_value(a["policy"].clone())?,
    };
    assert_eq!(
        add(client, || target.preparation(), &main, Some(&initial))
            .await
            .unwrap_err()
            .code,
        "policy_already_initialized"
    );
    let again = add(client, || target.preparation(), &main, None).await?;
    assert_eq!(again["checkout_id"], a["checkout_id"]);
    assert_eq!(again["revision"], 1);
    let mut change = policy::ApplyRequest {
        api_version: 1,
        expected_family_id: id,
        expected_revision: 1,
        acknowledge_reindex: false,
        policy: initial.policy.clone(),
    };
    change.policy.name = "changed after completed add".into();
    let applied = policy::apply_path(client, &worktree, &change).await?;
    assert_eq!(applied["revision"], 2);
    assert_eq!(applied["changed"], true);
    assert_eq!(applied["indexing_enabled"], false);
    assert_eq!(applied["reconciliation_scheduled"], false);
    change.expected_revision = 2;
    assert_eq!(
        policy::apply_path(client, &main, &change).await?["changed"],
        false
    );
    change.expected_revision = 1;
    assert_eq!(
        policy::apply_path(client, &main, &change)
            .await
            .unwrap_err()
            .code,
        "revision_conflict"
    );
    change.expected_revision = 2;
    change.expected_family_id = Uuid::new_v4();
    assert_eq!(
        policy::apply_path(client, &main, &change)
            .await
            .unwrap_err()
            .code,
        "family_conflict"
    );
    let again = add(client, || target.preparation(), &main, None).await?;
    assert_eq!(again["revision"], 2);
    assert_eq!(again["policy"]["name"], "changed after completed add");
    assert_eq!(
        count(
            client,
            &format!("SELECT count(*) FROM {schema}.policy_versions")
        )
        .await?,
        2
    );
    // Intent cannot be attached to an old row, overwritten, or marked incomplete.
    rejected(
        client,
        &format!("UPDATE repos SET registration_intent=NULL WHERE id='{id}'"),
        &SqlState::INTEGRITY_CONSTRAINT_VIOLATION,
    )
    .await?;
    rejected(
        client,
        &format!("UPDATE repos SET registration_completed_at=NULL WHERE id='{id}'"),
        &SqlState::INTEGRITY_CONSTRAINT_VIOLATION,
    )
    .await?;
    rejected(client, &format!("UPDATE repos SET registration_intent=(SELECT registration_intent FROM repos WHERE id='{id}') WHERE registration_intent IS NULL"), &SqlState::INTEGRITY_CONSTRAINT_VIOLATION).await?;
    // A completed new registration must not replace its graph if it disappears.
    client
        .batch_execute(&format!(
            "SELECT ag_catalog.drop_graph('{}',true)",
            store::graph_name(id)
        ))
        .await?;
    let failed = add(client, || target.preparation(), &main, None)
        .await
        .unwrap_err();
    assert_eq!(failed.code, "registration_error");
    assert_eq!(failed.details["family_id"], json!(id));
    assert_eq!(
        count(
            client,
            &format!(
                "SELECT count(*) FROM ag_catalog.ag_graph WHERE name='{}'",
                store::graph_name(id)
            )
        )
        .await?,
        0
    );
    create_graph(client, id).await?; // Repair only this deliberately damaged fixture.
    assert_eq!(
        add(client, || target.preparation(), &main, None).await?["revision"],
        2
    );

    // Inject a connection failure after committing the reservation, before family
    // preparation. Retry must reuse the original UUID and initial policy.
    let directory = root.join("registration-interrupted");
    fs::create_dir(&directory)?;
    let mut initial = initial.clone();
    initial.policy.name = "frozen initial configuration".into();
    initial.policy.embeddings.backend = policy::Backend::Local;
    initial.policy.embeddings.model = None;
    initial.policy.index.exclude.push("node_modules/".into());
    let calls = AtomicUsize::new(0);
    let factory = || async {
        if calls.fetch_add(1, Ordering::SeqCst) == 1 {
            anyhow::bail!("injected preparation connection failure");
        }
        target.preparation().await
    };
    let failure = add(client, factory, &directory, Some(&initial))
        .await
        .unwrap_err();
    assert_eq!(failure.details["reservation_persisted"], true);
    let recovered_id = Uuid::parse_str(failure.details["family_id"].as_str().unwrap())?;
    target.record(recovered_id)?;
    assert!(client.query_one("SELECT registration_intent IS NOT NULL AND registration_completed_at IS NULL AND schema_state='pending' FROM repos WHERE id=$1", &[&recovered_id]).await?.get::<_,bool>(0));
    let mut conflicting = initial.clone();
    conflicting.policy.name = "different input".into();
    assert_eq!(
        add(
            client,
            || target.preparation(),
            &directory,
            Some(&conflicting)
        )
        .await
        .unwrap_err()
        .code,
        "registration_intent_conflict"
    );
    // Force failure at the completion update, after policy initialization has
    // attempted its inserts. Only this disposable fixture is affected.
    target
        .preparation()
        .await?
        .prepare_family(recovered_id, GraphRequirement::RegistrationIntent)
        .await?;
    client.batch_execute(&format!("CREATE FUNCTION public.test_reject_registration_completion() RETURNS trigger LANGUAGE plpgsql AS $$ BEGIN IF NEW.id='{recovered_id}'::uuid AND NEW.registration_completed_at IS NOT NULL THEN RAISE EXCEPTION 'injected completion failure' USING ERRCODE='23000'; END IF; RETURN NEW; END $$; CREATE TRIGGER test_reject_registration_completion BEFORE UPDATE ON public.repos FOR EACH ROW EXECUTE FUNCTION public.test_reject_registration_completion()")).await?;
    let failure = add(client, || target.preparation(), &directory, None)
        .await
        .unwrap_err();
    assert_eq!(failure.details["reservation_persisted"], true);
    let recovered_schema = store::repo_schema(recovered_id);
    for table in ["policy_defaults", "policy_versions", "family_policy"] {
        assert_eq!(
            count(
                client,
                &format!("SELECT count(*) FROM {recovered_schema}.{table}")
            )
            .await?,
            0
        );
    }
    assert!(client
        .query_one(
            "SELECT registration_completed_at IS NULL FROM repos WHERE id=$1",
            &[&recovered_id]
        )
        .await?
        .get::<_, bool>(0));
    client.batch_execute("DROP TRIGGER test_reject_registration_completion ON public.repos; DROP FUNCTION public.test_reject_registration_completion()").await?;
    let recovered = add(client, || target.preparation(), &directory, None).await?;
    assert_eq!(recovered["family_id"], json!(recovered_id));
    assert_eq!(recovered["policy"], json!(initial.policy));
    assert_eq!(recovered["recovered_registration"], true);
    assert_eq!(recovered["dimension"], 512);
    assert_eq!(recovered["indexing_enabled"], false);
    fs::create_dir(directory.join("nested"))?;
    assert_eq!(
        add(
            client,
            || target.preparation(),
            &directory.join("nested"),
            None
        )
        .await?["family_id"],
        json!(recovered_id)
    );
    let before: Value = client
        .query_one(
            "SELECT jsonb_agg(to_jsonb(r) ORDER BY id) FROM repos r",
            &[],
        )
        .await?
        .get(0);
    let mut invalid = initial;
    invalid.api_version = 2;
    assert_eq!(
        add(client, || target.preparation(), &directory, Some(&invalid))
            .await
            .unwrap_err()
            .code,
        "invalid_request"
    );
    let after: Value = client
        .query_one(
            "SELECT jsonb_agg(to_jsonb(r) ORDER BY id) FROM repos r",
            &[],
        )
        .await?
        .get(0);
    assert_eq!(before, after);
    assert_eq!(count(client,"SELECT count(*) FROM mallard.applied_migration_schemas WHERE schema LIKE 'code_graph_%'").await?,0);
    println!("JSON registration/apply verified: concurrent worktrees, idempotency, CAS/path guards, durable recovery, immutable intent, missing completed graph refusal and no first indexing");
    Ok(())
}

#[path = "family_persistence/worktrees.rs"]
mod worktree_runtime;

#[path = "family_persistence/runtime.rs"]
mod policy_runtime;
