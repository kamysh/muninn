use super::*;
use muninn_core::{
    embeddings::{EmbedFuture, EmbeddingBackend},
    pipeline, worktrees,
};
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Arc,
};

struct Counter(AtomicUsize);
impl EmbeddingBackend for Counter {
    fn embed<'a>(&'a self, texts: &'a [String]) -> EmbedFuture<'a> {
        self.0.fetch_add(texts.len(), Ordering::SeqCst);
        Box::pin(async move { Ok(texts.iter().map(|_| vec![1.0; 32]).collect()) })
    }
}
async fn reconcile(
    client: &mut Client,
    id: Uuid,
    root: &Path,
    embedder: &Arc<Counter>,
) -> Result<(BatchOutcome, Vec<pipeline::SkipRecord>)> {
    pipeline::index_repo(
        client,
        id,
        root,
        embedder.clone(),
        16,
        32,
        &[],
        &[],
        |_, _, _| {},
    )
    .await
}
async fn found(client: &mut Client, target: &worktrees::Target, term: &str) -> Result<Vec<String>> {
    Ok(worktrees::fulltext_search(client, target, term, 100)
        .await?
        .into_iter()
        .map(|r| r.chunk.content)
        .collect())
}

pub(super) async fn verify_initial_progress(
    target: &Target,
    client: &mut Client,
    parent: &Path,
) -> Result<()> {
    use std::sync::{Once, OnceLock};

    let main = parent.join("initial-main");
    let linked = parent.join("initial-linked");
    fs::create_dir(&main)?;
    git(&main, &["init", "-b", "main"])?;
    git(&main, &["config", "user.name", "Fixture"])?;
    git(&main, &["config", "user.email", "fixture@example.invalid"])?;
    fs::write(main.join("inherited.txt"), "inheritedword\n")?;
    fs::write(main.join("deleted.txt"), "deletedword\n")?;
    fs::write(main.join("edited.txt"), "originalword\n")?;
    git(&main, &["add", "."])?;
    git(&main, &["commit", "-m", "base"])?;
    let repo = store::register_repo(client, main.to_str().unwrap(), "initial-progress", 32).await?;
    target.record(repo.id)?;
    let embedder = Arc::new(Counter(AtomicUsize::new(0)));
    let (_, skips) = reconcile(client, repo.id, &main, &embedder).await?;
    assert!(skips.is_empty(), "{skips:?}");
    let base = worktrees::resolve(client, &main).await?.unwrap();
    let schema = store::repo_schema(repo.id);
    git(
        &main,
        &["worktree", "add", "-b", "linked", linked.to_str().unwrap()],
    )?;
    fs::remove_file(main.join("deleted.txt"))?;
    fs::write(main.join("advance.txt"), "advanceword\n")?;
    git(&main, &["add", "-A"])?;
    git(&main, &["commit", "-m", "advance"])?;
    fs::write(linked.join("edited.txt"), "stagedword\n")?;
    git(&linked, &["add", "edited.txt"])?;
    fs::write(linked.join("stable.txt"), "stableword\n")?;

    let change = Once::new();
    let checkpoint = OnceLock::new();
    let (_, skips) = worktrees::reconcile_changed_family(
        client,
        repo.id,
        &main,
        embedder.clone(),
        16,
        32,
        &[],
        &[],
        |_, _, path| {
            if path == linked.join("stable.txt") {
                change.call_once(|| {
                    tokio::task::block_in_place(|| {
                        tokio::runtime::Handle::current().block_on(async {
                            let mut reader = target.connect().await.unwrap();
                            let rows = tokio::time::timeout(
                                std::time::Duration::from_secs(3),
                                found(&mut reader, &base, "inheritedword"),
                            ).await.unwrap().unwrap();
                            assert!(!rows.is_empty());
                            let row = reader.query_one(
                                &format!("SELECT version FROM {schema}.checkout_prepared_files WHERE path='stable.txt'"), &[],
                            ).await.unwrap();
                            checkpoint.set(row.get::<_, Uuid>(0)).unwrap();
                        })
                    });
                    git(&linked, &["reset", "--hard", "main"]).unwrap();
                    fs::write(linked.join("edited.txt"), "workingword\n").unwrap();
                });
            }
        },
        Some(std::slice::from_ref(&linked)),
    )
    .await?;
    assert!(change.is_completed());
    assert!(skips.is_empty(), "{skips:?}");
    let checkout = worktrees::resolve(client, &linked).await?.unwrap();
    for term in ["inheritedword", "advanceword", "workingword", "stableword"] {
        assert!(!found(client, &checkout, term).await?.is_empty(), "{term}");
    }
    for term in ["deletedword", "originalword", "stagedword"] {
        assert!(found(client, &checkout, term).await?.is_empty(), "{term}");
    }
    let saved: Uuid = client.query_one(
        &format!("SELECT m.version FROM {schema}.checkout_file_versions m JOIN {schema}.file_versions v ON v.id=m.version WHERE m.checkout=$1 AND v.path='stable.txt'"),
        &[&checkout.checkout],
    ).await?.get(0);
    assert_eq!(Some(&saved), checkpoint.get());
    assert_eq!(
        embedder.0.load(Ordering::SeqCst),
        0,
        "text search has no vector dependency"
    );
    let sibling_before = client.query(
        &format!("SELECT version,xmin::text FROM {schema}.checkout_file_versions WHERE checkout=$1 ORDER BY version"),
        &[&checkout.checkout],
    ).await?.into_iter().map(|row| (row.get::<_, Uuid>(0), row.get::<_, String>(1))).collect::<Vec<_>>();
    fs::write(main.join("primary-only.txt"), "primaryonlyword\n")?;
    let (_, skips) = worktrees::reconcile_changed_family(
        client,
        repo.id,
        &main,
        embedder,
        16,
        32,
        &[],
        &[],
        |_, _, _| {},
        Some(std::slice::from_ref(&main)),
    )
    .await?;
    assert!(skips.is_empty(), "{skips:?}");
    assert!(!found(client, &base, "advanceword").await?.is_empty());
    assert!(found(client, &checkout, "primaryonlyword")
        .await?
        .is_empty());
    let sibling_after = client.query(
        &format!("SELECT version,xmin::text FROM {schema}.checkout_file_versions WHERE checkout=$1 ORDER BY version"),
        &[&checkout.checkout],
    ).await?.into_iter().map(|row| (row.get::<_, Uuid>(0), row.get::<_, String>(1))).collect::<Vec<_>>();
    assert_eq!(
        sibling_before, sibling_after,
        "primary publication cannot rewrite sibling membership"
    );
    assert_eq!(
        count(
            client,
            &format!("SELECT count(*) FROM {schema}.checkout_prepared_files"),
        )
        .await?,
        0
    );
    verify_membership_upgrade(client, &schema, &base, &checkout).await?;
    if let Some(mcp) = std::env::var_os("MUNINN_TEST_MCP_BINARY") {
        verify_mcp_overlap(client, &main, &base, Path::new(&mcp), parent).await?;
    }
    store::delete_repo(client, repo.id).await?;
    Ok(())
}

async fn verify_mcp_overlap(
    client: &mut Client,
    main: &Path,
    base: &worktrees::Target,
    mcp: &Path,
    parent: &Path,
) -> Result<()> {
    use std::{process::Stdio, time::Duration};
    use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};

    let incoming = parent.join("mcp-first-search");
    git(
        main,
        &["worktree", "add", "--detach", incoming.to_str().unwrap()],
    )?;
    fs::write(incoming.join("only-here.txt"), "mcponlyword\n")?;
    let held = client.transaction().await?;
    held.query_one(
        "SELECT pg_advisory_xact_lock(hashtextextended($1,317530))",
        &[&base.family.to_string()],
    )
    .await?;

    let mut child = tokio::process::Command::new(mcp)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .kill_on_drop(true)
        .spawn()?;
    let mut stdin = child.stdin.take().context("missing MCP stdin")?;
    let mut stdout = BufReader::new(child.stdout.take().context("missing MCP stdout")?).lines();
    for (id, checkout, query) in [
        (1, &incoming, "mcponlyword"),
        (2, &base.root, "primaryonlyword"),
    ] {
        let request = serde_json::json!({
            "jsonrpc":"2.0", "id":id, "method":"tools/call",
            "params":{"name":"search_fulltext","arguments":{"query":query,"repo":checkout}}
        });
        stdin.write_all(format!("{request}\n").as_bytes()).await?;
    }
    let response = tokio::time::timeout(Duration::from_secs(8), stdout.next_line())
        .await??
        .context("MCP closed before returning the ready checkout")?;
    let response: serde_json::Value = serde_json::from_str(&response)?;
    assert_eq!(response["id"], 2, "{response}");
    assert!(
        response["result"]["content"][0]["text"]
            .as_str()
            .unwrap_or_default()
            .contains("primaryonlyword"),
        "{response}"
    );
    held.commit().await?;
    let response = tokio::time::timeout(Duration::from_secs(8), stdout.next_line())
        .await??
        .context("MCP closed before returning the new checkout")?;
    let response: serde_json::Value = serde_json::from_str(&response)?;
    assert_eq!(response["id"], 1, "{response}");
    assert!(
        response["result"]["content"][0]["text"]
            .as_str()
            .unwrap_or_default()
            .contains("mcponlyword"),
        "{response}"
    );
    stdin.shutdown().await?;
    drop(stdin);
    assert!(tokio::time::timeout(Duration::from_secs(8), child.wait())
        .await??
        .success());
    Ok(())
}

async fn verify_membership_upgrade(
    client: &mut Client,
    schema: &str,
    primary: &worktrees::Target,
    linked: &worktrees::Target,
) -> Result<()> {
    let state = format!("SELECT jsonb_build_object(
      'memberships',(SELECT jsonb_agg(to_jsonb(m) ORDER BY checkout,version) FROM {schema}.checkout_file_versions m),
      'structure',(SELECT jsonb_agg(to_jsonb(s) ORDER BY checkout) FROM {schema}.checkout_structural_snapshots s))");
    let expected: serde_json::Value = client.query_one(&state, &[]).await?.get(0);
    // Recreate the 1.3.1 moving-base representation inside the guarded fixture.
    // It contains a replacement, an addition and a deletion for the linked view.
    client.batch_execute(&format!(
        "CREATE TABLE {schema}.base_files(path text PRIMARY KEY,version uuid NOT NULL REFERENCES {schema}.file_versions(id));
         CREATE TABLE {schema}.file_deltas(checkout uuid NOT NULL,path text NOT NULL,version uuid,PRIMARY KEY(checkout,path));
         INSERT INTO {schema}.base_files SELECT v.path,v.id FROM {schema}.checkout_file_versions m
             JOIN {schema}.file_versions v ON v.id=m.version WHERE m.checkout='{}';
         WITH linked AS (SELECT v.path,v.id FROM {schema}.checkout_file_versions m
             JOIN {schema}.file_versions v ON v.id=m.version WHERE m.checkout='{}')
         INSERT INTO {schema}.file_deltas
             SELECT '{}',COALESCE(b.path,l.path),l.id FROM {schema}.base_files b FULL JOIN linked l USING(path)
             WHERE b.version IS DISTINCT FROM l.id;
         DROP TABLE {schema}.checkout_file_versions;
         ALTER TABLE {schema}.checkouts DROP COLUMN publication_generation, DROP COLUMN indexed_git_head, DROP COLUMN unreadable_paths;
         DELETE FROM mallard.applied_migration_schemas WHERE schema='{schema}' AND migration_name='repo-checkout-file-versions';",
        primary.checkout, linked.checkout, linked.checkout,
    )).await?;
    assert!(found(client, linked, "primaryonlyword").await?.is_empty());
    assert!(!found(client, linked, "workingword").await?.is_empty());
    assert!(!found(client, linked, "stableword").await?.is_empty());
    let migrated: serde_json::Value = client.query_one(&state, &[]).await?.get(0);
    assert_eq!(expected, migrated);
    Ok(())
}

pub(super) async fn verify(target: &Target, client: &mut Client, parent: &Path) -> Result<()> {
    let main = parent.join("runtime-main");
    let one = parent.join("runtime-one");
    let two = parent.join("runtime-two");
    fs::create_dir(&main)?;
    git(&main, &["init", "-b", "main"])?;
    git(&main, &["config", "user.name", "Fixture"])?;
    git(&main, &["config", "user.email", "fixture@example.invalid"])?;
    fs::write(main.join("a.rs"), "fn alpha() { beta(); }\nfn beta() {}\n")?;
    fs::write(main.join("deleted.txt"), "olddeletion\n")?;
    git(&main, &["add", "."])?;
    git(&main, &["commit", "-m", "base"])?;
    git(
        &main,
        &["worktree", "add", "-b", "one", one.to_str().unwrap()],
    )?;
    git(
        &main,
        &["worktree", "add", "-b", "two", two.to_str().unwrap()],
    )?;
    let repo = store::register_repo(client, main.to_str().unwrap(), "runtime", 32).await?;
    target.record(repo.id)?;
    let s = format!("\"{}\"", store::repo_schema(repo.id));
    let embedder = Arc::new(Counter(AtomicUsize::new(0)));
    // Seed precisely the existing index_file layout (absolute paths and no
    // file-version IDs). First reconciliation must reuse its embeddings.
    for file in ["a.rs", "deleted.txt"] {
        pipeline::index_file(
            client,
            repo.id,
            &main.join(file),
            embedder.as_ref(),
            1500,
            16,
            32,
            Tier::Tier1,
        )
        .await?;
    }
    let legacy_embeddings = embedder.0.load(Ordering::SeqCst);
    store::mark_indexed(client, repo.id).await?;
    fs::write(
        main.join(".git/MERGE_HEAD"),
        "0000000000000000000000000000000000000000\n",
    )?;
    let (_, skips) = reconcile(client, repo.id, &main, &embedder).await?;
    assert_eq!(skips.len(), 1);
    assert_eq!(skips[0].path, main);
    assert!(skips[0].reason.contains("Git operation incomplete"));
    assert!(worktrees::resolve(client, &main).await?.is_none());
    assert!(!search::fulltext_search(client, "alpha", repo.id, 20)
        .await?
        .is_empty());
    let independent = worktrees::resolve(client, &one).await?.unwrap();
    assert!(!found(client, &independent, "alpha").await?.is_empty());
    fs::remove_file(main.join(".git/MERGE_HEAD"))?;

    let (outcome, skips) = reconcile(client, repo.id, &main, &embedder).await?;
    assert_eq!(legacy_embeddings, embedder.0.load(Ordering::SeqCst));
    assert_eq!(outcome, BatchOutcome::AllSucceeded, "{skips:?}");
    let base = worktrees::resolve(client, &main).await?.unwrap();
    let t1 = worktrees::resolve(client, &one).await?.unwrap();
    let t2 = worktrees::resolve(client, &two).await?.unwrap();
    assert_eq!(
        count(
            client,
            &format!("SELECT count(*) FROM {s}.checkout_file_versions")
        )
        .await?,
        6
    );
    assert_eq!(
        count(client, &format!("SELECT count(*) FROM {s}.file_versions")).await?,
        2
    );
    // A reported edit is published without discovering an unreported file;
    // the full audit later discovers it, and other checkouts stay unchanged.
    fs::write(one.join("a.rs"), "fn incremental_changed() {}\n")?;
    fs::write(one.join("unreported.txt"), "audit_discovery_marker\n")?;
    let (_, skips) = worktrees::reconcile_changed_family(
        client,
        repo.id,
        &main,
        embedder.clone(),
        16,
        32,
        &[],
        &[],
        |_, _, _| {},
        Some(&[one.join("a.rs")]),
    )
    .await?;
    assert!(skips.is_empty(), "{skips:?}");
    assert!(!found(client, &t1, "incremental_changed").await?.is_empty());
    assert!(found(client, &t1, "audit_discovery_marker")
        .await?
        .is_empty());
    // A newly added target must resolve a retained caller; adding a local
    // namesake must then take priority, without changing another checkout.
    let caller = main.join("a.rs");
    let target_file = main.join("later.rs");
    fs::write(
        &caller,
        "fn alpha() { beta(); later_target(); }\nfn beta() {}\n",
    )?;
    let (_, skips) = worktrees::reconcile_changed_family(
        client,
        repo.id,
        &main,
        embedder.clone(),
        16,
        32,
        &[],
        &[],
        |_, _, _| {},
        Some(std::slice::from_ref(&caller)),
    )
    .await?;
    assert!(skips.is_empty(), "{skips:?}");
    fs::write(&target_file, "fn later_target() {}\n")?;
    let (_, skips) = worktrees::reconcile_changed_family(
        client,
        repo.id,
        &main,
        embedder.clone(),
        16,
        32,
        &[],
        &[],
        |_, _, _| {},
        Some(std::slice::from_ref(&target_file)),
    )
    .await?;
    assert!(skips.is_empty(), "{skips:?}");
    let related =
        worktrees::query_related(client, &base, "alpha", StructuralRelation::Calls, false).await?;
    assert!(related
        .iter()
        .any(|symbol| symbol.name == "later_target" && symbol.file_path.ends_with("later.rs")));
    fs::write(
        &caller,
        "fn alpha() { beta(); later_target(); }\nfn beta() {}\nfn later_target() {}\n",
    )?;
    let (_, skips) = worktrees::reconcile_changed_family(
        client,
        repo.id,
        &main,
        embedder.clone(),
        16,
        32,
        &[],
        &[],
        |_, _, _| {},
        Some(std::slice::from_ref(&caller)),
    )
    .await?;
    assert!(skips.is_empty(), "{skips:?}");
    let related =
        worktrees::query_related(client, &base, "alpha", StructuralRelation::Calls, false).await?;
    assert!(related
        .iter()
        .any(|symbol| symbol.name == "later_target" && symbol.file_path.ends_with("a.rs")));
    assert!(!related
        .iter()
        .any(|symbol| symbol.name == "later_target" && symbol.file_path.ends_with("later.rs")));
    assert!(
        worktrees::query_related(client, &t2, "later_target", StructuralRelation::Calls, true)
            .await?
            .is_empty()
    );
    fs::write(
        &caller,
        "fn alpha() { beta(); later_target(); }\nfn beta() {}\n",
    )?;
    let (_, skips) = worktrees::reconcile_changed_family(
        client,
        repo.id,
        &main,
        embedder.clone(),
        16,
        32,
        &[],
        &[],
        |_, _, _| {},
        Some(std::slice::from_ref(&caller)),
    )
    .await?;
    assert!(skips.is_empty(), "{skips:?}");
    let related =
        worktrees::query_related(client, &base, "alpha", StructuralRelation::Calls, false).await?;
    assert!(related
        .iter()
        .any(|symbol| symbol.name == "later_target" && symbol.file_path.ends_with("later.rs")));
    fs::write(&caller, "fn alpha() { beta(); }\nfn beta() {}\n")?;
    fs::remove_file(&target_file)?;
    let (_, skips) = worktrees::reconcile_changed_family(
        client,
        repo.id,
        &main,
        embedder.clone(),
        16,
        32,
        &[],
        &[],
        |_, _, _| {},
        Some(&[caller, target_file]),
    )
    .await?;
    assert!(skips.is_empty(), "{skips:?}");
    assert!(!found(client, &t2, "alpha").await?.is_empty());
    reconcile(client, repo.id, &main, &embedder).await?;
    assert!(!found(client, &t1, "audit_discovery_marker")
        .await?
        .is_empty());
    let linked_caller = one.join("linked_caller.rs");
    let linked_target = one.join("linked_target.rs");
    fs::write(&linked_caller, "fn linked_caller() { linked_target(); }\n")?;
    let (_, skips) = worktrees::reconcile_changed_family(
        client,
        repo.id,
        &main,
        embedder.clone(),
        16,
        32,
        &[],
        &[],
        |_, _, _| {},
        Some(std::slice::from_ref(&linked_caller)),
    )
    .await?;
    assert!(skips.is_empty(), "{skips:?}");
    fs::write(&linked_target, "fn linked_target() {}\n")?;
    let (_, skips) = worktrees::reconcile_changed_family(
        client,
        repo.id,
        &main,
        embedder.clone(),
        16,
        32,
        &[],
        &[],
        |_, _, _| {},
        Some(std::slice::from_ref(&linked_target)),
    )
    .await?;
    assert!(skips.is_empty(), "{skips:?}");
    let linked_edges = worktrees::query_related(
        client,
        &t1,
        "linked_caller",
        StructuralRelation::Calls,
        false,
    )
    .await?;
    assert!(linked_edges
        .iter()
        .any(|symbol| symbol.name == "linked_target"));
    let linked_disjoint = one.join("linked_disjoint.rs");
    fs::write(&linked_disjoint, "fn linked_disjoint() {}\n")?;
    let (_, skips) = worktrees::reconcile_changed_family(
        client,
        repo.id,
        &main,
        embedder.clone(),
        16,
        32,
        &[],
        &[],
        |_, _, _| {},
        Some(std::slice::from_ref(&linked_disjoint)),
    )
    .await?;
    assert!(skips.is_empty(), "{skips:?}");
    assert!(worktrees::query_related(
        client,
        &t1,
        "linked_caller",
        StructuralRelation::Calls,
        false
    )
    .await?
    .iter()
    .any(|symbol| symbol.name == "linked_target"));
    assert!(worktrees::query_related(
        client,
        &t2,
        "linked_target",
        StructuralRelation::Calls,
        true
    )
    .await?
    .is_empty());
    fs::remove_file(&linked_caller)?;
    fs::remove_file(&linked_target)?;
    fs::remove_file(&linked_disjoint)?;
    let (_, skips) = worktrees::reconcile_changed_family(
        client,
        repo.id,
        &main,
        embedder.clone(),
        16,
        32,
        &[],
        &[],
        |_, _, _| {},
        Some(&[linked_caller, linked_target, linked_disjoint]),
    )
    .await?;
    assert!(skips.is_empty(), "{skips:?}");
    // Both rename paths must be processed, even for an untracked file.
    fs::rename(one.join("unreported.txt"), one.join("renamed.txt"))?;
    let (_, skips) = worktrees::reconcile_changed_family(
        client,
        repo.id,
        &main,
        embedder.clone(),
        16,
        32,
        &[],
        &[],
        |_, _, _| {},
        Some(&[one.join("unreported.txt"), one.join("renamed.txt")]),
    )
    .await?;
    assert!(skips.is_empty(), "{skips:?}");
    let hits = worktrees::fulltext_search(client, &t1, "audit_discovery_marker", 20).await?;
    assert_eq!(hits.len(), 1);
    assert!(hits[0].chunk.file_path.ends_with("renamed.txt"));

    // A directory event cannot identify all affected descendants; audit it.
    fs::create_dir(one.join("newdir"))?;
    fs::write(one.join("newdir/nested.txt"), "nested_audit_marker\n")?;
    let (_, skips) = worktrees::reconcile_changed_family(
        client,
        repo.id,
        &main,
        embedder.clone(),
        16,
        32,
        &[],
        &[],
        |_, _, _| {},
        Some(&[one.join("newdir")]),
    )
    .await?;
    assert!(skips.is_empty(), "{skips:?}");
    assert!(!found(client, &t1, "nested_audit_marker").await?.is_empty());
    fs::remove_dir_all(one.join("newdir"))?;
    let (_, skips) = worktrees::reconcile_changed_family(
        client,
        repo.id,
        &main,
        embedder.clone(),
        16,
        32,
        &[],
        &[],
        |_, _, _| {},
        Some(&[one.join("newdir")]),
    )
    .await?;
    assert!(skips.is_empty(), "{skips:?}");
    assert!(found(client, &t1, "nested_audit_marker").await?.is_empty());

    // An epoch modification time cannot suppress a reported same-size edit.
    let epoch_file = one.join("a.rs");
    let set_epoch = || -> Result<()> {
        let file = fs::OpenOptions::new().write(true).open(&epoch_file)?;
        file.set_times(fs::FileTimes::new().set_modified(std::time::SystemTime::UNIX_EPOCH))?;
        Ok(())
    };
    set_epoch()?;
    fs::write(&epoch_file, "fn incremental_revised() {}\n")?;
    set_epoch()?;
    let (_, skips) = worktrees::reconcile_changed_family(
        client,
        repo.id,
        &main,
        embedder.clone(),
        16,
        32,
        &[],
        &[],
        |_, _, _| {},
        Some(std::slice::from_ref(&epoch_file)),
    )
    .await?;
    assert!(skips.is_empty(), "{skips:?}");
    assert!(!found(client, &t1, "incremental_revised").await?.is_empty());
    fs::write(one.join("a.rs"), "fn alpha() { beta(); }\nfn beta() {}\n")?;
    fs::remove_file(one.join("renamed.txt"))?;
    let (_, skips) = worktrees::reconcile_changed_family(
        client,
        repo.id,
        &main,
        embedder.clone(),
        16,
        32,
        &[],
        &[],
        |_, _, _| {},
        Some(&[one.join("a.rs"), one.join("renamed.txt")]),
    )
    .await?;
    assert!(skips.is_empty(), "{skips:?}");
    assert!(!found(client, &t1, "alpha").await?.is_empty());
    assert!(found(client, &t1, "audit_discovery_marker")
        .await?
        .is_empty());
    let initial = embedder.0.load(Ordering::SeqCst);
    assert!(initial > 0);
    let demanded = parent.join("runtime-demanded");
    let waiting = parent.join("runtime-waiting");
    git(
        &main,
        &[
            "worktree",
            "add",
            "-b",
            "demanded",
            demanded.to_str().unwrap(),
        ],
    )?;
    git(
        &main,
        &[
            "worktree",
            "add",
            "-b",
            "waiting",
            waiting.to_str().unwrap(),
        ],
    )?;
    worktrees::reconcile_requested_checkout(
        client,
        repo.id,
        &main,
        &demanded,
        embedder.clone(),
        16,
        32,
        &[],
        &[],
    )
    .await?;
    let demanded_target = worktrees::resolve(client, &demanded).await?.unwrap();
    assert!(!found(client, &demanded_target, "alpha").await?.is_empty());
    assert!(worktrees::resolve(client, &waiting).await?.is_none());
    assert_eq!(initial, embedder.0.load(Ordering::SeqCst));
    git(
        &main,
        &["worktree", "remove", "--force", waiting.to_str().unwrap()],
    )?;
    reconcile(client, repo.id, &main, &embedder).await?;
    assert_eq!(initial, embedder.0.load(Ordering::SeqCst));
    assert!(!found(client, &t1, "alpha").await?.is_empty());
    assert_eq!(
        worktrees::query_related(client, &t1, "alpha", StructuralRelation::Calls, false)
            .await?
            .len(),
        1
    );
    assert_eq!(
        count(
            client,
            &format!(
                "SELECT count(*) FROM ag_catalog.ag_graph WHERE name='{}'",
                store::graph_name(t1.graph)
            )
        )
        .await?,
        0,
        "new linked worktrees must not rebuild AGE graphs"
    );
    // Simulate an indexed checkout from before the snapshot migration. Its
    // existing AGE graph remains readable when no snapshot row exists.
    let row = client
        .query_one(
            &format!("SELECT nodes,edges FROM {s}.checkout_structural_snapshots WHERE checkout=$1"),
            &[&t2.checkout],
        )
        .await?;
    let legacy_nodes: Vec<Symbol> = serde_json::from_value(row.get(0))?;
    let legacy_edges: Vec<StructuralEdge> = serde_json::from_value(row.get(1))?;
    client
        .batch_execute(&format!(
            "SELECT ag_catalog.create_graph('{}')",
            store::graph_name(t2.graph)
        ))
        .await?;
    graph::upsert_symbol_nodes(
        client,
        t2.graph,
        &legacy_nodes
            .iter()
            .map(|symbol| graph::SymbolNodeInput {
                chunk_id: symbol.chunk_id,
                name: symbol.name.clone(),
                kind: symbol.kind.clone(),
                file_path: symbol.file_path.clone(),
                start_line: symbol.range.start,
                end_line: symbol.range.end,
            })
            .collect::<Vec<_>>(),
    )
    .await?;
    graph::upsert_edges(client, t2.graph, &legacy_edges).await?;
    client
        .execute(
            &format!("DELETE FROM {s}.checkout_structural_snapshots WHERE checkout=$1"),
            &[&t2.checkout],
        )
        .await?;
    assert_eq!(
        worktrees::query_related(client, &t2, "alpha", StructuralRelation::Calls, false)
            .await?
            .len(),
        1
    );
    assert!(worktrees::fulltext_search(client, &t1, "alpha", 100)
        .await?
        .iter()
        .all(|r| Path::new(&r.chunk.file_path).starts_with(&one)));

    // A worktree's replacement, addition and tombstone remain local.
    fs::write(one.join("a.rs"), "fn gamma() {}\n")?;
    fs::remove_file(one.join("deleted.txt"))?;
    fs::write(one.join("added.txt"), "onlyone\n")?;
    reconcile(client, repo.id, &main, &embedder).await?;
    assert!(found(client, &t1, "alpha").await?.is_empty());
    assert!(!found(client, &t1, "gamma").await?.is_empty());
    assert!(!found(client, &t2, "alpha").await?.is_empty());
    assert!(found(client, &t1, "olddeletion").await?.is_empty());
    assert!(found(client, &t2, "onlyone").await?.is_empty());
    let vector = vec![1.0; 32];
    while pipeline::backfill_once(client, repo.id, embedder.as_ref(), 32).await? > 0 {}
    let semantic = worktrees::semantic_search(client, &t1, &vector, 100).await?;
    assert!(!semantic.is_empty());
    assert!(semantic
        .iter()
        .all(|r| !r.chunk.content.contains("alpha") && !r.chunk.content.contains("olddeletion")));
    assert!(!worktrees::hybrid_search(client, &t1, &vector, "gamma", 20)
        .await?
        .is_empty());
    assert!(
        worktrees::query_related(client, &t1, "alpha", StructuralRelation::Calls, false)
            .await?
            .is_empty()
    );
    assert_eq!(
        worktrees::query_related(client, &t2, "alpha", StructuralRelation::Calls, false)
            .await?
            .len(),
        1
    );

    // Main adopts the first worktree's already indexed version: no embedding
    // recomputation. The second worktree retains its old file and graph.
    let before = embedder.0.load(Ordering::SeqCst);
    fs::write(main.join("a.rs"), "fn gamma() {}\n")?;
    fs::remove_file(main.join("deleted.txt"))?;
    fs::write(main.join("newmain.txt"), "mainaddition\n")?;
    reconcile(client, repo.id, &main, &embedder).await?;
    assert_eq!(embedder.0.load(Ordering::SeqCst), before);
    assert!(found(client, &base, "alpha").await?.is_empty());
    assert!(!found(client, &t2, "alpha").await?.is_empty());
    assert!(!found(client, &t2, "olddeletion").await?.is_empty());
    assert!(found(client, &t2, "mainaddition").await?.is_empty());
    assert_eq!(
        count(
            client,
            &format!(
                "SELECT count(*) FROM {s}.checkout_file_versions one JOIN {s}.checkout_file_versions main USING(version)
                 JOIN {s}.file_versions v ON v.id=one.version WHERE one.checkout='{}' AND main.checkout='{}' AND v.path='a.rs'",
                t1.checkout, base.checkout
            )
        )
        .await?,
        1
    );
    assert_eq!(
        worktrees::query_related(client, &t2, "alpha", StructuralRelation::Calls, false)
            .await?
            .len(),
        1
    );

    // The periodic discovery path initializes a new worktree without rereading
    // or re-embedding already indexed worktrees.
    git(&main, &["add", "."])?;
    git(&main, &["commit", "-m", "advanced main"])?;
    let three = parent.join("runtime-three");
    git(
        &main,
        &["worktree", "add", "-b", "three", three.to_str().unwrap()],
    )?;
    let before_discovery = embedder.0.load(Ordering::SeqCst);
    let (_, skips) = worktrees::reconcile_changed_family(
        client,
        repo.id,
        &main,
        embedder.clone(),
        16,
        32,
        &[],
        &[],
        |_, _, _| {},
        Some(&[]),
    )
    .await?;
    assert!(skips.is_empty(), "{skips:?}");
    assert_eq!(before_discovery, embedder.0.load(Ordering::SeqCst));
    let t3 = worktrees::resolve(client, &three).await?.unwrap();
    assert!(!found(client, &t3, "gamma").await?.is_empty());
    assert!(found(client, &t3, "alpha").await?.is_empty());
    fs::create_dir(three.join("nested"))?;
    assert_eq!(
        worktrees::resolve(client, &three.join("nested"))
            .await?
            .unwrap()
            .checkout,
        t3.checkout
    );

    // Git moves retain administrative identity. Discover the move and a new
    // checkout at its former path in one periodic pass, without new embeddings.
    let relocated = parent.join("runtime-relocated");
    git(
        &main,
        &[
            "worktree",
            "move",
            three.to_str().unwrap(),
            relocated.to_str().unwrap(),
        ],
    )?;
    git(
        &main,
        &["worktree", "add", "--detach", three.to_str().unwrap()],
    )?;
    let before_move = embedder.0.load(Ordering::SeqCst);
    let (_, skips) = worktrees::reconcile_changed_family(
        client,
        repo.id,
        &main,
        embedder.clone(),
        16,
        32,
        &[],
        &[],
        |_, _, _| {},
        Some(&[]),
    )
    .await?;
    assert!(skips.is_empty(), "{skips:?}");
    let relocated_target = worktrees::resolve(client, &relocated).await?.unwrap();
    assert_eq!(relocated_target.checkout, t3.checkout);
    assert_eq!(relocated_target.graph, t3.graph);
    let replacement = worktrees::resolve(client, &three).await?.unwrap();
    assert_ne!(replacement.checkout, t3.checkout);
    assert!(!found(client, &relocated_target, "gamma").await?.is_empty());
    assert!(!found(client, &replacement, "gamma").await?.is_empty());
    assert!(
        worktrees::fulltext_search(client, &relocated_target, "gamma", 20)
            .await?
            .iter()
            .all(|hit| Path::new(&hit.chunk.file_path).starts_with(&relocated))
    );
    assert_eq!(before_move, embedder.0.load(Ordering::SeqCst));
    git(
        &main,
        &["worktree", "remove", "--force", three.to_str().unwrap()],
    )?;
    worktrees::reconcile_changed_family(
        client,
        repo.id,
        &main,
        embedder.clone(),
        16,
        32,
        &[],
        &[],
        |_, _, _| {},
        Some(&[]),
    )
    .await?;
    assert_eq!(
        count(
            client,
            &format!(
                "SELECT count(*) FROM {s}.checkouts WHERE id='{}' AND registration_state='retired'",
                replacement.checkout
            )
        )
        .await?,
        1
    );
    assert!(!found(client, &relocated_target, "gamma").await?.is_empty());

    // Git can keep a manually deleted worktree in its registry until pruning.
    // Its confirmed missing directory retires the checkout without deleting
    // its completed structural snapshot.
    let missing = parent.join("runtime-missing");
    git(
        &main,
        &[
            "worktree",
            "add",
            "-b",
            "missing",
            missing.to_str().unwrap(),
        ],
    )?;
    reconcile(client, repo.id, &main, &embedder).await?;
    let missing_target = worktrees::resolve(client, &missing).await?.unwrap();
    let before = count(
        client,
        &format!(
            "SELECT count(*) FROM {s}.checkout_structural_snapshots WHERE checkout='{}'",
            missing_target.checkout
        ),
    )
    .await?;
    assert_eq!(before, 1);
    fs::remove_dir_all(&missing)?;
    assert!(
        muninn_core::repo_resolver::list_git_worktrees(&main.join(".git"))
            .await?
            .iter()
            .any(|entry| entry.path == missing)
    );
    reconcile(client, repo.id, &main, &embedder).await?;
    assert_eq!(
        count(
            client,
            &format!(
                "SELECT count(*) FROM {s}.checkouts WHERE id='{}' AND registration_state='active' AND missing_since IS NOT NULL",
                missing_target.checkout
            )
        )
        .await?,
        1
    );
    client
        .execute(
            &format!(
                "UPDATE {s}.checkouts SET missing_since=now()-interval '61 seconds' WHERE id=$1"
            ),
            &[&missing_target.checkout],
        )
        .await?;
    reconcile(client, repo.id, &main, &embedder).await?;
    assert_eq!(
        count(
            client,
            &format!(
                "SELECT count(*) FROM {s}.checkouts WHERE id='{}' AND registration_state='retired'",
                missing_target.checkout
            )
        )
        .await?,
        1
    );
    assert_eq!(
        count(
            client,
            &format!(
                "SELECT count(*) FROM {s}.checkout_structural_snapshots WHERE checkout='{}'",
                missing_target.checkout
            )
        )
        .await?,
        before
    );

    // Blocking Git metadata prevents publication, including resolved-but-not-
    // completed merges. Other worktrees continue updating independently.
    let g = muninn_core::repo_resolver::discover_git_checkout(&one)
        .await?
        .unwrap();
    fs::write(
        g.git_dir.join("MERGE_HEAD"),
        "0000000000000000000000000000000000000000\n",
    )?;
    fs::write(one.join("a.rs"), "fn conflictmarker() {}\n")?;
    let (_, skips) = reconcile(client, repo.id, &main, &embedder).await?;
    assert!(!skips.is_empty());
    assert!(!found(client, &t1, "gamma").await?.is_empty());
    assert!(found(client, &t1, "conflictmarker").await?.is_empty());
    let (_, retry) = worktrees::reconcile_changed_family(
        client,
        repo.id,
        &main,
        embedder.clone(),
        16,
        32,
        &[],
        &[],
        |_, _, _| {},
        Some(std::slice::from_ref(&one)),
    )
    .await?;
    assert_eq!(retry.len(), 1);
    assert_eq!(retry[0].path, one);
    fs::remove_file(g.git_dir.join("MERGE_HEAD"))?;
    reconcile(client, repo.id, &main, &embedder).await?;
    assert!(!found(client, &t1, "conflictmarker").await?.is_empty());

    // A source change detected after preparation must roll back the entire
    // publication (base, deltas, chunks and graph), not just repair it later.
    fs::write(main.join("a.rs"), "fn interrupted() {}\n")?;
    let changed = std::sync::atomic::AtomicBool::new(false);
    let (_, skips) = pipeline::index_repo(
        client,
        repo.id,
        &main,
        embedder.clone(),
        16,
        32,
        &[],
        &[],
        |_, _, file| {
            if file == main.join("a.rs") && !changed.swap(true, Ordering::SeqCst) {
                fs::write(file, "fn changedagain() {}\n").unwrap();
            }
        },
    )
    .await?;
    assert!(!skips.is_empty());
    assert!(!found(client, &base, "gamma").await?.is_empty());
    assert!(found(client, &base, "interrupted").await?.is_empty());
    assert!(!found(client, &t2, "alpha").await?.is_empty());
    fs::write(main.join("a.rs"), "fn gamma() {}\n")?;

    // A temporary move shorter than the grace period keeps the registration.
    let moved = parent.join("temporarily-away");
    fs::rename(&two, &moved)?;
    reconcile(client, repo.id, &main, &embedder).await?;
    assert_eq!(
        count(
            client,
            &format!(
                "SELECT count(*) FROM {s}.checkouts WHERE id='{}' AND registration_state='active'",
                t2.checkout
            )
        )
        .await?,
        1
    );
    fs::rename(&moved, &two)?;
    git(
        &main,
        &["worktree", "remove", "--force", two.to_str().unwrap()],
    )?;
    reconcile(client, repo.id, &main, &embedder).await?;
    assert_eq!(
        count(
            client,
            &format!(
                "SELECT count(*) FROM {s}.checkout_file_versions WHERE checkout='{}'",
                t2.checkout
            )
        )
        .await?,
        0
    );
    assert_eq!(
        count(
            client,
            &format!(
                "SELECT count(*) FROM ag_catalog.ag_graph WHERE name='{}'",
                store::graph_name(t2.graph)
            )
        )
        .await?,
        0
    );
    assert_eq!(count(client,&format!("SELECT count(*) FROM {s}.file_versions WHERE id NOT IN
        (SELECT version FROM {s}.checkout_file_versions UNION SELECT version FROM {s}.checkout_prepared_files)")).await?,0);
    assert!(worktrees::semantic_search(client, &t2, &vector, 20)
        .await?
        .is_empty());
    // Exercise Unicode properties, duplicate call candidates and replacement
    // of a non-empty structural view.
    let dense: String = (0..600)
        .map(|i| format!("fn node_{i}() {{ target(); target(); }}\n"))
        .collect();
    fs::write(main.join("gráph.rs"), format!("fn target() {{}}\n{dense}"))?;
    let (outcome, skips) = reconcile(client, repo.id, &main, &embedder).await?;
    assert_eq!(outcome, BatchOutcome::AllSucceeded, "{skips:?}");
    let graph_count = format!("SELECT count(*) FROM {s}.checkout_structural_snapshots graph,
        jsonb_array_elements(graph.edges) edge WHERE graph.checkout='{}' AND edge->>'relation'='Calls'",
        base.checkout);
    assert_eq!(count(client, &graph_count).await?, 600);
    // A disjoint file change must preserve unrelated existing relationships.
    let disjoint = main.join("disjoint.rs");
    fs::write(&disjoint, "fn unrelated_symbol() {}\n")?;
    let (_, skips) = worktrees::reconcile_changed_family(
        client,
        repo.id,
        &main,
        embedder.clone(),
        16,
        32,
        &[],
        &[],
        |_, _, _| {},
        Some(std::slice::from_ref(&disjoint)),
    )
    .await?;
    assert!(skips.is_empty(), "{skips:?}");
    assert_eq!(count(client, &graph_count).await?, 600);
    fs::remove_file(&disjoint)?;
    let (_, skips) = worktrees::reconcile_changed_family(
        client,
        repo.id,
        &main,
        embedder.clone(),
        16,
        32,
        &[],
        &[],
        |_, _, _| {},
        Some(std::slice::from_ref(&disjoint)),
    )
    .await?;
    assert!(skips.is_empty(), "{skips:?}");
    assert_eq!(count(client, &graph_count).await?, 600);
    fs::write(
        main.join("gráph.rs"),
        format!("fn target() {{}}\n{dense}// changed\n"),
    )?;
    let (outcome, skips) = reconcile(client, repo.id, &main, &embedder).await?;
    assert_eq!(outcome, BatchOutcome::AllSucceeded, "{skips:?}");
    assert_eq!(count(client, &graph_count).await?, 600);
    fs::remove_file(main.join("gráph.rs"))?;
    reconcile(client, repo.id, &main, &embedder).await?;
    assert_eq!(count(client, &graph_count).await?, 0);
    // An unchanged caller must gain a cross-file edge when a target appears.
    fs::write(main.join("caller.rs"), "fn caller() { later_target(); }\n")?;
    reconcile(client, repo.id, &main, &embedder).await?;
    let cached = client.query_one(
        &format!("SELECT a.file_version,a.candidates FROM {s}.file_analysis_cache a JOIN {s}.file_versions v ON v.id=a.file_version WHERE v.path='caller.rs'"),
        &[],
    ).await?;
    let caller_version: Uuid = cached.get(0);
    let candidates: serde_json::Value = cached.get(1);
    assert!(candidates.to_string().contains("later_target"));
    fs::write(main.join("target.rs"), "fn later_target() {}\n")?;
    reconcile(client, repo.id, &main, &embedder).await?;
    assert_eq!(
        worktrees::query_related(client, &base, "caller", StructuralRelation::Calls, false)
            .await?
            .len(),
        1
    );
    let after = client
        .query_one(
            &format!("SELECT candidates FROM {s}.file_analysis_cache WHERE file_version=$1"),
            &[&caller_version],
        )
        .await?;
    assert_eq!(after.get::<_, serde_json::Value>(0), candidates);
    // Simulate a collision by assigning the next content's hash to the old
    // version. The exact bytes still differ and must create a new version.
    let replacement = "fn caller() { collision_replacement(); }\n";
    let collision_hash = content_sha256(replacement);
    client
        .execute(
            &format!("UPDATE {s}.file_versions SET content_hash=$1 WHERE id=$2"),
            &[&collision_hash, &caller_version],
        )
        .await?;
    fs::write(main.join("caller.rs"), replacement)?;
    reconcile(client, repo.id, &main, &embedder).await?;
    let current = client
        .query_one(
            &format!("SELECT m.version FROM {s}.checkout_file_versions m
                JOIN {s}.file_versions v ON v.id=m.version WHERE m.checkout=$1 AND v.path='caller.rs'"),
            &[&base.checkout],
        )
        .await?
        .get::<_, Uuid>(0);
    assert_ne!(current, caller_version);
    assert!(!found(client, &base, "collision_replacement")
        .await?
        .is_empty());
    store::delete_repo(client, repo.id).await?;
    assert_eq!(
        count(
            client,
            &format!(
                "SELECT count(*) FROM ag_catalog.ag_graph WHERE name='{}'",
                store::graph_name(t3.graph)
            )
        )
        .await?,
        0
    );
    println!("Worktree runtime: shared versions, independent publication, Git suspension, rollback and removal verified");
    Ok(())
}
