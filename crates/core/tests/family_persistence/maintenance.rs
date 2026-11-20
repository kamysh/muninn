use super::*;
use muninn_core::{
    config::GlobalConfig,
    embeddings::{EmbedFuture, EmbeddingBackend},
    family_policy as policy, maintenance, pipeline, worktrees,
};
use std::sync::Arc;

struct Embed {
    fail: bool,
}
impl EmbeddingBackend for Embed {
    fn embed<'a>(&'a self, texts: &'a [String]) -> EmbedFuture<'a> {
        Box::pin(async move {
            ensure!(!self.fail, "injected embedding failure");
            Ok(texts.iter().map(|_| vec![1.0; 512]).collect())
        })
    }
}

async fn add(target: &Target, client: &mut Client, root: &Path) -> Result<Uuid> {
    let mut initial = policy::Policy::shipped("serialized fixture".into());
    initial.embeddings.backend = policy::Backend::Local;
    initial.embeddings.model = None;
    initial.index.exclude = vec!["!generated/keep.rs".into()];
    let receipt = policy::registration::add(
        client,
        || target.preparation(),
        root,
        Some(&policy::InitialRequest {
            api_version: 1,
            policy: initial,
        }),
    )
    .await?;
    let id = Uuid::parse_str(receipt["family_id"].as_str().unwrap())?;
    target.record(id)?;
    policy::start::authorize(
        client,
        root,
        &policy::start::Request {
            api_version: 1,
            expected_family_id: id,
            expected_revision: 1,
        },
        &GlobalConfig::default(),
    )
    .await?;
    Ok(id)
}

async fn refresh(
    client: &mut Client,
    id: Uuid,
    root: &Path,
    fail: bool,
) -> Result<Vec<pipeline::SkipRecord>> {
    Ok(pipeline::index_repo(
        client,
        id,
        root,
        Arc::new(Embed { fail }),
        8,
        512,
        &[],
        &[],
        |_, _, _| {},
    )
    .await?
    .1)
}

pub(super) async fn verify(target: &Target, client: &mut Client, parent: &Path) -> Result<()> {
    let root = parent.join("serialized-main");
    let linked = parent.join("serialized-linked");
    fs::create_dir(&root)?;
    git(&root, &["init", "-b", "main"])?;
    git(&root, &["config", "user.name", "Fixture"])?;
    git(&root, &["config", "user.email", "fixture@example.invalid"])?;
    fs::write(
        root.join("shared.rs"),
        "fn sharedword() { targetword(); }\nfn targetword() {}\n",
    )?;
    fs::write(root.join("anchor.rs"), "fn anchorword() {}\n")?;
    git(&root, &["add", "."])?;
    git(&root, &["commit", "-m", "fixture"])?;
    git(
        &root,
        &["worktree", "add", "--detach", linked.to_str().unwrap()],
    )?;
    let id = add(target, client, &root).await?;
    let note = muninn_core::knowledge::upsert(
        client,
        None,
        root.to_str().unwrap(),
        "retained note",
        "curated knowledge",
        &[],
        &[],
        None,
        512,
    )
    .await?;
    ensure!(refresh(client, id, &root, false).await?.is_empty());
    let base = worktrees::resolve(client, &root).await?.unwrap();
    let sibling = worktrees::resolve(client, &linked).await?.unwrap();
    let schema = format!("\"{}\"", store::repo_schema(id));
    let requested_sql =
        format!("SELECT COALESCE(sum(requested),0)::bigint FROM {schema}.selection_maintenance");
    let requested_before: i64 = client.query_one(&requested_sql, &[]).await?.get(0);
    let graph = store::graph_name(id);
    let ids_sql = format!("SELECT array_agg(id::text ORDER BY id) FROM {graph}._ag_label_vertex");
    let graph_before: Vec<String> = client.query_one(&ids_sql, &[]).await?.get(0);
    ensure!(refresh(client, id, &root, false).await?.is_empty());
    let requested_after: i64 = client.query_one(&requested_sql, &[]).await?.get(0);
    let graph_after: Vec<String> = client.query_one(&ids_sql, &[]).await?.get(0);
    ensure!(
        requested_after == requested_before,
        "an audit must not request policy maintenance"
    );
    ensure!(
        graph_after == graph_before,
        "an unchanged audit must retain the existing graph"
    );
    let versions: i64 = client
        .query_one(
            &format!("SELECT count(*) FROM {schema}.file_versions WHERE path='shared.rs'"),
            &[],
        )
        .await?
        .get(0);
    ensure!(versions == 1, "unchanged worktree content must be shared");

    // The gate is database-wide, not an in-process mutex; another family works.
    let other_root = parent.join("serialized-other");
    fs::create_dir(&other_root)?;
    fs::write(other_root.join("other.rs"), "fn independentword() {}\n")?;
    let other_id = add(target, client, &other_root).await?;
    ensure!(refresh(client, other_id, &other_root, false)
        .await?
        .is_empty());
    let mut locker = target.connect().await?;
    let held = locker.transaction().await?;
    held.query_one(
        "SELECT pg_advisory_xact_lock(hashtextextended($1,771913))",
        &[&id.to_string()],
    )
    .await?;
    let error = worktrees::fulltext_search(client, &base, "sharedword", 10)
        .await
        .unwrap_err();
    ensure!(error.to_string().contains("family_busy"));
    ensure!(
        !search::fulltext_search(client, "independentword", other_id, 10)
            .await?
            .is_empty()
    );
    held.rollback().await?;

    fs::write(root.join(".gitignore"), "shared.rs\ngenerated/\n")?;
    fs::create_dir(root.join("generated"))?;
    fs::write(
        root.join("generated/keep.rs"),
        "fn explicitlyincludedword() {}\n",
    )?;
    fs::write(
        root.join("generated/drop.rs"),
        "fn ignoredgeneratedword() {}\n",
    )?;
    let (_, skips) = worktrees::reconcile_changed_family(
        client,
        id,
        &root,
        Arc::new(Embed { fail: false }),
        8,
        512,
        &[],
        &[],
        |_, _, _| {},
        Some(&[root.join(".gitignore")]),
    )
    .await?;
    ensure!(skips.is_empty());
    ensure!(worktrees::fulltext_search(client, &base, "sharedword", 10)
        .await?
        .is_empty());
    ensure!(
        !worktrees::fulltext_search(client, &sibling, "sharedword", 10)
            .await?
            .is_empty()
    );
    ensure!(
        !worktrees::fulltext_search(client, &base, "explicitlyincludedword", 10)
            .await?
            .is_empty()
    );
    ensure!(
        worktrees::fulltext_search(client, &base, "ignoredgeneratedword", 10)
            .await?
            .is_empty()
    );
    ensure!(worktrees::query_related(
        client,
        &base,
        "sharedword",
        StructuralRelation::Calls,
        false
    )
    .await?
    .is_empty());
    ensure!(!worktrees::query_related(
        client,
        &sibling,
        "sharedword",
        StructuralRelation::Calls,
        false
    )
    .await?
    .is_empty());

    // A paused pending target retains data, blocks new searches, and reports why.
    client
        .execute(
            &format!("UPDATE {schema}.checkouts SET paused=true WHERE id=$1"),
            &[&sibling.checkout],
        )
        .await?;
    fs::write(linked.join(".gitignore"), "shared.rs\n")?;
    let (_, skips) = worktrees::reconcile_changed_family(
        client,
        id,
        &root,
        Arc::new(Embed { fail: false }),
        8,
        512,
        &[],
        &[],
        |_, _, _| {},
        Some(&[linked.join(".gitignore")]),
    )
    .await?;
    ensure!(!skips.is_empty() && maintenance::pending(client, id).await?);
    ensure!(worktrees::fulltext_search(client, &base, "anchorword", 10)
        .await
        .unwrap_err()
        .to_string()
        .contains("family_maintenance"));
    ensure!(!maintenance::status(client, id).await?["targets"][0]["last_error"].is_null());
    client
        .execute(
            &format!("UPDATE {schema}.checkouts SET paused=false WHERE id=$1"),
            &[&sibling.checkout],
        )
        .await?;

    // Force preparation failure. The old shared version survives rollback.
    fs::write(linked.join("new.rs"), "fn newlyembeddedword() {}\n")?;
    let _ = refresh(client, id, &root, true).await;
    ensure!(maintenance::pending(client, id).await?);
    let versions: i64 = client
        .query_one(
            &format!("SELECT count(*) FROM {schema}.file_versions WHERE path='shared.rs'"),
            &[],
        )
        .await?
        .get(0);
    ensure!(versions == 1);
    let mut restarted = target.connect().await?;
    ensure!(refresh(&mut restarted, id, &root, false).await?.is_empty());
    ensure!(!maintenance::pending(&restarted, id).await?);
    let versions: i64 = restarted
        .query_one(
            &format!("SELECT count(*) FROM {schema}.file_versions WHERE path='shared.rs'"),
            &[],
        )
        .await?
        .get(0);
    ensure!(
        versions == 0,
        "last-reference cleanup must remove shared versions"
    );
    ensure!(worktrees::query_related(
        &mut restarted,
        &sibling,
        "sharedword",
        StructuralRelation::Calls,
        false
    )
    .await?
    .is_empty());

    fs::remove_file(root.join(".gitignore"))?;
    ensure!(refresh(&mut restarted, id, &root, false).await?.is_empty());
    ensure!(
        !worktrees::fulltext_search(&mut restarted, &base, "sharedword", 10)
            .await?
            .is_empty()
    );

    // Explicit policy acceptance has the same pending/completion contract.
    let view = policy::inspect(&restarted, id).await?;
    let mut policy = view.policy;
    policy.index.exclude.push("shared.rs".into());
    policy::apply(
        &mut restarted,
        id,
        &policy::ApplyRequest {
            api_version: 1,
            expected_family_id: id,
            expected_revision: view.revision,
            policy,
            acknowledge_reindex: false,
        },
    )
    .await?;
    ensure!(maintenance::pending(&restarted, id).await?);
    ensure!(refresh(&mut restarted, id, &root, false).await?.is_empty());
    ensure!(
        worktrees::fulltext_search(&mut restarted, &base, "sharedword", 10)
            .await?
            .is_empty()
    );
    ensure!(
        muninn_core::knowledge::list(&restarted, root.to_str().unwrap())
            .await?
            .iter()
            .any(|item| item.id == note.id)
    );
    // An accepted policy change waits for an already admitted reader to leave.
    let mut reader = target.connect().await?;
    let held_reader = maintenance::read(&mut reader, id).await?;
    let view = policy::inspect(&restarted, id).await?;
    let mut candidate = view.policy;
    candidate.index.exclude.push("anchor.rs".into());
    let mut writer = target.connect().await?;
    let (started, ready) = tokio::sync::oneshot::channel();
    let mut update = tokio::spawn(async move {
        let _ = started.send(());
        policy::apply(
            &mut writer,
            id,
            &policy::ApplyRequest {
                api_version: 1,
                expected_family_id: id,
                expected_revision: view.revision,
                policy: candidate,
                acknowledge_reindex: false,
            },
        )
        .await
    });
    ready.await?;
    ensure!(
        tokio::time::timeout(std::time::Duration::from_millis(100), &mut update)
            .await
            .is_err()
    );
    held_reader.rollback().await?;
    update.await??;
    ensure!(refresh(&mut restarted, id, &root, false).await?.is_empty());

    // Directory families use their family ID as the single maintenance target.
    let view = policy::inspect(&restarted, other_id).await?;
    let mut candidate = view.policy;
    candidate.index.exclude.push("other.rs".into());
    policy::apply(
        &mut restarted,
        other_id,
        &policy::ApplyRequest {
            api_version: 1,
            expected_family_id: other_id,
            expected_revision: view.revision,
            policy: candidate,
            acknowledge_reindex: false,
        },
    )
    .await?;
    ensure!(maintenance::pending(&restarted, other_id).await?);
    ensure!(refresh(&mut restarted, other_id, &other_root, false)
        .await?
        .is_empty());
    ensure!(!maintenance::pending(&restarted, other_id).await?);
    ensure!(
        search::fulltext_search(&mut restarted, "independentword", other_id, 10)
            .await?
            .is_empty()
    );
    eprintln!("Serialized maintenance verified: sharing, Git overrides, gate isolation, pause, rollback, reconnect retry, last-reference cleanup, re-inclusion and policy refresh.");
    Ok(())
}
