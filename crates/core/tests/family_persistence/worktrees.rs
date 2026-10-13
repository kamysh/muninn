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
async fn found(client: &Client, target: &worktrees::Target, term: &str) -> Result<Vec<String>> {
    Ok(worktrees::fulltext_search(client, target, term, 100)
        .await?
        .into_iter()
        .map(|r| r.chunk.content)
        .collect())
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
    assert!(reconcile(client, repo.id, &main, &embedder).await.is_err());
    assert!(worktrees::resolve(client, &main).await?.is_none());
    assert!(!search::fulltext_search(client, "alpha", repo.id, 20)
        .await?
        .is_empty());
    assert!(worktrees::resolve(client, &one).await.is_err());
    fs::remove_file(main.join(".git/MERGE_HEAD"))?;

    let (outcome, skips) = reconcile(client, repo.id, &main, &embedder).await?;
    assert_eq!(legacy_embeddings, embedder.0.load(Ordering::SeqCst));
    assert_eq!(outcome, BatchOutcome::AllSucceeded, "{skips:?}");
    let base = worktrees::resolve(client, &main).await?.unwrap();
    let t1 = worktrees::resolve(client, &one).await?.unwrap();
    let t2 = worktrees::resolve(client, &two).await?.unwrap();
    assert_eq!(
        count(client, &format!("SELECT count(*) FROM {s}.file_deltas")).await?,
        0
    );
    assert_eq!(
        count(client, &format!("SELECT count(*) FROM {s}.file_versions")).await?,
        2
    );
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
    assert!(worktrees::resolve(client, &waiting).await.is_err());
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
            &format!(
                "SELECT nodes,edges FROM {s}.checkout_structural_snapshots WHERE checkout=$1"
            ),
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
    assert_eq!(embedder.0.load(Ordering::SeqCst), before + 1);
    assert!(found(client, &base, "alpha").await?.is_empty());
    assert!(!found(client, &t2, "alpha").await?.is_empty());
    assert!(!found(client, &t2, "olddeletion").await?.is_empty());
    assert!(found(client, &t2, "mainaddition").await?.is_empty());
    assert_eq!(
        count(
            client,
            &format!(
                "SELECT count(*) FROM {s}.file_deltas WHERE checkout='{}' AND path='a.rs'",
                t1.checkout
            )
        )
        .await?,
        0
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
        &["worktree", "add", "-b", "missing", missing.to_str().unwrap()],
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
    assert!(muninn_core::repo_resolver::list_git_worktrees(&main.join(".git"))
        .await?
        .iter()
        .any(|entry| entry.path == missing));
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
            &format!("UPDATE {s}.checkouts SET missing_since=now()-interval '61 seconds' WHERE id=$1"),
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
        Some(&[one.clone()]),
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
                "SELECT count(*) FROM {s}.file_deltas WHERE checkout='{}'",
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
    assert_eq!(count(client,&format!("SELECT count(*) FROM {s}.file_versions WHERE id NOT IN (SELECT version FROM {s}.base_files UNION SELECT version FROM {s}.file_deltas WHERE version IS NOT NULL)")).await?,0);
    assert!(worktrees::semantic_search(client, &t2, &vector, 20)
        .await?
        .is_empty());
    // Exercise multiple AGE batches, Unicode properties, duplicate call
    // candidates and a second replacement of a non-empty graph.
    let dense: String = (0..600)
        .map(|i| format!("fn node_{i}() {{ target(); target(); }}\n"))
        .collect();
    fs::write(main.join("gráph.rs"), format!("fn target() {{}}\n{dense}"))?;
    let (outcome, skips) = reconcile(client, repo.id, &main, &embedder).await?;
    assert_eq!(outcome, BatchOutcome::AllSucceeded, "{skips:?}");
    let graph_name = store::graph_name(base.graph);
    assert_eq!(
        count(
            client,
            &format!("SELECT count(*) FROM {graph_name}.\"CALLS\"")
        )
        .await?,
        600
    );
    fs::write(
        main.join("gráph.rs"),
        format!("fn target() {{}}\n{dense}// changed\n"),
    )?;
    let (outcome, skips) = reconcile(client, repo.id, &main, &embedder).await?;
    assert_eq!(outcome, BatchOutcome::AllSucceeded, "{skips:?}");
    assert_eq!(
        count(
            client,
            &format!("SELECT count(*) FROM {graph_name}.\"CALLS\"")
        )
        .await?,
        600
    );
    fs::remove_file(main.join("gráph.rs"))?;
    reconcile(client, repo.id, &main, &embedder).await?;
    assert_eq!(
        count(
            client,
            &format!("SELECT count(*) FROM {graph_name}.\"CALLS\"")
        )
        .await?,
        0
    );
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
    println!("Worktree runtime: shared embeddings, isolated updates/search, moving base, Git suspension, rollback and removal verified");
    Ok(())
}
