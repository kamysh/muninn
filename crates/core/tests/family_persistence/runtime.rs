use super::*;
use muninn_core::{
    config::GlobalConfig,
    embeddings::{EmbedFuture, EmbeddingBackend},
    family_policy::{self as policy, runtime},
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
        Box::pin(async move { Ok(texts.iter().map(|_| vec![1.0; 512]).collect()) })
    }
}
async fn index(
    client: &mut Client,
    id: Uuid,
    root: &Path,
    embedder: Arc<dyn EmbeddingBackend>,
) -> Result<()> {
    let (outcome, skips) =
        pipeline::index_repo(client, id, root, embedder, 8, 512, &[], &[], |_, _, _| {}).await?;
    ensure!(outcome == BatchOutcome::AllSucceeded, "{skips:?}");
    Ok(())
}
async fn content(client: &Client, id: Uuid, path: &Path, word: &str) -> Result<bool> {
    Ok(
        if let Some(target) = worktrees::resolve(client, path).await? {
            !worktrees::fulltext_search(client, &target, word, 20)
                .await?
                .is_empty()
        } else {
            !search::fulltext_search(client, word, id, 20)
                .await?
                .is_empty()
        },
    )
}
pub async fn verify(target: &Target, client: &mut Client, fixtures: &Path) -> Result<()> {
    for git_family in [false, true] {
        let root = fixtures.join(if git_family {
            "configured-git"
        } else {
            "configured-directory"
        });
        fs::create_dir(&root)?;
        fs::create_dir(root.join("generated"))?;
        fs::create_dir(root.join("node_modules"))?;
        fs::write(root.join("main.rs"), "fn primaryword() {}\n")?;
        fs::write(root.join("ignored.rs"), "fn vendorword() {}\n")?;
        fs::write(root.join(".gitignore"), "ignored.rs\n")?;
        fs::write(root.join("generated/keep.rs"), "fn retainedword() {}\n")?;
        fs::write(root.join("generated/drop.rs"), "fn droppedword() {}\n")?;
        fs::write(
            root.join("node_modules/package.rs"),
            "fn dependencyword() {}\n",
        )?;
        if git_family {
            git(&root, &["init", "-b", "main"])?;
            git(&root, &["add", "-f", "."])?;
            git(
                &root,
                &[
                    "-c",
                    "user.name=Fixture",
                    "-c",
                    "user.email=fixture@example.invalid",
                    "commit",
                    "-m",
                    "fixture",
                ],
            )?;
        }
        let linked = fixtures.join("configured-linked");
        if git_family {
            git(
                &root,
                &["worktree", "add", "--detach", linked.to_str().unwrap()],
            )?;
        }
        let selected = if git_family {
            linked.as_path()
        } else {
            root.as_path()
        };
        let mut initial = policy::Policy::shipped("configured runtime".into());
        initial.embeddings.backend = policy::Backend::Local;
        initial.embeddings.model = None;
        initial.index.exclude = vec![
            "generated/*".into(),
            "!generated/keep.rs".into(),
            "node_modules/".into(),
        ];
        initial.index.vendor = vec!["ignored.rs".into()];
        let receipt = policy::registration::add(
            client,
            || target.preparation(),
            selected,
            Some(&policy::InitialRequest {
                api_version: 1,
                policy: initial.clone(),
            }),
        )
        .await?;
        let id = Uuid::parse_str(receipt["family_id"].as_str().unwrap())?;
        target.record(id)?;
        let counter = Arc::new(Counter(AtomicUsize::new(0)));
        assert!(index(client, id, &root, counter.clone()).await.is_err());
        assert_eq!(
            counter.0.load(Ordering::SeqCst),
            0,
            "registration must not index"
        );
        let view = policy::inspect(client, id).await?;
        let inventory = policy::preflight::scan(
            &root,
            &view.policy,
            &view.defaults,
            policy::preflight::Budget::default(),
        )?;
        assert!(inventory.complete);
        assert_eq!(inventory.tier1.files, 3);
        assert_eq!(inventory.tier2.files, 1);
        let global = GlobalConfig::default();
        let (effective, _) = runtime::config(client, id, &root, &global).await?;
        assert_eq!(
            effective.embeddings.backend,
            muninn_core::config::EmbeddingBackend::Local
        );
        let mut request = policy::start::Request {
            api_version: 1,
            expected_family_id: id,
            expected_revision: 2,
        };
        assert_eq!(
            policy::start::authorize(client, &root, &request, &global)
                .await
                .unwrap_err()
                .code,
            "revision_conflict"
        );
        assert!(!policy::inspect(client, id).await?.indexing_enabled);
        request.expected_revision = 1;
        policy::start::authorize(client, &root, &request, &global).await?;
        policy::start::authorize(client, &root, &request, &global).await?; // idempotent
        assert_eq!(runtime::root(client, id, selected).await?, root);
        index(client, id, &root, counter.clone()).await?;
        for path in if git_family {
            vec![root.as_path(), linked.as_path()]
        } else {
            vec![root.as_path()]
        } {
            assert!(content(client, id, path, "primaryword").await?);
            assert!(content(client, id, path, "retainedword").await?);
            assert!(content(client, id, path, "vendorword").await?); // Git ignore is not policy
            assert!(!content(client, id, path, "droppedword").await?);
            assert!(!content(client, id, path, "dependencyword").await?);
        }
        let s = store::repo_schema(id);
        let file_count = count(
            client,
            &format!("SELECT count(DISTINCT file_path) FROM {s}.chunks"),
        )
        .await?;
        assert_eq!(
            file_count as u64,
            inventory.tier1.files + inventory.tier2.files
        );
        assert_eq!(
            count(
                client,
                &format!("SELECT count(*) FROM {s}.chunks WHERE tier=2 AND embedding IS NULL")
            )
            .await?,
            1
        );
        let mut changed = initial.clone();
        changed
            .index
            .exclude
            .extend(["ignored.rs".into(), "generated/keep.rs".into()]);
        let apply = policy::ApplyRequest {
            api_version: 1,
            expected_family_id: id,
            expected_revision: 1,
            acknowledge_reindex: false,
            policy: changed,
        };
        let saved = policy::apply_path(client, selected, &apply).await?;
        assert_eq!(saved["reconciliation_scheduled"], true);
        assert!(client
            .query_one(
                "SELECT indexed_at IS NULL FROM public.repos WHERE id=$1",
                &[&id]
            )
            .await?
            .get::<_, bool>(0));
        index(client, id, &root, counter.clone()).await?;
        for path in if git_family {
            vec![root.as_path(), linked.as_path()]
        } else {
            vec![root.as_path()]
        } {
            assert!(content(client, id, path, "primaryword").await?);
            assert!(!content(client, id, path, "retainedword").await?);
            assert!(!content(client, id, path, "vendorword").await?);
        }
        if git_family {
            let later = fixtures.join("configured-later");
            git(
                &root,
                &["worktree", "add", "--detach", later.to_str().unwrap()],
            )?;
            index(client, id, &root, counter.clone()).await?;
            assert!(content(client, id, &later, "primaryword").await?);
            assert!(!content(client, id, &later, "vendorword").await?);
            git(
                &root,
                &["worktree", "remove", "--force", linked.to_str().unwrap()],
            )?;
            assert_eq!(runtime::root(client, id, &linked).await?, root);
            assert_eq!(
                worktrees::registered_family(client, &root)
                    .await?
                    .unwrap()
                    .id,
                id
            );
        }
        if git_family {
            // A policy save waits for any publication using the previous policy.
            // After save commits, its invalidation cannot be cleared by old work.
            let mut other = target.connect().await?;
            let blocker = Arc::new(Blocking {
                entered: tokio::sync::Notify::new(),
                release: tokio::sync::Notify::new(),
            });
            fs::write(root.join("main.rs"), "fn concurrentword() {}\n")?;
            let indexing = index(&mut other, id, &root, blocker.clone());
            let changing = async {
                blocker.entered.notified().await;
                let mut request = apply.clone();
                request.expected_revision = 2;
                request.policy.index.exclude.push("main.rs".into());
                let change = policy::apply(client, id, &request);
                tokio::pin!(change);
                tokio::select! {
                    _ = &mut change => anyhow::bail!("policy changed during older publication"),
                    _ = tokio::time::sleep(std::time::Duration::from_millis(100)) => {},
                }
                blocker.release.notify_one();
                change.await?;
                Ok::<_, anyhow::Error>(())
            };
            let (indexed, changed) = tokio::join!(indexing, changing);
            indexed?;
            changed?;
            assert!(client
                .query_one(
                    "SELECT indexed_at IS NULL FROM public.repos WHERE id=$1",
                    &[&id]
                )
                .await?
                .get::<_, bool>(0));
            index(client, id, &root, counter.clone()).await?;
            assert!(!content(client, id, &root, "concurrentword").await?);
        }
        store::delete_repo(client, id).await?;
    }
    println!("policy runtime: explicit start, inventory parity, directory/Git indexing, saved exclusions and worktree inheritance verified");
    Ok(())
}

struct Blocking {
    entered: tokio::sync::Notify,
    release: tokio::sync::Notify,
}
impl EmbeddingBackend for Blocking {
    fn embed<'a>(&'a self, texts: &'a [String]) -> EmbedFuture<'a> {
        Box::pin(async move {
            self.entered.notify_one();
            self.release.notified().await;
            Ok(texts.iter().map(|_| vec![1.0; 512]).collect())
        })
    }
}
