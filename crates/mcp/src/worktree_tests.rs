//! First search of a linked checkout must register and publish it on demand.
use super::{dispatch_tool, tools::SearchContext};
use anyhow::{ensure, Result};
use muninn_core::{
    config::GlobalConfig,
    db,
    embeddings::{EmbedFuture, EmbeddingBackend},
    repo_resolver, store, worktrees,
};
use serde::Deserialize;
use serde_json::json;
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

struct Dummy(usize);
impl EmbeddingBackend for Dummy {
    fn embed<'a>(&'a self, texts: &'a [String]) -> EmbedFuture<'a> {
        Box::pin(async move {
            ensure!(
                texts.iter().all(|text| !text.starts_with("offline\n")),
                "provider intentionally unavailable"
            );
            Ok(texts.iter().map(|_| vec![1.0; self.0]).collect())
        })
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
    let embedder: Arc<dyn EmbeddingBackend> = Arc::new(Dummy(32));
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
    #[cfg(unix)]
    {
        use std::os::unix::fs::symlink;
        let source = linked.join("real_sources");
        fs::create_dir(&source)?;
        fs::write(source.join("b.rs"), "fn allowword() {}\n")?;
        fs::write(source.join("skip.rs"), "fn skipword() {}\n")?;
        fs::write(linked.join(".gitignore"), "/walk_alias/skip.rs\n")?;
        fs::write(fixture.join("outside.rs"), "fn outsideword() {}\n")?;
        symlink("real_sources", linked.join("walk_alias"))?;
        symlink("real_sources/b.rs", linked.join("file_alias.rs"))?;
        symlink("../outside.rs", linked.join("outside_alias.rs"))?;
        symlink(fixture.join("returns"), linked.join("reentry.rs"))?;
        symlink(source.join("b.rs"), fixture.join("returns"))?;
        symlink("b.rs-loop", source.join("loop.rs"))?;
        symlink("loop.rs", source.join("b.rs-loop"))?;
    }
    ensure!(worktrees::resolve(&client, &linked).await?.is_none());

    let mut config = GlobalConfig::default();
    config.database.host = target.host;
    config.database.port = target.port;
    config.database.dbname = target.database;
    config.database.user = target.user;
    let mut context = SearchContext {
        client: Arc::new(client),
        embedder,
        embedding_dim: 32,
        config,
        family_embedders: Default::default(),
        record_usage: false,
    };
    let id = Uuid::new_v4().to_string();
    let args =
        json!({"symbol": "alpha", "relation": "callees", "repo": linked, "operation_id": id});
    let git = repo_resolver::discover_git_checkout(&linked)
        .await?
        .unwrap();
    let merge = git.git_dir.join("MERGE_HEAD");
    fs::write(&merge, "0000000000000000000000000000000000000000\n")?;
    let pending = dispatch_tool(&context, "search_structural", args.clone()).await;
    ensure!(
        pending.is_err(),
        "a new checkout cannot publish during a merge"
    );
    ensure!(
        muninn_core::owned_control::mcp_request_owner(context.client.as_ref(), &id).await?
            == Some(Some(repo.id)),
        "the blocked first search did not save its request"
    );
    fs::remove_file(merge)?;
    context.client = Arc::new(db::connect(&context.config.database).await?);
    let continued =
        dispatch_tool(&context, "continue_request", json!({"operation_id": id})).await?;
    ensure!(continued["resumed"] == true && continued["finished"] == true);
    let response = &continued["result"];
    ensure!(dispatch_tool(&context, "search_structural", args.clone()).await? == *response);
    let mut different = args;
    different["symbol"] = json!("beta");
    ensure!(dispatch_tool(&context, "search_structural", different)
        .await
        .is_err());
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
    let candidates = response["candidates"].as_array().unwrap();
    ensure!(
        candidates.len() == 1
            && candidates[0]["source"]["name"] == "alpha"
            && candidates[0]["target"] == symbols[0]
            && candidates[0]["relation"] == "Calls"
            && candidates[0]["source"]["file_path"]
                .as_str()
                .is_some_and(|path| path.starts_with(linked.to_str().unwrap())),
        "relationship evidence must describe both endpoints in the linked checkout: {response}"
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
    #[cfg(unix)]
    {
        let by_word = |query| {
            dispatch_tool(
                &context,
                "search_fulltext",
                json!({"query": query, "repo": linked}),
            )
        };
        for (word, mut expected) in [
            (
                "allowword",
                vec!["file_alias.rs", "real_sources/b.rs", "walk_alias/b.rs"],
            ),
            ("skipword", vec!["real_sources/skip.rs"]),
            ("outsideword", vec![]),
        ] {
            let found = by_word(word).await?;
            let mut paths: Vec<_> = found["results"]
                .as_array()
                .unwrap()
                .iter()
                .map(|row| {
                    Path::new(row["file_path"].as_str().unwrap())
                        .strip_prefix(&linked)
                        .unwrap()
                        .to_str()
                        .unwrap()
                })
                .collect();
            paths.sort_unstable();
            expected.sort_unstable();
            ensure!(paths == expected, "wrong aliases for {word}: {paths:?}");
        }
    }
    let semantic_args = json!({"query": "alpha", "repo": linked, "exact": true, "limit": 1});
    let pending = dispatch_tool(&context, "search_semantic", semantic_args.clone()).await?;
    ensure!(pending["results"] == json!([]));
    ensure!(pending["coverage"]["exact"] == true && pending["coverage"]["complete"] == false);
    ensure!(pending["coverage"]["total"].as_i64().unwrap_or_default() > 0);
    ensure!(pending["coverage"]["total"] == pending["coverage"]["pending"]);
    let mut writer = db::connect(&context.config.database).await?;
    ensure!(muninn_core::pipeline::backfill_once(&mut writer, repo.id, &Dummy(32), 32).await? > 0);
    let exact = dispatch_tool(&context, "search_semantic", semantic_args.clone()).await?;
    ensure!(exact["coverage"]["complete"] == true);
    ensure!(exact["results"]
        .as_array()
        .is_some_and(|rows| rows.len() == 1));
    let mut approximate_args = semantic_args;
    approximate_args["exact"] = json!(false);
    let approximate = dispatch_tool(&context, "search_semantic", approximate_args).await?;
    ensure!(approximate["coverage"]["exact"] == false);
    ensure!(approximate["coverage"]["complete"] == true);
    ensure!(
        approximate["coverage"]["candidate_count"]
            .as_i64()
            .unwrap_or_default()
            > 0
    );
    ensure!(exact["results"] == approximate["results"]);
    check_note_receipts(&mut context, &fixture).await?;
    let mut client = Arc::try_unwrap(context.client)
        .map_err(|_| anyhow::anyhow!("test client is still shared"))?;
    store::delete_repo(&mut client, repo.id).await?;
    Ok(())
}

async fn check_note_receipts(context: &mut SearchContext, fixture: &Path) -> Result<()> {
    use muninn_core::family_policy::{Backend, Policy};
    let root = fixture.join("notes");
    fs::create_dir(&root)?;
    let mut policy = Policy::shipped("scoped notes".into());
    policy.embeddings.backend = Backend::Local;
    policy.embeddings.model = None;
    let registered = dispatch_tool(
        context,
        "register_family",
        json!({
            "repo": root, "draft": {"api_version": 1, "policy": policy}
        }),
    )
    .await?;
    let family = Uuid::parse_str(registered["family_id"].as_str().unwrap())?;
    context.config.embeddings.backend = muninn_core::config::EmbeddingBackend::Local;
    context.config.embeddings.model = None;
    context.embedder = Arc::new(Dummy(512));
    let id = Uuid::new_v4().to_string();
    let args = json!({"repo": root, "title": "kept", "body": "same request", "operation_id": id});
    let (left, right) = tokio::try_join!(
        dispatch_tool(context, "record_knowledge", args.clone()),
        dispatch_tool(context, "record_knowledge", args)
    )?;
    ensure!(left == right);
    let list = dispatch_tool(context, "list_knowledge", json!({"repo": root})).await?;
    ensure!(list.as_array().is_some_and(|items| items.len() == 1));
    let receipt = dispatch_tool(context, "continue_request", json!({"operation_id": id})).await?;
    ensure!(receipt["result"] == left);
    let deletion = Uuid::new_v4().to_string();
    let args = json!({"repo": root, "id": left["id"], "operation_id": deletion});
    ensure!(dispatch_tool(context, "delete_knowledge", args.clone()).await?["deleted"] == true);
    ensure!(dispatch_tool(context, "delete_knowledge", args).await?["deleted"] == true);
    let offline = dispatch_tool(context, "record_knowledge", json!({
        "repo": root, "title": "offline", "body": "provider is unavailable", "operation_id": Uuid::new_v4()
    })).await?;
    let saved_offline = Uuid::parse_str(offline["id"].as_str().unwrap())?;
    ensure!(context
        .client
        .query_one(
            "SELECT embedding IS NULL FROM public.knowledge WHERE id=$1",
            &[&saved_offline]
        )
        .await?
        .get::<_, bool>(0));
    let forgotten = dispatch_tool(
        context,
        "record_knowledge",
        json!({
            "repo": root, "title": "forgotten", "body": "owned by the removed family"
        }),
    )
    .await?;
    dispatch_tool(
        context,
        "start_family",
        json!({
            "repo": root, "draft": {
                "api_version": 1, "expected_family_id": family, "expected_revision": 1,
            }
        }),
    )
    .await?;
    fs::write(root.join("text.txt"), "retirement example")?;
    let mut writer = db::connect(&context.config.database).await?;
    muninn_core::pipeline::index_repo(
        &mut writer,
        family,
        &root,
        Arc::clone(&context.embedder),
        8,
        512,
        &[],
        &[],
        |_, _, _| {},
    )
    .await?;
    let schema = store::repo_schema(family);
    let counts = format!(
        "SELECT (SELECT count(*) FROM {schema}.chunks),
        (SELECT count(*) FROM {schema}.policy_versions),
        (SELECT count(*) FROM public.knowledge WHERE family_id=$1)"
    );
    let before = writer.query_one(&counts, &[&family]).await?;
    ensure!(before.get::<_, i64>(0) > 0);
    let recreate = json!({"repo": root, "draft": {
        "api_version": 1, "expected_family_id": family, "expected_revision": 1,
        "backend": "openai", "model": "text-embedding-3-small"
    }});
    ensure!(dispatch_tool(context, "recreate_index", recreate.clone()).await?["recreated"] == true);
    let saved_note = Uuid::parse_str(forgotten["id"].as_str().unwrap())?;
    let note = writer
        .query_one(
            "SELECT body,embedding IS NULL FROM public.knowledge WHERE id=$1",
            &[&saved_note],
        )
        .await?;
    ensure!(note.get::<_, String>(0) == "owned by the removed family");
    ensure!(note.get::<_, bool>(1));
    let searchable = dispatch_tool(
        context,
        "search_knowledge",
        json!({
            "repo": root, "query": "forgotten"
        }),
    )
    .await?;
    ensure!(searchable["semantic_available"] == false);
    ensure!(searchable["results"][0]["id"] == forgotten["id"]);
    ensure!(
        writer
            .query_one(&counts, &[&family])
            .await?
            .get::<_, i64>(0)
            == 0
    );
    muninn_core::pipeline::index_repo(
        &mut writer,
        family,
        &root,
        Arc::new(Dummy(1536)),
        8,
        1536,
        &[],
        &[],
        |_, _, _| {},
    )
    .await?;
    ensure!(dispatch_tool(context, "recreate_index", recreate).await?["recreated"] == false);
    let checkout_sql =
        format!("SELECT id FROM {schema}.checkouts WHERE registration_state='active'");
    let prior_checkout: Uuid = writer.query_one(&checkout_sql, &[]).await?.get(0);
    git(&root, &["init", "-b", "main"])?;
    git(&root, &["config", "user.name", "Fixture"])?;
    git(&root, &["config", "user.email", "fixture@example.invalid"])?;
    git(&root, &["add", "."])?;
    git(&root, &["commit", "-m", "convert"])?;
    let convert = json!({"repo": root, "draft": {
        "api_version": 1, "expected_family_id": family, "expected_revision": 2
    }});
    ensure!(
        dispatch_tool(context, "convert_directory", convert.clone()).await?["converted"] == true
    );
    ensure!(dispatch_tool(context, "convert_directory", convert).await?["converted"] == false);
    let converted_checkout: Uuid = writer.query_one(&checkout_sql, &[]).await?.get(0);
    ensure!(converted_checkout == prior_checkout);
    let before = writer.query_one(&counts, &[&family]).await?;
    ensure!(before.get::<_, i64>(0) > 0);
    dispatch_tool(context, "unregister_family", json!({"repo": root})).await?;
    let after = writer.query_one(&counts, &[&family]).await?;
    ensure!(after.get::<_, i64>(0) == 0);
    ensure!(before.get::<_, i64>(1) == after.get::<_, i64>(1));
    ensure!(before.get::<_, i64>(2) == after.get::<_, i64>(2));
    dispatch_tool(context, "forget_repository", json!({"repo": root})).await?;
    let forgotten_id = Uuid::parse_str(forgotten["id"].as_str().unwrap())?;
    let remains: bool = context
        .client
        .query_one(
            "SELECT EXISTS(SELECT FROM public.knowledge WHERE id=$1)",
            &[&forgotten_id],
        )
        .await?
        .get(0);
    ensure!(!remains);
    let compacted = dispatch_tool(context, "continue_request", json!({"operation_id": id})).await?;
    ensure!(compacted["resumed"] == false);
    ensure!(compacted.get("result").is_none());
    Ok(())
}
