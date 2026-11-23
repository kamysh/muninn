//! Independently published checkout memberships in family-shared file versions.
use crate::pipeline::SkipRecord;
use crate::{
    embeddings::EmbeddingBackend,
    family_store::StoredPath,
    graph, parser, pipeline,
    repo_resolver::{self, GitCheckout},
    store,
    types::*,
};
use anyhow::{ensure, Context, Result};
use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    path::{Path, PathBuf},
    sync::Arc,
};
use tokio_postgres::{Client, Transaction};
use uuid::Uuid;

mod initial;
mod prepared;
mod search;
pub use search::{fulltext_search, hybrid_search, semantic_search};

#[derive(Debug, Clone)]
pub struct Target {
    pub family: Uuid,
    pub checkout: Uuid,
    pub graph: Uuid,
    pub root: PathBuf,
}

#[derive(Debug)]
pub struct PendingIndex(pub PathBuf);

impl std::fmt::Display for PendingIndex {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            formatter,
            "worktree has no completed index yet: {}",
            self.0.display()
        )
    }
}

impl std::error::Error for PendingIndex {}

fn schema(family: Uuid) -> String {
    format!("\"{}\"", store::repo_schema(family))
}

async fn ensure_checkout_schema(client: &mut Client, family: Uuid) -> Result<()> {
    let schema = store::repo_schema(family);
    let exists: bool = client
        .query_one(
            "SELECT to_regclass($1) IS NOT NULL",
            &[&format!("{schema}.checkout_file_versions")],
        )
        .await?
        .get(0);
    if !exists {
        crate::db::run_repo_migrations(client, &schema).await?;
    }
    Ok(())
}

pub(crate) async fn lock(tx: &Transaction<'_>, family: Uuid) -> Result<()> {
    tx.query_one(
        "SELECT pg_advisory_xact_lock(hashtextextended($1, 771913))",
        &[&family.to_string()],
    )
    .await?;
    Ok(())
}

/// Existing registration for a checkout; family configuration still comes
/// from the original registered root during the core-runtime rollout.
pub async fn registered_family(client: &Client, path: &Path) -> Result<Option<Repo>> {
    let path = tokio::fs::canonicalize(path).await?;
    if let Some(repo) = store::get_repo_by_path(client, &path.to_string_lossy()).await? {
        return Ok(Some(repo));
    }
    let identity = crate::family_store::CheckoutIdentity::discover(&path).await?;
    if let Some(family) = crate::family_store::lookup_family(client, &identity.family).await? {
        return Ok(store::list_repos(client)
            .await?
            .into_iter()
            .find(|repo| repo.id == family.id));
    }
    let Some(git) = repo_resolver::discover_git_checkout(&path).await? else {
        return Ok(None);
    };
    for repo in store::list_repos(client).await? {
        if let Ok(Some(candidate)) =
            repo_resolver::discover_git_checkout(Path::new(&repo.path)).await
        {
            if candidate.common_dir == git.common_dir && candidate.root == Path::new(&repo.path) {
                return Ok(Some(repo));
            }
        }
    }
    Ok(None)
}

pub async fn base_target(client: &Client, family: Uuid) -> Result<Option<Target>> {
    let s = schema(family);
    if !client
        .query_one(
            "SELECT to_regclass($1) IS NOT NULL",
            &[&format!("{s}.worktree_base")],
        )
        .await?
        .get::<_, bool>(0)
    {
        return Ok(None);
    }
    let row=client.query_opt(&format!("SELECT c.id,c.root FROM {s}.checkouts c JOIN {s}.worktree_base b ON b.checkout=c.id WHERE c.indexed_at IS NOT NULL"),&[]).await?;
    row.map(|row| {
        #[cfg(unix)]
        let encoding = "unix-bytes";
        #[cfg(windows)]
        let encoding = "windows-utf16le";
        Ok(Target {
            family,
            checkout: row.get(0),
            graph: family,
            root: StoredPath::from_db(encoding, row.get(1))?.to_path_buf()?,
        })
    })
    .transpose()
}

/// Resolve an indexed worktree, including a nested cwd without a config marker.
/// No registrations or migrations are performed by search.
pub async fn resolve(client: &Client, path: &Path) -> Result<Option<Target>> {
    let root = if let Some(git) = repo_resolver::discover_git_checkout(path).await? {
        git.root
    } else {
        tokio::fs::canonicalize(path).await?
    };
    let stored = StoredPath::canonicalize(&root).await?;
    let Some(repo) = registered_family(client, &root).await? else {
        return Ok(None);
    };
    let s = schema(repo.id);
    let exists: bool = client
        .query_one(
            "SELECT to_regclass($1) IS NOT NULL",
            &[&format!("{}.worktree_base", s)],
        )
        .await?
        .get(0);
    if !exists {
        return Ok(None);
    }
    let Some(row) = client.query_opt(&format!(
        "SELECT c.id,c.indexed_at IS NOT NULL,b.checkout=c.id AS is_base FROM {s}.checkouts c CROSS JOIN {s}.worktree_base b WHERE c.root=$1 AND c.registration_state='active'"), &[&stored.bytes()]).await? else {
        return Ok(None);
    };
    let is_base: bool = row.get(2);
    if !row.get::<_, bool>(1) {
        return if is_base && repo.ever_indexed {
            // An interrupted first conversion can still serve the primary index.
            Ok(None)
        } else {
            Err(PendingIndex(root).into())
        };
    }
    let id: Uuid = row.get(0);
    Ok(Some(Target {
        family: repo.id,
        checkout: id,
        graph: if is_base { repo.id } else { id },
        root,
    }))
}

/// Return the primary checkout and all registered Git worktree locations.
async fn discovery(root: &Path) -> Result<(GitCheckout, Vec<repo_resolver::GitWorktree>)> {
    let checkout = repo_resolver::discover_git_checkout(root)
        .await?
        .context("not a Git checkout")?;
    let entries = repo_resolver::list_git_worktrees(&checkout.common_dir).await?;
    let first = entries.first().context("empty Git worktree registry")?;
    ensure!(!first.bare, "a non-bare primary checkout is required");
    let primary = repo_resolver::discover_git_checkout(&first.path)
        .await?
        .context("primary checkout unavailable")?;
    ensure!(
        primary.git_dir == primary.common_dir,
        "primary Git checkout identity is ambiguous"
    );
    Ok((primary, entries))
}

/// Discover/register worktrees, reconcile each available checkout, and retire
/// those absent from a successfully read Git registry or confirmed missing on
/// disk. Other filesystem errors retain their last index. No Git operation is
/// performed.
#[allow(clippy::too_many_arguments)]
pub async fn reconcile_family(
    client: &mut Client,
    family: Uuid,
    root: &Path,
    embedder: Arc<dyn EmbeddingBackend>,
    batch_size: usize,
    dimension: usize,
    exclude: &[String],
    vendor: &[String],
    progress: impl Fn(usize, usize, &Path),
) -> Result<(BatchOutcome, Vec<SkipRecord>)> {
    reconcile_changed_family(
        client, family, root, embedder, batch_size, dimension, exclude, vendor, progress, None,
    )
    .await
}

/// Event-driven reconciliation; periodic discovery still initializes newly seen
/// worktrees. Only affected/previously failed checkouts need their files read.
#[allow(clippy::too_many_arguments)]
pub async fn reconcile_changed_family(
    client: &mut Client,
    family: Uuid,
    root: &Path,
    embedder: Arc<dyn EmbeddingBackend>,
    batch_size: usize,
    dimension: usize,
    exclude: &[String],
    vendor: &[String],
    progress: impl Fn(usize, usize, &Path),
    changed: Option<&[PathBuf]>,
) -> Result<(BatchOutcome, Vec<SkipRecord>)> {
    reconcile_family_targets(
        client, family, root, embedder, batch_size, dimension, exclude, vendor, progress, changed,
        None,
    )
    .await
}

/// Initialize only the requested checkout. Search uses this path instead of
/// waiting for the family watcher to discover and index every pending worktree.
#[allow(clippy::too_many_arguments)]
pub async fn reconcile_requested_checkout(
    client: &mut Client,
    family: Uuid,
    root: &Path,
    requested: &Path,
    embedder: Arc<dyn EmbeddingBackend>,
    batch_size: usize,
    dimension: usize,
    exclude: &[String],
    vendor: &[String],
) -> Result<()> {
    // MCP can reach an already registered family before its watcher has
    // started. Apply the new per-repo table migration on this path as well.
    ensure_checkout_schema(client, family).await?;
    let (_, skips) = reconcile_family_targets(
        client,
        family,
        root,
        embedder,
        batch_size,
        dimension,
        exclude,
        vendor,
        |_, _, _| {},
        None,
        Some(requested),
    )
    .await?;
    if let Some(skip) = skips.into_iter().find(|skip| skip.path == requested) {
        anyhow::bail!("indexing {}: {}", requested.display(), skip.reason);
    }
    ensure!(
        resolve(client, requested).await?.is_some(),
        "requested worktree was not registered: {}",
        requested.display()
    );
    Ok(())
}

#[allow(clippy::too_many_arguments)]
async fn reconcile_family_targets(
    client: &mut Client,
    family: Uuid,
    root: &Path,
    _embedder: Arc<dyn EmbeddingBackend>,
    _batch_size: usize,
    _dimension: usize,
    exclude: &[String],
    vendor: &[String],
    progress: impl Fn(usize, usize, &Path),
    changed: Option<&[PathBuf]>,
    requested: Option<&Path>,
) -> Result<(BatchOutcome, Vec<SkipRecord>)> {
    ensure_checkout_schema(client, family).await?;
    if let Some(view) = crate::family_policy::runtime::policy(client, family).await? {
        ensure!(
            view.indexing_enabled && !view.paused,
            "family indexing is not enabled or is paused"
        );
    }
    let (primary, entries) = discovery(root).await?;
    if requested.is_none()
        && changed.is_some_and(|paths| {
            !paths.is_empty()
                && paths
                    .iter()
                    .all(|path| git_bookkeeping(&primary.common_dir, path))
        })
    {
        return Ok((BatchOutcome::AllSucceeded, Vec::new()));
    }
    let s = schema(family);
    let mut targets = Vec::new();
    let mut listed = Vec::new();
    let mut missing_listed = Vec::new();
    let mut available = Vec::new();
    for entry in &entries {
        if requested.is_some_and(|path| path != entry.path && primary.root != entry.path) {
            continue;
        }
        // Git can keep a deleted worktree in its registry until pruning. A
        // concrete NotFound is removal evidence; access errors are not.
        if matches!(tokio::fs::metadata(&entry.path).await, Err(ref error) if error.kind() == std::io::ErrorKind::NotFound)
        {
            missing_listed.push(entry.path.clone());
        } else {
            listed.push(entry.path.clone());
        }
        if entry.bare {
            continue;
        }
        let Some(git) = repo_resolver::discover_git_checkout(&entry.path)
            .await
            .ok()
            .flatten()
        else {
            continue;
        };
        ensure!(
            git.common_dir == primary.common_dir,
            "worktree changed family during discovery"
        );
        let stored = StoredPath::canonicalize(&git.root).await?;
        let admin = StoredPath::canonicalize(&git.git_dir).await?;
        available.push((git, stored, admin));
    }
    let tx = client.transaction().await?;
    // Coordinate only competing Git-registry reconciliations. Search and
    // checkout publication never take the registry lock.
    tx.query_one(
        "SELECT pg_advisory_xact_lock(hashtextextended($1, 317530))",
        &[&family.to_string()],
    )
    .await?;
    // Retire absent identities before inserting replacements. A moved checkout
    // still has its Git administrative identity, even though its old root is
    // absent; a briefly missing Git-listed entry keeps its completed view.
    for row in tx
        .query(
            &format!(
                "SELECT id,root,git_dir,missing_since FROM {s}.checkouts WHERE registration_state<>'retired'"
            ),
            &[],
        )
        .await?
    {
        let id: Uuid = row.get(0);
        let bytes: Vec<u8> = row.get(1);
        let admin: Option<Vec<u8>> = row.get(2);
        let missing_since: Option<chrono::DateTime<chrono::Utc>> = row.get(3);
        #[cfg(unix)]
        let encoding = "unix-bytes";
        #[cfg(windows)]
        let encoding = "windows-utf16le";
        let path = StoredPath::from_db(encoding, bytes)?.to_path_buf()?;
        if requested.is_some_and(|requested| requested != path && primary.root != path)
            && !available.iter().any(|(_, _, git_dir)| Some(git_dir.bytes()) == admin.as_deref())
        {
            continue;
        }
        let identity_present = available
            .iter()
            .any(|(_, _, git_dir)| Some(git_dir.bytes()) == admin.as_deref());
        let replaced = available.iter().any(|(_, root, git_dir)| {
            root.to_path_buf().ok().as_ref() == Some(&path)
                && Some(git_dir.bytes()) != admin.as_deref()
        });
        let missing_on_disk = missing_listed.contains(&path);
        if missing_on_disk
            && !matches!(tokio::fs::metadata(&path).await, Err(ref error) if error.kind() == std::io::ErrorKind::NotFound)
        {
            continue;
        }
        if missing_on_disk {
            if missing_since.is_none() {
                tx.execute(
                    &format!("UPDATE {s}.checkouts SET missing_since=now() WHERE id=$1"),
                    &[&id],
                )
                .await?;
                continue;
            }
            let elapsed: bool = tx
                .query_one(
                    "SELECT $1::timestamptz <= now() - interval '60 seconds'",
                    &[&missing_since],
                )
                .await?
                .get(0);
            if !elapsed {
                continue;
            }
        } else if missing_since.is_some() {
            tx.execute(
                &format!("UPDATE {s}.checkouts SET missing_since=NULL WHERE id=$1"),
                &[&id],
            )
            .await?;
        }
        if !identity_present && (!listed.contains(&path) || replaced) {
            // Prevent a same-checkout publication from committing between
            // removing its membership and marking its registration retired.
            tx.query_one(&format!("SELECT id FROM {s}.checkouts WHERE id=$1 FOR UPDATE"), &[&id]).await?;
            // Keep a missing checkout's stored view for explicit recovery.
            // Registry removal keeps its established storage cleanup behavior.
            if !missing_on_disk {
                graph::drop_graph(tx.client(), id).await?;
                tx.execute(
                    &format!("DELETE FROM {s}.checkout_structural_snapshots WHERE checkout=$1"),
                    &[&id],
                )
                .await?;
                tx.execute(
                    &format!("DELETE FROM {s}.checkout_file_versions WHERE checkout=$1"),
                    &[&id],
                )
                .await?;
            }
            crate::maintenance::forget(&tx, family, id).await?;
            tx.execute(
                &format!("DELETE FROM {s}.checkout_prepared_files WHERE checkout=$1"),
                &[&id],
            )
            .await?;
            tx.execute(&format!("UPDATE {s}.checkouts SET registration_state='retired',retired_at=now(),indexed_at=NULL WHERE id=$1"), &[&id]).await?;
        }
    }
    // Apply relocations before additions so the old location can be reused by
    // a newly created worktree in the same discovery pass.
    let mut relocated = BTreeSet::new();
    for (_, stored, admin) in &available {
        if let Some(row) = tx.query_opt(
            &format!("SELECT id,root FROM {s}.checkouts WHERE git_dir=$1 AND registration_state<>'retired'"),
            &[&admin.bytes()],
        ).await? {
            let id: Uuid = row.get(0);
            if row.get::<_, Vec<u8>>(1) != stored.bytes() {
                tx.execute(&format!("UPDATE {s}.checkouts SET root=$1 WHERE id=$2"), &[&stored.bytes(), &id]).await?;
                relocated.insert(id);
            }
        }
    }
    for (git, stored, admin) in available {
        let existing = tx.query_opt(
            &format!("SELECT id,registration_state,root,indexed_at IS NOT NULL FROM {s}.checkouts WHERE git_dir=$1 AND registration_state<>'retired'"),
            &[&admin.bytes()],
        ).await?;
        let mut initialized = false;
        let id = if let Some(row) = existing {
            let id: Uuid = row.get(0);
            let moved = relocated.contains(&id);
            if row.get::<_, String>(1) == "suppressed" {
                continue;
            }
            initialized = row.get::<_, bool>(3) && !moved;
            id
        } else {
            let id = Uuid::new_v4();
            tx.execute(
                &format!("INSERT INTO {s}.checkouts(id,root,git_dir) VALUES($1,$2,$3)"),
                &[&id, &stored.bytes(), &admin.bytes()],
            )
            .await?;
            id
        };
        let is_base = git.root == primary.root;
        if is_base {
            tx.execute(&format!("INSERT INTO {s}.worktree_base(singleton,checkout) VALUES(true,$1) ON CONFLICT(singleton) DO NOTHING"),&[&id]).await?;
            let base: Uuid = tx
                .query_one(&format!("SELECT checkout FROM {s}.worktree_base"), &[])
                .await?
                .get(0);
            ensure!(
                base == id,
                "primary checkout changed; refusing automatic base replacement"
            );
        }
        targets.push((
            initialized,
            Target {
                family,
                checkout: id,
                graph: if is_base { family } else { id },
                root: git.root.clone(),
            },
            git,
        ));
    }
    ensure!(
        targets.first().map(|(_, t, _)| &t.root) == Some(&primary.root),
        "primary checkout cannot be indexed"
    );
    if requested.is_none() {
        let already_pending = crate::maintenance::pending(&tx, family).await?;
        for (initialized, target, git) in &targets {
            let refresh =
                changed.is_some_and(|paths| paths.iter().any(|path| selection_event(git, path)));
            if refresh || (!initialized && already_pending) {
                crate::maintenance::request(&tx, family, target.checkout).await?;
            }
        }
        // A pre-discovery policy request used the directory/family target.
        if crate::maintenance::generation(&tx, family, family)
            .await?
            .is_some()
        {
            for (_, target, _) in &targets {
                crate::maintenance::request(&tx, family, target.checkout).await?;
            }
            crate::maintenance::forget(&tx, family, family).await?;
        }
    }
    let pending: BTreeSet<Uuid> = tx
        .query(
            &format!("SELECT target FROM {s}.selection_maintenance WHERE requested>completed"),
            &[],
        )
        .await?
        .into_iter()
        .map(|row| row.get(0))
        .collect();
    let unreadable: BTreeSet<Uuid> = tx.query(
        &format!("SELECT id FROM {s}.checkouts WHERE registration_state='active' AND cardinality(unreadable_paths)>0"),
        &[],
    ).await?.into_iter().map(|row| row.get(0)).collect();
    tx.commit().await?;
    let mut skips = Vec::new();
    let mut completed = 0;
    let mut attempted = 0;
    for (initialized, target, git) in targets {
        if requested.is_some_and(|path| path != target.root) {
            continue;
        }
        if initialized
            && !pending.contains(&target.checkout)
            && !unreadable.contains(&target.checkout)
            && changed.is_some_and(|paths| {
                !paths
                    .iter()
                    .any(|path| source_event(&git, path) || git_operation_event(&git, path))
            })
        {
            continue;
        }
        attempted += 1;
        match reconcile_checkout(
            client,
            &target,
            &git,
            exclude,
            vendor,
            &progress,
            !initialized || pending.contains(&target.checkout),
            if pending.contains(&target.checkout) {
                None
            } else {
                changed
            },
        )
        .await
        {
            Ok(()) => completed += 1,
            Err(e) => {
                let reason = format!("{e:#}");
                crate::maintenance::failed(client, family, target.checkout, &reason).await?;
                skips.push(SkipRecord {
                    path: target.root,
                    reason,
                });
            }
        }
    }
    if requested.is_none() {
        garbage_collect(client, &s).await?;
    }
    ensure!(
        completed > 0 || attempted == 0 || changed.is_some(),
        "no checkout reconciled: {}",
        skips
            .iter()
            .map(|s| format!("{}: {}", s.path.display(), s.reason))
            .collect::<Vec<_>>()
            .join("; ")
    );
    Ok((
        if skips.is_empty() {
            BatchOutcome::AllSucceeded
        } else {
            BatchOutcome::SomeSucceeded
        },
        skips,
    ))
}

#[derive(Clone)]
struct SourceFile {
    path: String,
    // An inherited published version needs no filesystem content read.
    source: Option<String>,
    source_size: usize,
    hash: Vec<u8>,
    tier: Tier,
}

#[derive(Default)]
struct Scan {
    files: Vec<SourceFile>,
    unreadable: BTreeSet<String>,
}

fn io_path(error: &ignore::Error) -> Option<&Path> {
    match error {
        ignore::Error::WithPath { path, .. } => Some(path),
        ignore::Error::WithDepth { err, .. } | ignore::Error::WithLineNumber { err, .. } => {
            io_path(err)
        }
        _ => None,
    }
}

async fn scan(root: &Path, selection: &crate::family_policy::runtime::Selection) -> Result<Scan> {
    let walker = selection.walker(root);
    let mut paths = Vec::new();
    let mut scan = Scan::default();
    for entry in walker {
        let entry = match entry {
            Ok(entry) => entry,
            Err(error) if error.io_error().is_some() => {
                if let Some(path) = io_path(&error)
                    .and_then(|path| path.strip_prefix(root).ok())
                    .filter(|path| !path.as_os_str().is_empty())
                {
                    scan.unreadable.insert(
                        path.to_str()
                            .context("unreadable path is not UTF-8")?
                            .to_owned(),
                    );
                    continue;
                }
                return Err(error.into());
            }
            Err(error) => return Err(error.into()),
        };
        if !entry.file_type().is_some_and(|t| t.is_file()) {
            continue;
        }
        paths.push(entry.path().strip_prefix(root)?.to_path_buf());
    }
    let ignored = crate::git_ignore::check(root, &paths).await?;
    for (rel, ignored) in paths.iter().zip(ignored) {
        if selection.classify_with_git(rel, false, ignored) == pipeline::Decision::Drop {
            continue;
        }
        if let Some(file) = observe_file(root, selection, rel, &mut scan.unreadable)? {
            scan.files.push(file);
        }
    }
    scan.files.sort_by(|a, b| a.path.cmp(&b.path));
    Ok(scan)
}

fn observe_file(
    root: &Path,
    selection: &crate::family_policy::runtime::Selection,
    path: &Path,
    unreadable: &mut BTreeSet<String>,
) -> Result<Option<SourceFile>> {
    match scan_changed_file(root, selection, path) {
        Err(error) if error.downcast_ref::<std::io::Error>().is_some() => {
            unreadable.insert(
                path.to_str()
                    .context("unreadable path is not UTF-8")?
                    .to_owned(),
            );
            tracing::warn!(checkout=%root.display(), path=%path.display(), %error, "file remains pending");
            Ok(None)
        }
        result => result,
    }
}

fn git_bookkeeping(common_dir: &Path, path: &Path) -> bool {
    let Ok(relative) = path.strip_prefix(common_dir) else {
        return false;
    };
    let admin_relative = if let Ok(linked) = relative.strip_prefix("worktrees") {
        let mut components = linked.components();
        components.next();
        components.as_path()
    } else {
        relative
    };
    ["index", "index.lock"]
        .iter()
        .any(|name| admin_relative == Path::new(name))
        || ["objects", "refs", "logs"]
            .iter()
            .any(|name| admin_relative.starts_with(name))
}

fn source_event(git: &GitCheckout, path: &Path) -> bool {
    path.starts_with(&git.root)
        && !path.starts_with(&git.common_dir)
        && !path.starts_with(&git.git_dir)
        && path != git.root.join(".git")
}

fn selection_event(git: &GitCheckout, path: &Path) -> bool {
    ["info", "info/exclude", "config"]
        .iter()
        .any(|name| path == git.common_dir.join(name))
        || path == git.git_dir.join("config.worktree")
        || (source_event(git, path) && path.file_name().is_some_and(|name| name == ".gitignore"))
}

fn git_operation_event(git: &GitCheckout, path: &Path) -> bool {
    path.strip_prefix(&git.git_dir).is_ok_and(|relative| {
        ["HEAD", "MERGE_HEAD", "rebase-merge", "rebase-apply"]
            .iter()
            .any(|name| relative.starts_with(name))
    })
}

// Directory and Git operation events may affect paths not named in the event.
// Source edits otherwise reconcile just the reported paths.
fn changed_paths(
    target: &Target,
    git: &GitCheckout,
    events: Option<&[PathBuf]>,
    previous: &BTreeMap<String, Uuid>,
) -> Option<Vec<PathBuf>> {
    let mut paths = BTreeSet::new();
    for event in events? {
        if selection_event(git, event) || git_operation_event(git, event) {
            return None;
        }
        if !source_event(git, event) {
            continue;
        }
        let Ok(relative) = event.strip_prefix(&target.root) else {
            continue;
        };
        if relative.as_os_str().is_empty()
            || relative
                .components()
                .any(|c| !matches!(c, std::path::Component::Normal(_)))
            || event.is_dir()
            || previous.keys().any(|path| {
                let path = Path::new(path);
                path != relative && path.starts_with(relative)
            })
        {
            return None;
        }
        paths.insert(relative.to_path_buf());
    }
    Some(paths.into_iter().collect())
}

// Apply the same selection and admission rules as a full scan to one event.
fn scan_changed_file(
    root: &Path,
    selection: &crate::family_policy::runtime::Selection,
    relative: &Path,
) -> Result<Option<SourceFile>> {
    for ancestor in relative
        .ancestors()
        .skip(1)
        .filter(|p| !p.as_os_str().is_empty())
    {
        if selection.classify(ancestor, true) == pipeline::Decision::Drop {
            return Ok(None);
        }
        match std::fs::symlink_metadata(root.join(ancestor)) {
            Ok(metadata) if metadata.file_type().is_dir() => {}
            Ok(_) => return Ok(None),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(None),
            Err(error) => return Err(error.into()),
        }
    }
    let decision = selection.classify(relative, false);
    if decision == pipeline::Decision::Drop {
        return Ok(None);
    }
    let path = root.join(relative);
    let metadata = match std::fs::symlink_metadata(&path) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(None),
        Err(error) => return Err(error.into()),
    };
    if !metadata.file_type().is_file() || metadata.len() > 10 * 1024 * 1024 {
        return Ok(None);
    }
    let bytes = match std::fs::read(&path) {
        Ok(bytes) => bytes,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(None),
        Err(error) => return Err(error.into()),
    };
    if bytes.len() > 10 * 1024 * 1024 || bytes.contains(&0) {
        return Ok(None);
    }
    let Ok(source) = String::from_utf8(bytes) else {
        return Ok(None);
    };
    Ok(Some(SourceFile {
        path: relative
            .to_str()
            .context("indexed file path is not UTF-8")?
            .to_owned(),
        hash: content_sha256(&source),
        source_size: source.len(),
        source: Some(source),
        tier: if decision == pipeline::Decision::Tier2 {
            Tier::Tier2
        } else {
            Tier::Tier1
        },
    }))
}

async fn git_stamp(git: &GitCheckout) -> Result<String> {
    ensure!(
        !repo_resolver::inspect_git_operation_state(git)
            .await?
            .is_blocked(),
        "Git operation incomplete; retaining last index"
    );
    let out = tokio::process::Command::new("git")
        .arg("-C")
        .arg(&git.root)
        .args(["rev-parse", "--verify", "HEAD"])
        .env("GIT_OPTIONAL_LOCKS", "0")
        .output()
        .await?;
    // Unborn repositories have no HEAD; file validation still applies.
    Ok(if out.status.success() {
        String::from_utf8(out.stdout)?
    } else {
        String::new()
    })
}

async fn manifest(
    client: &impl tokio_postgres::GenericClient,
    s: &str,
    checkout: Uuid,
) -> Result<BTreeMap<String, Uuid>> {
    let rows=client.query(&format!("SELECT v.path,v.id FROM {s}.checkout_file_versions m JOIN {s}.file_versions v ON v.id=m.version WHERE m.checkout=$1"),&[&checkout]).await?;
    Ok(rows.into_iter().map(|r| (r.get(0), r.get(1))).collect())
}

#[allow(clippy::too_many_arguments)]
async fn reconcile_checkout(
    client: &mut Client,
    target: &Target,
    git: &GitCheckout,
    exclude: &[String],
    vendor: &[String],
    progress: &impl Fn(usize, usize, &Path),
    refresh_graph: bool,
    events: Option<&[PathBuf]>,
) -> Result<()> {
    loop {
        if reconcile_checkout_pass(
            client,
            target,
            git,
            exclude,
            vendor,
            progress,
            refresh_graph,
            events,
        )
        .await?
        {
            return Ok(());
        }
    }
}

#[allow(clippy::too_many_arguments)]
async fn reconcile_checkout_pass(
    client: &mut Client,
    target: &Target,
    git: &GitCheckout,
    exclude: &[String],
    vendor: &[String],
    progress: &impl Fn(usize, usize, &Path),
    refresh_graph: bool,
    events: Option<&[PathBuf]>,
) -> Result<bool> {
    let started = std::time::Instant::now();
    let stamp = git_stamp(git).await?;
    let s = schema(target.family);
    let tx = client
        .build_transaction()
        .isolation_level(tokio_postgres::IsolationLevel::RepeatableRead)
        .read_only(true)
        .start()
        .await?;
    let maintenance_generation =
        crate::maintenance::generation(&tx, target.family, target.checkout).await?;
    let refresh_graph = refresh_graph || maintenance_generation.is_some();
    let events = if maintenance_generation.is_some() {
        None
    } else {
        events
    };
    let family = tx
        .query_opt(
            "SELECT paused,storage_generation FROM public.repos WHERE id=$1 AND retired_at IS NULL",
            &[&target.family],
        )
        .await?
        .context("family removed")?;
    ensure!(!family.get::<_, bool>(0), "family is paused");
    let storage_generation: String = family.get(1);
    let row=tx.query_one(&format!("SELECT registration_state,paused,indexed_at IS NOT NULL,publication_generation,root,
        indexed_git_head,cardinality(unreadable_paths)>0 FROM {s}.checkouts WHERE id=$1"),&[&target.checkout]).await?;
    ensure!(
        row.get::<_, String>(0) == "active" && !row.get::<_, bool>(1),
        "checkout is inactive or paused"
    );
    let generation: i64 = row.get(3);
    let root: Vec<u8> = row.get(4);
    let initialized: bool = row.get(2);
    let initial_linked = !initialized && target.graph != target.family;
    let policy = crate::family_policy::runtime::policy(&tx, target.family).await?;
    let selection = crate::family_policy::runtime::Selection::new(
        &target.root,
        policy.as_ref(),
        exclude,
        vendor,
    )?;
    let previous = if initialized {
        manifest(&tx, &s, target.checkout).await?
    } else {
        BTreeMap::new()
    };
    let candidates = if initialized
        && row.get::<_, Option<String>>(5).as_deref() == Some(stamp.as_str())
        && !row.get::<_, bool>(6)
    {
        changed_paths(target, git, events, &previous)
    } else {
        None
    };
    let mut fast_changes = None;
    let mut inherited = BTreeMap::new();
    if candidates.is_some() {
        let ids: Vec<Uuid> = previous.values().copied().collect();
        for row in tx.query(
            &format!("SELECT v.id,v.path,v.content_hash,v.tier,octet_length(c.source)::bigint FROM {s}.file_versions v LEFT JOIN {s}.file_content_cache c ON c.file_version=v.id WHERE v.id=ANY($1)"),
            &[&ids],
        ).await? {
            let id: Uuid = row.get(0);
            let path: String = row.get(1);
            let length: Option<i64> = row.get(4);
            if previous.get(&path) != Some(&id) || length.is_none() {
                inherited.clear();
                break;
            }
            inherited.insert(path.clone(), SourceFile {
                path,
                hash: row.get(2),
                tier: Tier::from_i16(row.get(3)).context("invalid stored file tier")?,
                source_size: usize::try_from(length.unwrap()).context("invalid stored file size")?,
                source: None,
            });
        }
    }
    tx.commit().await?;
    let observed = if let Some(paths) = candidates.filter(|_| inherited.len() == previous.len()) {
        let mut unreadable = BTreeSet::new();
        let mut observed = Vec::with_capacity(paths.len());
        let ignored = crate::git_ignore::check(&target.root, &paths).await?;
        for (path, ignored) in paths.into_iter().zip(ignored) {
            let key = path
                .to_str()
                .context("indexed file path is not UTF-8")?
                .to_owned();
            let file =
                if selection.classify_with_git(&path, false, ignored) == pipeline::Decision::Drop {
                    None
                } else {
                    observe_file(&target.root, &selection, &path, &mut unreadable)?
                };
            inherited.remove(&key);
            if let Some(value) = &file {
                inherited.insert(key, value.clone());
            }
            observed.push((path, file));
        }
        fast_changes = Some(observed);
        Scan {
            files: inherited.into_values().collect(),
            unreadable,
        }
    } else if initial_linked {
        initial::read(&target.root, &selection).await?
    } else {
        scan(&target.root, &selection).await?
    };
    let files = &observed.files;
    let scanned = started.elapsed();
    let desired = prepared::prepare(client, target, files, &previous, progress).await?;
    let versioned = started.elapsed();
    if initial_linked && git_stamp(git).await? != stamp {
        return Ok(false);
    }
    let structural = if refresh_graph || !initialized || previous != desired {
        Some(
            prepare_graph(
                client,
                target,
                files,
                &previous,
                &desired,
                fast_changes.is_some() && !refresh_graph,
            )
            .await?,
        )
    } else {
        None
    };
    let graphed = started.elapsed();
    let tx = client.transaction().await?;
    let current = tx.query_one(
        &format!("SELECT publication_generation,root,registration_state,paused,unreadable_paths FROM {s}.checkouts WHERE id=$1 FOR UPDATE"),
        &[&target.checkout],
    ).await?;
    ensure!(
        current.get::<_, Vec<u8>>(1) == root,
        "checkout moved during indexing"
    );
    ensure!(
        current.get::<_, String>(2) == "active" && !current.get::<_, bool>(3),
        "checkout is inactive or paused"
    );
    if current.get::<_, i64>(0) != generation {
        return Ok(false);
    }
    let view_changed = structural.is_some()
        || !current
            .get::<_, Vec<String>>(4)
            .iter()
            .eq(observed.unreadable.iter());
    // Revalidate the checkout before taking the policy row lock.
    // Prepared file versions survive a stale observation or interrupted commit.
    if let Some(changes) = fast_changes.as_ref().filter(|_| view_changed) {
        let paths: Vec<_> = changes.iter().map(|(path, _)| path.clone()).collect();
        let ignored = crate::git_ignore::check(&target.root, &paths).await?;
        let mut unreadable = BTreeSet::new();
        for ((path, before), ignored) in changes.iter().zip(ignored) {
            let after =
                if selection.classify_with_git(path, false, ignored) == pipeline::Decision::Drop {
                    None
                } else {
                    observe_file(&target.root, &selection, path, &mut unreadable)?
                };
            ensure!(
                match (before, &after) {
                    (None, None) => true,
                    (Some(a), Some(b)) => a.source == b.source && a.tier == b.tier,
                    _ => false,
                },
                "files changed during indexing; retaining previous index"
            );
        }
        ensure!(
            unreadable == observed.unreadable,
            "unreadable paths changed during indexing"
        );
    } else if initial_linked {
        if !initial_matches(target, git, &selection, &observed, &stamp).await? {
            return Ok(false);
        }
    } else if view_changed {
        let after = scan(&target.root, &selection).await?;
        ensure!(
            same_scan(&observed, &after),
            "files changed during indexing; retaining previous index"
        );
    }
    if !initial_linked {
        ensure!(
            git_stamp(git).await? == stamp,
            "Git HEAD changed during indexing; retaining previous index"
        );
    }
    let family = tx
        .query_opt(
            "SELECT paused,storage_generation,indexed_at IS NULL FROM public.repos WHERE id=$1 AND retired_at IS NULL",
            &[&target.family],
        )
        .await?
        .context("family removed")?;
    ensure!(!family.get::<_, bool>(0), "family is paused");
    let current_policy = crate::family_policy::runtime::lock_policy(&tx, target.family).await?;
    if family.get::<_, String>(1) != storage_generation
        || current_policy.as_ref().map(|view| view.revision)
            != policy.as_ref().map(|view| view.revision)
        || crate::maintenance::generation(&tx, target.family, target.checkout).await?
            != maintenance_generation
    {
        return Ok(false);
    }
    if let Some((nodes, edges)) = structural {
        publish_membership(&tx, &s, target.checkout, &previous, &desired).await?;
        if target.graph == target.family {
            // Legacy rows have no reliable file-version identity. They remain
            // visible until this first complete base publication commits.
            tx.execute(
                &format!("DELETE FROM {s}.chunks WHERE file_version IS NULL"),
                &[],
            )
            .await?;
        }
        tx.execute(
            &format!("INSERT INTO {s}.checkout_structural_snapshots(checkout,nodes,edges) VALUES($1,$2,$3)
              ON CONFLICT(checkout) DO UPDATE SET nodes=EXCLUDED.nodes,edges=EXCLUDED.edges"),
            &[&target.checkout, &nodes, &edges],
        ).await.context("publish checkout structural index")?;
    }
    tx.execute(
        &format!("DELETE FROM {s}.checkout_prepared_files WHERE checkout=$1"),
        &[&target.checkout],
    )
    .await?;
    let unreadable: Vec<_> = observed.unreadable.iter().collect();
    tx.execute(&format!("UPDATE {s}.checkouts SET indexed_at=CASE WHEN $4 THEN now() ELSE indexed_at END,
        publication_generation=publication_generation+CASE WHEN $4 THEN 1 ELSE 0 END,
        indexed_git_head=$2,unreadable_paths=$3,availability='available',git_state='clear',merge_in_progress=false,
        rebase_merge_in_progress=false,rebase_apply_in_progress=false,unmerged_index=false,observed_at=now(),
        last_seen_at=now() WHERE id=$1"),&[&target.checkout,&stamp,&unreadable,&view_changed]).await?;
    if target.graph == target.family && (view_changed || family.get::<_, bool>(2)) {
        store::mark_indexed(tx.client(), target.family).await?;
    }
    if !initialized {
        store::notify_repos_changed(tx.client()).await?;
    }
    crate::maintenance::complete(&tx, target.family, target.checkout, maintenance_generation)
        .await?;
    tx.commit().await?;
    if !initialized || started.elapsed().as_secs() >= 5 {
        tracing::info!(
            checkout = %target.root.display(),
            files = files.len(),
            scan_ms = scanned.as_millis() as u64,
            versions_ms = (versioned - scanned).as_millis() as u64,
            graph_ms = (graphed - versioned).as_millis() as u64,
            finish_ms = (started.elapsed() - graphed).as_millis() as u64,
            "worktree reconciliation completed"
        );
    }
    Ok(true)
}

async fn initial_matches(
    target: &Target,
    git: &GitCheckout,
    selection: &crate::family_policy::runtime::Selection,
    observed: &Scan,
    stamp: &str,
) -> Result<bool> {
    let after = initial::read(&target.root, selection).await?;
    Ok(git_stamp(git).await? == stamp && same_scan(observed, &after))
}

fn same_scan(before: &Scan, after: &Scan) -> bool {
    before.unreadable == after.unreadable
        && before.files.len() == after.files.len()
        && before
            .files
            .iter()
            .zip(&after.files)
            .all(|(before, after)| {
                before.path == after.path
                    && before.source == after.source
                    && before.tier == after.tier
            })
}

async fn publish_membership(
    tx: &Transaction<'_>,
    s: &str,
    checkout: Uuid,
    previous: &BTreeMap<String, Uuid>,
    desired: &BTreeMap<String, Uuid>,
) -> Result<()> {
    let removed: Vec<_> = previous
        .iter()
        .filter_map(|(path, version)| (desired.get(path) != Some(version)).then_some(*version))
        .collect();
    let added: Vec<_> = desired
        .iter()
        .filter_map(|(path, version)| (previous.get(path) != Some(version)).then_some(*version))
        .collect();
    if !removed.is_empty() {
        tx.execute(
            &format!(
                "DELETE FROM {s}.checkout_file_versions WHERE checkout=$1 AND version=ANY($2)"
            ),
            &[&checkout, &removed],
        )
        .await?;
    }
    if !added.is_empty() {
        tx.execute(
            &format!("INSERT INTO {s}.checkout_file_versions(checkout,version) SELECT $1,unnest($2::uuid[])"),
            &[&checkout, &added],
        ).await?;
    }
    Ok(())
}

async fn garbage_collect(client: &mut Client, s: &str) -> Result<()> {
    let unreferenced = format!(
        "NOT EXISTS(SELECT FROM {s}.checkout_file_versions m WHERE m.version=v.id)
        AND NOT EXISTS(SELECT FROM {s}.checkout_prepared_files p WHERE p.version=v.id)"
    );
    loop {
        let tx = client.transaction().await?;
        let candidates: Vec<Uuid> = tx.query(
            &format!("SELECT v.id FROM {s}.file_versions v WHERE {unreferenced} LIMIT 64 FOR UPDATE OF v SKIP LOCKED"),
            &[],
        ).await?.into_iter().map(|row| row.get(0)).collect();
        if candidates.is_empty() {
            return Ok(());
        }
        // A fresh statement sees any reference acquired before the row lock.
        tx.execute(
            &format!("DELETE FROM {s}.file_versions v WHERE v.id=ANY($1) AND {unreferenced}"),
            &[&candidates],
        )
        .await?;
        tx.commit().await?;
    }
}

async fn prepare_graph(
    tx: &Client,
    target: &Target,
    files: &[SourceFile],
    previous: &BTreeMap<String, Uuid>,
    desired: &BTreeMap<String, Uuid>,
    allow_patch: bool,
) -> Result<(serde_json::Value, serde_json::Value)> {
    let started = std::time::Instant::now();
    let s = schema(target.family);
    let versions: Vec<Uuid> = desired.values().copied().collect();
    // Bump this identity when grammar, parser, or relationship extraction
    // behavior changes. The language is included separately below.
    const ANALYSIS_REVISION: &str =
        "tree-sitter-0.22.6-rust-0.21.2-python-0.21.0-js-0.21.4-typescript-0.21.2-extractor-1";
    let changed_files: BTreeSet<String> = previous
        .keys()
        .chain(desired.keys())
        .filter(|path| previous.get(*path) != desired.get(*path))
        .cloned()
        .collect();
    let mut patchable = allow_patch && !changed_files.is_empty();
    let mut old_snapshot = None;
    let mut affected_names = BTreeSet::new();
    if patchable {
        if let Some(row) = tx
            .query_opt(
                &format!(
                    "SELECT nodes,edges FROM {s}.checkout_structural_snapshots WHERE checkout=$1"
                ),
                &[&target.checkout],
            )
            .await?
        {
            let symbols: Vec<Symbol> = serde_json::from_value(row.get(0))?;
            let edges: Vec<StructuralEdge> = serde_json::from_value(row.get(1))?;
            let ids: std::collections::HashSet<_> =
                symbols.iter().map(|symbol| symbol.chunk_id).collect();
            if edges
                .iter()
                .all(|edge| ids.contains(&edge.from) && ids.contains(&edge.to))
            {
                old_snapshot = Some((symbols, edges));
            } else {
                patchable = false;
            }
        } else {
            patchable = false;
        }
    }
    if patchable {
        for path in &changed_files {
            let (Some(version), Some(lang)) = (previous.get(path), parser::detect_language(path))
            else {
                continue;
            };
            let identity = format!("{ANALYSIS_REVISION}:{lang:?}");
            let row = tx.query_opt(
                &format!("SELECT octet_length(c.source)::bigint,a.symbols FROM {s}.file_content_cache c LEFT JOIN {s}.file_analysis_cache a ON a.file_version=c.file_version AND a.analysis_identity=$2 WHERE c.file_version=$1"),
                &[version, &identity],
            ).await?;
            let Some(row) = row else {
                patchable = false;
                break;
            };
            let size: i64 = row.get(0);
            if size > 1024 * 1024 {
                continue;
            }
            let Some(symbols) = row.get::<_, Option<serde_json::Value>>(1) else {
                patchable = false;
                break;
            };
            for symbol in serde_json::from_value::<Vec<parser::ParsedSymbol>>(symbols)? {
                affected_names.insert(symbol.name);
            }
        }
    }
    let mut cached = HashMap::new();
    for row in tx.query(
        &format!("SELECT file_version,analysis_identity,symbols,candidates FROM {s}.file_analysis_cache WHERE file_version=ANY($1)"),
        &[&versions],
    ).await? {
        cached.insert(
            (row.get::<_, Uuid>(0), row.get::<_, String>(1)),
            (row.get::<_, serde_json::Value>(2), row.get::<_, serde_json::Value>(3)),
        );
    }
    let mut chunks: HashMap<Uuid, Vec<(Uuid, u32)>> = HashMap::new();
    for row in tx
        .query(
            &format!(
                "SELECT file_version,id,start_line FROM {s}.chunks WHERE file_version=ANY($1)"
            ),
            &[&versions],
        )
        .await?
    {
        chunks
            .entry(row.get(0))
            .or_default()
            .push((row.get(1), row.get::<_, i32>(2) as u32));
    }
    let mut nodes = Vec::new();
    let mut parsed = Vec::new();
    let mut pending_analysis = Vec::new();
    let mut names: HashMap<String, Vec<(String, Uuid)>> = HashMap::new();
    let mut ranges: HashMap<(String, u32), Uuid> = HashMap::new();
    for file in files {
        let Some(lang) = parser::detect_language(&file.path) else {
            continue;
        };
        if file.source_size > 1024 * 1024 {
            continue;
        }
        let version = desired[&file.path];
        let identity = format!("{ANALYSIS_REVISION}:{lang:?}");
        let (symbols, candidates): (Vec<parser::ParsedSymbol>, Vec<parser::ParsedEdge>) =
            match cached.remove(&(version, identity.clone())) {
                Some((symbols, candidates)) => (
                    serde_json::from_value(symbols)?,
                    serde_json::from_value(candidates)?,
                ),
                None => {
                    let source = match &file.source {
                        Some(source) => source.clone(),
                        None => tx.query_one(
                            &format!("SELECT source FROM {s}.file_content_cache WHERE file_version=$1"),
                            &[&version],
                        ).await?.get(0),
                    };
                    let symbols = parser::parse_file(&source, lang)?;
                    let candidates = parser::extract_edge_candidates(&symbols, &source, &lang);
                    pending_analysis.push((
                        version,
                        identity,
                        serde_json::to_value(&symbols)?,
                        serde_json::to_value(&candidates)?,
                    ));
                    (symbols, candidates)
                }
            };
        if patchable && changed_files.contains(&file.path) {
            affected_names.extend(symbols.iter().map(|symbol| symbol.name.clone()));
        }
        for &(id, start) in chunks.get(&version).into_iter().flatten() {
            if let Some(sym) = symbols.iter().find(|sym| sym.range.start == start) {
                nodes.push(graph::SymbolNodeInput {
                    chunk_id: id,
                    name: sym.name.clone(),
                    kind: sym.kind.clone(),
                    file_path: target
                        .root
                        .join(&file.path)
                        .to_str()
                        .context("non-UTF8 checkout root")?
                        .to_owned(),
                    start_line: sym.range.start,
                    end_line: sym.range.end,
                });
                names
                    .entry(sym.name.clone())
                    .or_default()
                    .push((file.path.clone(), id));
                ranges.insert((file.path.clone(), start), id);
            }
        }
        parsed.push((file, candidates));
    }
    for batch in pending_analysis.chunks(128) {
        let ids: Vec<Uuid> = batch.iter().map(|(id, _, _, _)| *id).collect();
        let identities: Vec<&str> = batch
            .iter()
            .map(|(_, identity, _, _)| identity.as_str())
            .collect();
        let symbols: Vec<&serde_json::Value> =
            batch.iter().map(|(_, _, symbols, _)| symbols).collect();
        let candidates: Vec<&serde_json::Value> = batch
            .iter()
            .map(|(_, _, _, candidates)| candidates)
            .collect();
        tx.execute(
            &format!("INSERT INTO {s}.file_analysis_cache(file_version,analysis_identity,symbols,candidates)
              SELECT * FROM unnest($1::uuid[],$2::text[],$3::jsonb[],$4::jsonb[]) ON CONFLICT DO NOTHING"),
            &[&ids, &identities, &symbols, &candidates],
        ).await?;
    }
    let known: std::collections::HashSet<String> = names.keys().cloned().collect();
    let mut edges = Vec::new();
    for (file, candidates) in parsed {
        for edge in candidates
            .into_iter()
            .filter(|edge| known.contains(&edge.to_name))
        {
            if patchable
                && !changed_files.contains(&file.path)
                && !affected_names.contains(&edge.to_name)
            {
                continue;
            }
            let Some(from) = ranges.get(&(file.path.clone(), edge.from_range.start)) else {
                continue;
            };
            let Some(candidates) = names.get(&edge.to_name) else {
                continue;
            };
            let local = candidates.iter().any(|(path, _)| path == &file.path);
            for (path, to) in candidates {
                if !local || path == &file.path {
                    edges.push(StructuralEdge {
                        from: *from,
                        to: *to,
                        relation: edge.relation.clone(),
                    });
                }
            }
        }
    }
    let node_count = nodes.len();
    let edge_count = edges.len();
    if patchable {
        let (old_symbols, old_edges) = old_snapshot.context("missing structural snapshot")?;
        let changed_paths: std::collections::HashSet<_> = changed_files
            .iter()
            .map(|path| {
                target
                    .root
                    .join(path)
                    .to_str()
                    .map(str::to_owned)
                    .context("non-UTF8 checkout root")
            })
            .collect::<Result<_>>()?;
        let changed_ids: std::collections::HashSet<_> = old_symbols
            .iter()
            .filter(|symbol| changed_paths.contains(&symbol.file_path))
            .map(|symbol| symbol.chunk_id)
            .collect();
        let affected_ids: std::collections::HashSet<_> = old_symbols
            .iter()
            .filter(|symbol| affected_names.contains(&symbol.name))
            .map(|symbol| symbol.chunk_id)
            .collect();
        edges.extend(old_edges.into_iter().filter(|edge| {
            !changed_ids.contains(&edge.from)
                && !changed_ids.contains(&edge.to)
                && !affected_ids.contains(&edge.to)
        }));
    }
    let symbols: Vec<Symbol> = nodes
        .into_iter()
        .map(|node| Symbol {
            name: node.name,
            kind: node.kind,
            file_path: node.file_path,
            range: LineRange {
                start: node.start_line,
                end: node.end_line,
            },
            chunk_id: node.chunk_id,
        })
        .collect();
    let mut seen = std::collections::HashSet::new();
    edges.retain(|edge| seen.insert((edge.from, edge.to, edge.relation.clone())));
    if started.elapsed().as_secs() >= 5 {
        tracing::info!(
            checkout = %target.root.display(),
            nodes = node_count,
            edges = edge_count,
            prepare_ms = started.elapsed().as_millis() as u64,
            "worktree structural preparation completed"
        );
    }
    Ok((serde_json::to_value(symbols)?, serde_json::to_value(edges)?))
}

/// Read a checkout's structural snapshot. Indexed checkouts created by
/// older binaries keep their AGE graph until their next reconciliation.
pub async fn query_related(
    client: &mut Client,
    target: &Target,
    symbol_name: &str,
    relation: StructuralRelation,
    incoming: bool,
) -> Result<Vec<Symbol>> {
    ensure_checkout_schema(client, target.family).await?;
    loop {
        let guard = crate::maintenance::read(client, target.family).await?;
        let expected = search::visibility_epoch(&guard, target).await?;
        let results =
            query_related_snapshot(&guard, target, symbol_name, relation.clone(), incoming).await?;
        guard.commit().await?;
        if search::visibility_epoch(client, target).await? == expected {
            return Ok(results);
        }
    }
}

async fn query_related_snapshot(
    tx: &Transaction<'_>,
    target: &Target,
    symbol_name: &str,
    relation: StructuralRelation,
    incoming: bool,
) -> Result<Vec<Symbol>> {
    let hidden: BTreeSet<String> = search::hidden_paths(tx, target)
        .await?
        .into_keys()
        .map(|path| target.root.join(path).to_string_lossy().into_owned())
        .collect();
    let client = tx.client();
    let active: bool = client.query_one(&format!("SELECT EXISTS(SELECT 1 FROM {}.checkouts WHERE id=$1 AND registration_state='active' AND indexed_at IS NOT NULL)", schema(target.family)), &[&target.checkout]).await?.get(0);
    ensure!(active, "checkout has no available published view");
    {
        let s = schema(target.family);
        let snapshot_table_exists: bool = client
            .query_one(
                "SELECT to_regclass($1) IS NOT NULL",
                &[&format!("{s}.checkout_structural_snapshots")],
            )
            .await?
            .get(0);
        if snapshot_table_exists {
            let row = client
            .query_opt(
                &format!("SELECT nodes,edges FROM {s}.checkout_structural_snapshots WHERE checkout=$1"),
                &[&target.checkout],
            )
            .await?;
            if let Some(row) = row {
                let nodes: Vec<Symbol> = serde_json::from_value(row.get(0))?;
                let edges: Vec<StructuralEdge> = serde_json::from_value(row.get(1))?;
                let by_id: HashMap<Uuid, Symbol> = nodes
                    .into_iter()
                    .map(|symbol| (symbol.chunk_id, symbol))
                    .collect();
                return Ok(edges
                    .into_iter()
                    .filter(|edge| edge.relation == relation)
                    .filter_map(|edge| {
                        let (origin, related) = if incoming {
                            (edge.to, edge.from)
                        } else {
                            (edge.from, edge.to)
                        };
                        let origin = by_id.get(&origin)?;
                        let related = by_id.get(&related)?;
                        (origin.name == symbol_name
                            && !hidden.contains(&origin.file_path)
                            && !hidden.contains(&related.file_path))
                        .then(|| related.clone())
                    })
                    .collect());
            }
        }
    }
    graph::query_related_unlocked(
        client,
        target.graph,
        symbol_name,
        relation,
        incoming,
        &hidden,
    )
    .await
}
