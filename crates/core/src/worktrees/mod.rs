//! A moving base and ordinary file-level deltas. All publications for a family
//! use the same transaction-owned advisory lock; readers see committed views.
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
    for repo in store::list_repos(client).await? {
        let s = schema(repo.id);
        let exists: bool = client
            .query_one(
                "SELECT to_regclass($1) IS NOT NULL",
                &[&format!("{}.worktree_base", s)],
            )
            .await?
            .get(0);
        if !exists {
            continue;
        }
        if let Some(row) = client.query_opt(&format!(
            "SELECT c.id,c.indexed_at IS NOT NULL,b.checkout=c.id AS is_base FROM {s}.checkouts c CROSS JOIN {s}.worktree_base b WHERE c.root=$1 AND c.registration_state='active'"), &[&stored.bytes()]).await? {
            if !row.get::<_,bool>(1) && row.get::<_,bool>(2) && repo.ever_indexed {
                // An interrupted first conversion must still serve the existing
                // primary index through the legacy search path.
                return Ok(None);
            }
            if !row.get::<_, bool>(1) {
                return Err(PendingIndex(root).into());
            }
            let id: Uuid = row.get(0);
            return Ok(Some(Target { family:repo.id, checkout:id, graph:if row.get(2) {repo.id} else {id},root }));
        }
    }
    Ok(None)
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
    crate::db::run_repo_migrations(client, &store::repo_schema(family)).await?;
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
    embedder: Arc<dyn EmbeddingBackend>,
    batch_size: usize,
    dimension: usize,
    exclude: &[String],
    vendor: &[String],
    progress: impl Fn(usize, usize, &Path),
    changed: Option<&[PathBuf]>,
    requested: Option<&Path>,
) -> Result<(BatchOutcome, Vec<SkipRecord>)> {
    if let Some(view) = crate::family_policy::runtime::policy(client, family).await? {
        ensure!(
            view.indexing_enabled && !view.paused,
            "family indexing is not enabled or is paused"
        );
    }
    let (primary, entries) = discovery(root).await?;
    let s = schema(family);
    let tx = client.transaction().await?;
    lock(&tx, family).await?;
    let mut targets = Vec::new();
    let mut listed = Vec::new();
    let mut missing_listed = Vec::new();
    let mut available = Vec::new();
    for entry in &entries {
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
                    &format!("DELETE FROM {s}.file_deltas WHERE checkout=$1"),
                    &[&id],
                )
                .await?;
            }
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
    garbage_collect(&tx, &s).await?;
    tx.commit().await?;
    let mut skips = Vec::new();
    let mut completed = 0;
    let mut attempted = 0;
    for (initialized, target, git) in targets {
        if requested.is_some_and(|path| path != target.root) {
            continue;
        }
        if initialized
            && changed.is_some_and(|paths| {
                !paths
                    .iter()
                    .any(|p| p.starts_with(&target.root) || p.starts_with(&git.git_dir))
            })
        {
            continue;
        }
        attempted += 1;
        match reconcile_checkout(
            client,
            &target,
            &git,
            embedder.as_ref(),
            batch_size,
            dimension,
            exclude,
            vendor,
            &progress,
            !initialized,
            changed,
        )
        .await
        {
            Ok(()) => completed += 1,
            Err(e) => skips.push(SkipRecord {
                path: target.root,
                reason: format!("{e:#}"),
            }),
        }
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

// Reuse vectors already stored by the original indexer during the first
// worktree-aware reconciliation. Content is compared exactly; paths constrain
// the lookup to the file rather than scanning the whole repository per chunk.
struct ReuseEmbeddings<'a> {
    vectors: std::collections::HashMap<String, Vec<f32>>,
    backend: &'a dyn EmbeddingBackend,
}
impl EmbeddingBackend for ReuseEmbeddings<'_> {
    fn embed<'a>(&'a self, texts: &'a [String]) -> crate::embeddings::EmbedFuture<'a> {
        Box::pin(async move {
            let mut vectors = vec![Vec::new(); texts.len()];
            let mut missing = Vec::new();
            let mut positions = Vec::new();
            for (i, text) in texts.iter().enumerate() {
                if let Some(vector) = self.vectors.get(text) {
                    vectors[i] = vector.clone();
                } else {
                    missing.push(text.clone());
                    positions.push(i);
                }
            }
            if !missing.is_empty() {
                let new = self.backend.embed(&missing).await?;
                ensure!(
                    new.len() == missing.len(),
                    "embedding backend returned wrong result count"
                );
                for (i, v) in positions.into_iter().zip(new) {
                    vectors[i] = v;
                }
            }
            Ok(vectors)
        })
    }
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

type VersionCandidates = HashMap<(String, Vec<u8>, i16), Vec<(Uuid, Option<String>)>>;

fn scan(
    root: &Path,
    selection: &crate::family_policy::runtime::Selection,
) -> Result<Vec<SourceFile>> {
    let walker = selection.walker(root);
    let mut files = Vec::new();
    for entry in walker {
        let entry = entry?;
        if !entry.file_type().is_some_and(|t| t.is_file()) {
            continue;
        }
        let path = entry.path();
        if entry.metadata()?.len() > 10 * 1024 * 1024 {
            continue;
        }
        let bytes = std::fs::read(path)?;
        if bytes.contains(&0) {
            continue;
        }
        let Ok(source) = String::from_utf8(bytes) else {
            continue;
        };
        let rel = path.strip_prefix(root)?;
        let relative = rel
            .to_str()
            .context("indexed file path is not UTF-8")?
            .to_owned();
        let tier = if selection.classify(rel, false) == pipeline::Decision::Tier2 {
            Tier::Tier2
        } else {
            Tier::Tier1
        };
        files.push(SourceFile {
            path: relative,
            hash: content_sha256(&source),
            source_size: source.len(),
            source: Some(source),
            tier,
        });
    }
    files.sort_by(|a, b| a.path.cmp(&b.path));
    Ok(files)
}

// Directory or Git-administration events can affect paths not named in the
// event. Those cases use the full-audit path instead of guessing descendants.
fn changed_paths(
    target: &Target,
    git: &GitCheckout,
    events: Option<&[PathBuf]>,
    previous: &BTreeMap<String, Uuid>,
) -> Option<Vec<PathBuf>> {
    let mut paths = BTreeSet::new();
    for event in events? {
        if event.starts_with(&git.git_dir) {
            return None;
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
    let bytes = std::fs::read(&path)?;
    if bytes.contains(&0) {
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

async fn manifest(tx: &Transaction<'_>, s: &str, checkout: Uuid) -> Result<BTreeMap<String, Uuid>> {
    let rows=tx.query(&format!("SELECT b.path,b.version FROM {s}.base_files b WHERE NOT EXISTS(SELECT 1 FROM {s}.file_deltas d WHERE d.checkout=$1 AND d.path=b.path) UNION ALL SELECT path,version FROM {s}.file_deltas WHERE checkout=$1 AND version IS NOT NULL"),&[&checkout]).await?;
    Ok(rows.into_iter().map(|r| (r.get(0), r.get(1))).collect())
}

#[allow(clippy::too_many_arguments)]
async fn reconcile_checkout(
    client: &mut Client,
    target: &Target,
    git: &GitCheckout,
    embedder: &dyn EmbeddingBackend,
    batch_size: usize,
    dimension: usize,
    exclude: &[String],
    vendor: &[String],
    progress: &impl Fn(usize, usize, &Path),
    refresh_graph: bool,
    events: Option<&[PathBuf]>,
) -> Result<()> {
    let started = std::time::Instant::now();
    let stamp = git_stamp(git).await?;
    let s = schema(target.family);
    let tx = client.transaction().await?;
    tx.batch_execute("SET LOCAL statement_timeout='60s'")
        .await?;
    lock(&tx, target.family).await?;
    let family = tx
        .query_opt(
            "SELECT paused FROM public.repos WHERE id=$1",
            &[&target.family],
        )
        .await?
        .context("family removed")?;
    ensure!(!family.get::<_, bool>(0), "family is paused");
    let row=tx.query_one(&format!("SELECT registration_state,paused,indexed_at IS NOT NULL FROM {s}.checkouts WHERE id=$1"),&[&target.checkout]).await?;
    ensure!(
        row.get::<_, String>(0) == "active" && !row.get::<_, bool>(1),
        "checkout is inactive or paused"
    );
    let initialized: bool = row.get(2);
    if target.graph != target.family {
        let base_ready:bool=tx.query_one(&format!("SELECT c.indexed_at IS NOT NULL FROM {s}.worktree_base b JOIN {s}.checkouts c ON c.id=b.checkout"),&[]).await?.get(0);
        ensure!(
            base_ready,
            "primary checkout has no completed base yet; retaining pending worktree"
        );
    }

    let policy = crate::family_policy::runtime::lock_policy(&tx, target.family).await?;
    let selection = crate::family_policy::runtime::Selection::new(
        &target.root,
        policy.as_ref(),
        exclude,
        vendor,
    )?;
    let batch_size = policy
        .as_ref()
        .map_or(batch_size, |p| p.policy.embeddings.batch_size as usize);
    let previous = if initialized {
        manifest(&tx, &s, target.checkout).await?
    } else {
        BTreeMap::new()
    };
    let candidates = if initialized {
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
    let files = if let Some(paths) = candidates.filter(|_| inherited.len() == previous.len()) {
        let mut observed = Vec::with_capacity(paths.len());
        for path in paths {
            let key = path
                .to_str()
                .context("indexed file path is not UTF-8")?
                .to_owned();
            let file = scan_changed_file(&target.root, &selection, &path)?;
            inherited.remove(&key);
            if let Some(value) = &file {
                inherited.insert(key, value.clone());
            }
            observed.push((path, file));
        }
        fast_changes = Some(observed);
        inherited.into_values().collect()
    } else {
        scan(&target.root, &selection)?
    };
    let scanned = started.elapsed();
    let mut desired = BTreeMap::new();
    let paths: Vec<_> = files
        .iter()
        .filter(|file| file.source.is_some())
        .map(|file| file.path.clone())
        .collect();
    let mut versions = VersionCandidates::new();
    for row in tx
        .query(
            &format!("SELECT v.id,v.path,v.content_hash,v.tier,c.source FROM {s}.file_versions v LEFT JOIN {s}.file_content_cache c ON c.file_version=v.id WHERE v.path=ANY($1)"),
            &[&paths],
        )
        .await? {
        versions.entry((row.get(1), row.get(2), row.get(3))).or_default().push((row.get(0), row.get(4)));
    }
    let mut pending_sources = Vec::new();
    for (n, file) in files.iter().enumerate() {
        let Some(source) = &file.source else {
            desired.insert(
                file.path.clone(),
                *previous
                    .get(&file.path)
                    .context("missing inherited file version")?,
            );
            continue;
        };
        let version = if let Some((version, _)) = versions
            .get(&(file.path.clone(), file.hash.clone(), file.tier.as_i16()))
            .and_then(|candidates| {
                candidates
                    .iter()
                    .find(|(_, cached)| cached.as_deref() == Some(source.as_str()))
            }) {
            *version
        } else {
            let version = Uuid::new_v4();
            let paths = vec![
                file.path.clone(),
                target.root.join(&file.path).to_string_lossy().into_owned(),
            ];
            // Read reusable vectors once per file, rather than scanning its
            // stored chunks once for every candidate chunk.
            let rows = tx.query(&format!("SELECT content,embedding FROM {s}.chunks WHERE file_path=ANY($1) AND embedding IS NOT NULL"), &[&paths]).await
                .with_context(|| format!("load reusable embeddings for {}", file.path))?;
            let vectors = rows
                .into_iter()
                .map(|row| {
                    (
                        row.get::<_, String>(0),
                        row.get::<_, pgvector::Vector>(1).to_vec(),
                    )
                })
                .collect();
            let reuse = ReuseEmbeddings {
                vectors,
                backend: embedder,
            };
            let (chunks, _) = tokio::time::timeout(
                std::time::Duration::from_secs(120),
                pipeline::prepare_chunks(
                    target.family,
                    file.path.clone(),
                    source.clone(),
                    &reuse,
                    1500,
                    batch_size,
                    dimension,
                    file.tier,
                ),
            )
            .await
            .with_context(|| format!("prepare {} exceeded 120 seconds", file.path))?
            .with_context(|| format!("prepare {}", file.path))?;
            tx.execute(
                &format!(
                    "INSERT INTO {s}.file_versions(id,path,content_hash,tier) VALUES($1,$2,$3,$4)"
                ),
                &[&version, &file.path, &file.hash, &file.tier.as_i16()],
            )
            .await?;
            pending_sources.push((version, source.as_str()));
            for chunk in chunks {
                let vector = chunk.embedding.map(pgvector::Vector::from);
                tx.execute(&format!("INSERT INTO {s}.chunks(id,repo_id,file_path,start_line,end_line,content,embedding,tier,embedding_state,content_hash,file_version,in_base) VALUES($1,$2,$3,$4,$5,$6,$7,$8,$9,$10,$11,false)"),
                    &[&chunk.id,&target.family,&file.path,&(chunk.range.start as i32),&(chunk.range.end as i32),&chunk.content,&vector,&chunk.tier.as_i16(),&chunk.embedding_state.as_str(),&chunk.content_hash,&version]).await?;
            }
            version
        };
        desired.insert(file.path.clone(), version);
        progress(n + 1, files.len(), &target.root.join(&file.path));
    }
    for batch in pending_sources.chunks(128) {
        let ids: Vec<Uuid> = batch.iter().map(|(id, _)| *id).collect();
        let sources: Vec<&str> = batch.iter().map(|(_, source)| *source).collect();
        tx.execute(
            &format!("INSERT INTO {s}.file_content_cache(file_version,source) SELECT * FROM unnest($1::uuid[],$2::text[])"),
            &[&ids, &sources],
        ).await?;
    }
    let versioned = started.elapsed();
    if refresh_graph || !initialized || previous != desired {
        if target.graph == target.family {
            publish_base(&tx, &s, target.checkout, &desired).await?;
            // Legacy rows have no reliable file-version identity. They remain
            // visible until this first complete base publication commits.
            tx.execute(
                &format!("DELETE FROM {s}.chunks WHERE file_version IS NULL"),
                &[],
            )
            .await?;
        } else {
            tx.execute(
                &format!("DELETE FROM {s}.file_deltas WHERE checkout=$1"),
                &[&target.checkout],
            )
            .await?;
            let base: BTreeMap<String, Uuid> = tx
                .query(&format!("SELECT path,version FROM {s}.base_files"), &[])
                .await?
                .into_iter()
                .map(|r| (r.get(0), r.get(1)))
                .collect();
            for path in base.keys().chain(desired.keys()).collect::<BTreeSet<_>>() {
                if base.get(path) != desired.get(path) {
                    tx.execute(
                        &format!(
                            "INSERT INTO {s}.file_deltas(checkout,path,version) VALUES($1,$2,$3)"
                        ),
                        &[&target.checkout, path, &desired.get(path)],
                    )
                    .await?;
                }
            }
        }
        rebuild_graph(
            &tx,
            target,
            &files,
            &previous,
            &desired,
            fast_changes.is_some() && !refresh_graph,
        )
        .await
        .context("publish checkout structural index")?;
    }
    let graphed = started.elapsed();
    // Re-read the selection and hashes before committing. A read/scan failure or
    // Git blocker rolls back chunks, deltas and graph together.
    if let Some(changes) = &fast_changes {
        for (path, before) in changes {
            let after = scan_changed_file(&target.root, &selection, path)?;
            ensure!(
                match (before, &after) {
                    (None, None) => true,
                    (Some(a), Some(b)) => a.source == b.source && a.tier == b.tier,
                    _ => false,
                },
                "files changed during indexing; retaining previous index"
            );
        }
    } else {
        let after = scan(&target.root, &selection)?;
        ensure!(
            files.len() == after.len()
                && files
                    .iter()
                    .zip(&after)
                    .all(|(a, b)| a.path == b.path && a.source == b.source && a.tier == b.tier),
            "files changed during indexing; retaining previous index"
        );
    }
    ensure!(
        git_stamp(git).await? == stamp,
        "Git HEAD changed during indexing; retaining previous index"
    );
    tx.execute(&format!("UPDATE {s}.checkouts SET indexed_at=now(),availability='available',git_state='clear',merge_in_progress=false,rebase_merge_in_progress=false,rebase_apply_in_progress=false,unmerged_index=false,observed_at=now(),last_seen_at=now() WHERE id=$1"),&[&target.checkout]).await?;
    if target.graph == target.family {
        store::mark_indexed(tx.client(), target.family).await?;
    }
    garbage_collect(&tx, &s).await?;
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
    Ok(())
}

async fn publish_base(
    tx: &Transaction<'_>,
    s: &str,
    base: Uuid,
    desired: &BTreeMap<String, Uuid>,
) -> Result<()> {
    let previous: BTreeMap<String, Uuid> = tx
        .query(&format!("SELECT path,version FROM {s}.base_files"), &[])
        .await?
        .into_iter()
        .map(|r| (r.get(0), r.get(1)))
        .collect();
    for path in previous
        .keys()
        .chain(desired.keys())
        .collect::<BTreeSet<_>>()
    {
        let old = previous.get(path);
        let new = desired.get(path);
        if old == new {
            continue;
        }
        // Preserve inherited old values before replacing the base. Existing
        // explicit overrides win, including NULL tombstones.
        tx.execute(&format!("INSERT INTO {s}.file_deltas(checkout,path,version) SELECT id,$1,$2 FROM {s}.checkouts WHERE id<>$3 AND indexed_at IS NOT NULL AND registration_state<>'retired' ON CONFLICT(checkout,path) DO NOTHING"),&[path,&old,&base]).await?;
        tx.execute(
            &format!(
                "DELETE FROM {s}.file_deltas WHERE path=$1 AND version IS NOT DISTINCT FROM $2"
            ),
            &[path, &new],
        )
        .await?;
        if let Some(old) = old {
            tx.execute(
                &format!("UPDATE {s}.chunks SET in_base=false WHERE file_version=$1"),
                &[old],
            )
            .await?;
        }
        match new {
            Some(version) => {
                tx.execute(&format!("INSERT INTO {s}.base_files(path,version) VALUES($1,$2) ON CONFLICT(path) DO UPDATE SET version=EXCLUDED.version"),&[path,version]).await?;
                tx.execute(
                    &format!("UPDATE {s}.chunks SET in_base=true WHERE file_version=$1"),
                    &[version],
                )
                .await?;
            }
            None => {
                tx.execute(
                    &format!("DELETE FROM {s}.base_files WHERE path=$1"),
                    &[path],
                )
                .await?;
            }
        }
    }
    Ok(())
}

async fn garbage_collect(tx: &Transaction<'_>, s: &str) -> Result<()> {
    tx.execute(&format!("DELETE FROM {s}.file_versions v WHERE NOT EXISTS(SELECT 1 FROM {s}.base_files b WHERE b.version=v.id) AND NOT EXISTS(SELECT 1 FROM {s}.file_deltas d WHERE d.version=v.id)"),&[]).await?;
    Ok(())
}

async fn rebuild_graph(
    tx: &Transaction<'_>,
    target: &Target,
    files: &[SourceFile],
    previous: &BTreeMap<String, Uuid>,
    desired: &BTreeMap<String, Uuid>,
    allow_patch: bool,
) -> Result<()> {
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
    if patchable && target.graph == target.family {
        patchable = tx
            .query_one(
                "SELECT EXISTS(SELECT 1 FROM ag_catalog.ag_graph WHERE name=$1)",
                &[&store::graph_name(target.graph)],
            )
            .await?
            .get(0);
    } else if patchable {
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
            &format!("INSERT INTO {s}.file_analysis_cache(file_version,analysis_identity,symbols,candidates) SELECT * FROM unnest($1::uuid[],$2::text[],$3::jsonb[],$4::jsonb[])"),
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
    let prepared = started.elapsed();
    let node_count = nodes.len();
    let edge_count = edges.len();
    if target.graph == target.family {
        // The primary checkout and legacy graph readers retain their existing
        // AGE representation. Linked checkouts use a single transactional row.
        store::ensure_graph(tx.client(), target.graph).await?;
        if patchable {
            let changed_paths: Vec<String> = changed_files
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
            let changed_nodes: Vec<_> = nodes
                .iter()
                .filter(|node| changed_paths.contains(&node.file_path))
                .collect();
            graph::patch_graph(
                tx.client(),
                target.graph,
                &changed_paths,
                &affected_names.into_iter().collect::<Vec<_>>(),
                &nodes,
                &changed_nodes,
                &edges,
            )
            .await?;
        } else {
            graph::replace_graph(tx.client(), target.graph, &nodes, &edges).await?;
        }
    } else {
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
        let node_json = serde_json::to_value(symbols)?;
        let edge_json = serde_json::to_value(edges)?;
        tx.execute(
            &format!("INSERT INTO {s}.checkout_structural_snapshots(checkout,nodes,edges) VALUES($1,$2,$3) ON CONFLICT(checkout) DO UPDATE SET nodes=EXCLUDED.nodes,edges=EXCLUDED.edges"),
            &[&target.checkout, &node_json, &edge_json],
        )
        .await?;
    }
    if started.elapsed().as_secs() >= 5 {
        tracing::info!(
            checkout = %target.root.display(),
            nodes = node_count,
            edges = edge_count,
            prepare_ms = prepared.as_millis() as u64,
            write_ms = (started.elapsed() - prepared).as_millis() as u64,
            "worktree structural publication completed"
        );
    }
    Ok(())
}

/// Read a linked checkout's structural snapshot. Indexed checkouts created by
/// older binaries keep their AGE graph until their next reconciliation.
pub async fn query_related(
    client: &Client,
    target: &Target,
    symbol_name: &str,
    relation: StructuralRelation,
    incoming: bool,
) -> Result<Vec<Symbol>> {
    if target.graph != target.family {
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
                        if by_id.get(&origin)?.name == symbol_name {
                            by_id.get(&related).cloned()
                        } else {
                            None
                        }
                    })
                    .collect());
            }
        }
    }
    graph::query_related(client, target.graph, symbol_name, relation, incoming).await
}
