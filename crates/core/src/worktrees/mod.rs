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
            ensure!(row.get::<_,bool>(1), "worktree has no completed index yet: {}",root.display());
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
/// only those absent from a successfully read Git registry. Missing directories
/// which Git still lists retain their last index. No Git operation is performed.
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
    let mut available = Vec::new();
    for entry in &entries {
        // Git keeps unavailable/locked/prunable entries. Never retire them just
        // because canonicalization or discovery is currently impossible.
        listed.push(entry.path.clone());
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
    // absent; an unavailable entry still listed by Git must retain its index.
    for row in tx
        .query(
            &format!(
                "SELECT id,root,git_dir FROM {s}.checkouts WHERE registration_state<>'retired'"
            ),
            &[],
        )
        .await?
    {
        let id: Uuid = row.get(0);
        let bytes: Vec<u8> = row.get(1);
        let admin: Option<Vec<u8>> = row.get(2);
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
        if !identity_present && (!listed.contains(&path) || replaced) {
            graph::drop_graph(tx.client(), id).await?;
            tx.execute(
                &format!("DELETE FROM {s}.file_deltas WHERE checkout=$1"),
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
    garbage_collect(&tx, &s).await?;
    tx.commit().await?;
    let mut skips = Vec::new();
    let mut completed = 0;
    let mut attempted = 0;
    for (initialized, target, git) in targets {
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

struct SourceFile {
    path: String,
    source: String,
    hash: Vec<u8>,
    tier: Tier,
}

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
            source,
            tier,
        });
    }
    files.sort_by(|a, b| a.path.cmp(&b.path));
    Ok(files)
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
) -> Result<()> {
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
    let files = scan(&target.root, &selection)?;
    let previous = if initialized {
        manifest(&tx, &s, target.checkout).await?
    } else {
        BTreeMap::new()
    };
    let mut desired = BTreeMap::new();
    for (n, file) in files.iter().enumerate() {
        let version=if let Some(row)=tx.query_opt(&format!("SELECT id FROM {s}.file_versions WHERE path=$1 AND content_hash=$2 AND tier=$3"),&[&file.path,&file.hash,&file.tier.as_i16()]).await? {
            row.get(0)
        } else {
            let version=Uuid::new_v4();
            let paths = vec![file.path.clone(), target.root.join(&file.path).to_string_lossy().into_owned()];
            // Read reusable vectors once per file, rather than scanning its
            // stored chunks once for every candidate chunk.
            let rows = tx.query(&format!("SELECT content,embedding FROM {s}.chunks WHERE file_path=ANY($1) AND embedding IS NOT NULL"), &[&paths]).await
                .with_context(|| format!("load reusable embeddings for {}", file.path))?;
            let vectors = rows.into_iter().map(|row| (row.get::<_, String>(0), row.get::<_, pgvector::Vector>(1).to_vec())).collect();
            let reuse = ReuseEmbeddings { vectors, backend: embedder };
            let (chunks,_) = tokio::time::timeout(std::time::Duration::from_secs(120),pipeline::prepare_chunks(target.family,file.path.clone(),file.source.clone(),&reuse,1500,batch_size,dimension,file.tier)).await
                .with_context(|| format!("prepare {} exceeded 120 seconds", file.path))?
                .with_context(|| format!("prepare {}", file.path))?;
            tx.execute(&format!("INSERT INTO {s}.file_versions(id,path,content_hash,tier) VALUES($1,$2,$3,$4)"),&[&version,&file.path,&file.hash,&file.tier.as_i16()]).await?;
            for chunk in chunks {
                let vector=chunk.embedding.map(pgvector::Vector::from);
                tx.execute(&format!("INSERT INTO {s}.chunks(id,repo_id,file_path,start_line,end_line,content,embedding,tier,embedding_state,content_hash,file_version,in_base) VALUES($1,$2,$3,$4,$5,$6,$7,$8,$9,$10,$11,false)"),
                    &[&chunk.id,&target.family,&file.path,&(chunk.range.start as i32),&(chunk.range.end as i32),&chunk.content,&vector,&chunk.tier.as_i16(),&chunk.embedding_state.as_str(),&chunk.content_hash,&version]).await?;
            }
            version
        };
        desired.insert(file.path.clone(), version);
        progress(n + 1, files.len(), &target.root.join(&file.path));
    }
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
        rebuild_graph(&tx, target, &files, &desired)
            .await
            .context("replace checkout AGE graph")?;
    }
    // Re-read the selection and hashes before committing. A read/scan failure or
    // Git blocker rolls back chunks, deltas and graph together.
    let after = scan(&target.root, &selection)?;
    ensure!(
        files.len() == after.len()
            && files
                .iter()
                .zip(&after)
                .all(|(a, b)| a.path == b.path && a.hash == b.hash && a.tier == b.tier),
        "files changed during indexing; retaining previous index"
    );
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
    desired: &BTreeMap<String, Uuid>,
) -> Result<()> {
    let s = schema(target.family);
    let mut nodes = Vec::new();
    let mut parsed = Vec::new();
    let mut names: HashMap<String, Vec<(String, Uuid)>> = HashMap::new();
    let mut ranges: HashMap<(String, u32), Uuid> = HashMap::new();
    for file in files {
        let Some(lang) = parser::detect_language(&file.path) else {
            continue;
        };
        if file.source.len() > 1024 * 1024 {
            continue;
        }
        let symbols = parser::parse_file(&file.source, lang)?;
        let version = desired[&file.path];
        for row in tx
            .query(
                &format!("SELECT id,start_line FROM {s}.chunks WHERE file_version=$1"),
                &[&version],
            )
            .await?
        {
            let id: Uuid = row.get(0);
            let start = row.get::<_, i32>(1) as u32;
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
        parsed.push((file, lang, symbols));
    }
    let known = names.keys().cloned().collect();
    let mut edges = Vec::new();
    for (file, lang, symbols) in parsed {
        for edge in parser::extract_edges(&symbols, &file.source, &lang, &known) {
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
    store::ensure_graph(tx.client(), target.graph).await?;
    graph::replace_graph(tx.client(), target.graph, &nodes, &edges).await
}
