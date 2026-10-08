use anyhow::{bail, ensure, Context};
use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::{Output, Stdio};
use tokio::process::Command;

mod git_state;
pub use git_state::{inspect_git_operation_state, GitOperationState};

/// Filesystem identity discovered by Git, before looking up a registered family.
/// Linked worktrees have distinct roots and the same canonical common directory.
/// These paths do not assign database IDs or select an indexed snapshot.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GitCheckout {
    pub root: PathBuf,
    pub common_dir: PathBuf,
    /// Per-checkout administrative directory; distinct for linked worktrees.
    pub git_dir: PathBuf,
}

/// One entry reported by Git, including unavailable and bare worktrees.
/// Paths are absolute but not canonicalized: a missing checkout must remain
/// visible. Validate an available checkout with `discover_git_checkout` before
/// watching it. HEAD and branch are observations, not snapshot identities.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct GitWorktree {
    pub path: PathBuf,
    pub head: Option<String>,
    pub branch: Option<OsString>,
    pub detached: bool,
    pub bare: bool,
    /// Some(empty) means locked without a reason; None means unlocked.
    pub locked: Option<OsString>,
    /// Git's advisory pruning status, never an instruction to remove data.
    pub prunable: Option<OsString>,
}

/// Enumerate a family's worktrees from its Git common directory. This neither
/// prunes Git metadata nor registers, starts, or removes any Muninn watchers.
/// Errors fail the scan instead of returning an apparently empty family.
pub async fn list_git_worktrees(common_dir: &Path) -> anyhow::Result<Vec<GitWorktree>> {
    let output = git_output(common_dir, &["worktree", "list", "--porcelain", "-z"]).await?;
    check_git_output(&output, common_dir)?;
    parse_git_worktrees(&output.stdout)
}

fn parse_git_worktrees(bytes: &[u8]) -> anyhow::Result<Vec<GitWorktree>> {
    let bytes = bytes
        .strip_suffix(b"\0")
        .context("unterminated Git worktree list")?;
    let mut entries = Vec::new();
    let mut current: Option<GitWorktree> = None;
    let mut seen = std::collections::HashSet::new();
    for field in bytes.split(|b| *b == 0) {
        if field.is_empty() {
            entries.push(current.take().context("empty Git worktree record")?);
            seen.clear();
            continue;
        }
        let mut parts = field.splitn(2, |b| *b == b' ');
        let name = parts.next().unwrap();
        let value = parts.next();
        if name == b"worktree" {
            ensure!(current.is_none(), "unterminated Git worktree record");
            let path = PathBuf::from(git_os_string(value.context("missing worktree path")?)?);
            ensure!(
                path.is_absolute(),
                "Git returned a non-absolute worktree path"
            );
            current = Some(GitWorktree {
                path,
                ..GitWorktree::default()
            });
            continue;
        }
        let entry = current
            .as_mut()
            .context("Git attribute before worktree path")?;
        ensure!(seen.insert(name), "duplicate Git worktree attribute");
        match name {
            b"HEAD" => {
                entry.head = Some(std::str::from_utf8(value.context("missing HEAD")?)?.to_owned())
            }
            b"branch" => entry.branch = Some(git_os_string(value.context("missing branch")?)?),
            b"detached" | b"bare" => {
                ensure!(value.is_none(), "unexpected Git worktree flag value");
                if name == b"detached" {
                    entry.detached = true;
                } else {
                    entry.bare = true;
                }
            }
            b"locked" => entry.locked = Some(git_os_string(value.unwrap_or_default())?),
            b"prunable" => entry.prunable = Some(git_os_string(value.unwrap_or_default())?),
            // Porcelain may gain attributes in future Git versions.
            _ => {}
        }
    }
    ensure!(current.is_none(), "unterminated Git worktree record");
    ensure!(!entries.is_empty(), "empty Git worktree list");
    Ok(entries)
}

/// Discover a checkout from an existing directory, including a nested directory.
/// Returns None outside a working tree (including bare repositories and Git's
/// internal directory). Missing paths, invalid repositories and Git errors fail.
/// No configuration marker, branch name or commit is required.
pub async fn discover_git_checkout(directory: &Path) -> anyhow::Result<Option<GitCheckout>> {
    let directory = tokio::fs::canonicalize(directory)
        .await
        .with_context(|| format!("resolve directory {}", directory.display()))?;
    ensure!(
        directory.is_dir(),
        "not a directory: {}",
        directory.display()
    );

    let inside = git_rev_parse(&directory, &["--is-inside-work-tree"]).await?;
    if !inside.status.success() {
        // Git has no distinct exit status for this case. Use only its specific
        // discovery diagnostics in the C locale; other failures must propagate.
        if inside
            .stderr
            .starts_with(b"fatal: not a git repository (or any of the parent directories): ")
            || inside
                .stderr
                .starts_with(b"fatal: not a git repository (or any parent up to mount point ")
        {
            return Ok(None);
        }
        check_git_output(&inside, &directory)?;
    }
    match inside.stdout.as_slice() {
        b"false\n" => return Ok(None),
        b"true\n" => {}
        _ => bail!(
            "unexpected Git working-tree response for {}",
            directory.display()
        ),
    }

    // Query separately: path names may themselves contain newlines.
    let root = git_path(&directory, "--show-toplevel").await?;
    let common_dir = git_path(&directory, "--git-common-dir").await?;
    let git_dir = git_path(&directory, "--absolute-git-dir").await?;
    Ok(Some(GitCheckout {
        root,
        common_dir,
        git_dir,
    }))
}

fn git_command(directory: &Path) -> Command {
    let mut command = Command::new("git");
    command
        .current_dir(directory)
        .stdin(Stdio::null())
        .kill_on_drop(true);
    command.env("LC_ALL", "C").env("GIT_OPTIONAL_LOCKS", "0");
    // Discovery is about the supplied directory, even when invoked from a hook
    // or a shell carrying another repository's Git environment.
    for name in [
        "GIT_DIR",
        "GIT_WORK_TREE",
        "GIT_COMMON_DIR",
        "GIT_INDEX_FILE",
        "GIT_OBJECT_DIRECTORY",
        "GIT_ALTERNATE_OBJECT_DIRECTORIES",
        "GIT_PREFIX",
        "GIT_CEILING_DIRECTORIES",
    ] {
        command.env_remove(name);
    }
    command
}

async fn git_rev_parse(directory: &Path, args: &[&str]) -> anyhow::Result<Output> {
    let mut command_args = vec!["rev-parse"];
    command_args.extend_from_slice(args);
    git_output(directory, &command_args).await
}

async fn git_output(directory: &Path, args: &[&str]) -> anyhow::Result<Output> {
    tokio::time::timeout(
        std::time::Duration::from_secs(10),
        git_command(directory).args(args).output(),
    )
    .await
    .with_context(|| format!("Git discovery timed out for {}", directory.display()))?
    .with_context(|| format!("run Git discovery for {}", directory.display()))
}

fn check_git_output(output: &Output, directory: &Path) -> anyhow::Result<()> {
    ensure!(
        output.status.success(),
        "Git discovery failed for {}: {}",
        directory.display(),
        String::from_utf8_lossy(&output.stderr).trim_end()
    );
    Ok(())
}

async fn git_path(directory: &Path, option: &str) -> anyhow::Result<PathBuf> {
    let output = git_rev_parse(directory, &["--path-format=absolute", option]).await?;
    check_git_output(&output, directory)?;
    let path = parse_git_path(&output.stdout)?;
    tokio::fs::canonicalize(&path)
        .await
        .with_context(|| format!("resolve Git path {}", path.display()))
}

// Administrative paths may not exist outside an operation, so parsing and
// canonicalization are separate. Preserve newlines and native path bytes.
fn parse_git_path(bytes: &[u8]) -> anyhow::Result<PathBuf> {
    // Strip exactly Git's terminator, preserving whitespace in the path itself.
    let bytes = bytes.strip_suffix(b"\n").context("unterminated Git path")?;
    let path = PathBuf::from(git_os_string(bytes)?);
    ensure!(path.is_absolute(), "Git returned a non-absolute path");
    Ok(path)
}

fn git_os_string(bytes: &[u8]) -> anyhow::Result<OsString> {
    #[cfg(unix)]
    {
        use std::os::unix::ffi::OsStringExt;
        Ok(OsString::from_vec(bytes.to_vec()))
    }
    #[cfg(not(unix))]
    {
        Ok(OsString::from(std::str::from_utf8(bytes)?))
    }
}

/// Resolve a user-supplied path string into a clean absolute PathBuf.
///
/// Handles:
/// - Leading `~` → expanded to `$HOME` (shell does not expand `~` inside
///   quoted strings or config files).
/// - Relative paths → made absolute against the current working directory.
/// - Symlinks and `.`/`..` components → resolved via `canonicalize` when the
///   path exists.
///
/// For paths that do not exist on disk (e.g. `unregister` after the directory
/// was already deleted), canonicalize is skipped and the path is returned as
/// an absolute path without symlink resolution.
pub fn resolve_path(raw: &str) -> anyhow::Result<PathBuf> {
    // Expand leading ~ (only `~` alone or `~/…` — `~user` is intentionally
    // not supported; the shell handles that before argv reaches us).
    let expanded = if raw == "~" || raw.starts_with("~/") {
        let home = std::env::var("HOME")
            .or_else(|_| std::env::var("USERPROFILE"))
            .map_err(|_| anyhow::anyhow!("cannot expand '~': $HOME is not set"))?;
        PathBuf::from(format!("{}{}", home, &raw[1..]))
    } else {
        PathBuf::from(raw)
    };

    // Prefer canonicalize (resolves symlinks, cleans . and ..).
    // Fall back to a plain absolute path when the path does not yet exist.
    match std::fs::canonicalize(&expanded) {
        Ok(p) => Ok(p),
        Err(_) if expanded.is_absolute() => Ok(expanded),
        Err(_) => Ok(std::env::current_dir()?.join(expanded)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    pub(super) async fn fixture_git_output(
        directory: &Path,
        args: &[impl AsRef<std::ffi::OsStr>],
    ) -> Output {
        let mut command = git_command(directory);
        command
            .env("GIT_CONFIG_NOSYSTEM", "1")
            .env(
                "GIT_CONFIG_GLOBAL",
                if cfg!(windows) { "NUL" } else { "/dev/null" },
            )
            .env("GIT_CONFIG_COUNT", "0")
            .env("GIT_EDITOR", "true")
            .env_remove("GIT_SEQUENCE_EDITOR")
            .args([
                "-c",
                "user.name=Muninn test",
                "-c",
                "user.email=muninn-test@example.invalid",
                "-c",
                "commit.gpgsign=false",
            ])
            .args(args);
        tokio::time::timeout(std::time::Duration::from_secs(10), command.output())
            .await
            .expect("Git fixture timed out")
            .expect("run Git fixture command")
    }

    pub(super) async fn fixture_git(directory: &Path, args: &[impl AsRef<std::ffi::OsStr>]) {
        let output = fixture_git_output(directory, args).await;
        assert!(
            output.status.success(),
            "Git fixture failed: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }

    pub(super) async fn init_fixture(path: &Path) {
        std::fs::create_dir_all(path).unwrap();
        // No template hooks or user configuration participate in fixture setup.
        fixture_git(
            path,
            &["init", "--quiet", "--template=", "--initial-branch=main"],
        )
        .await;
    }

    #[tokio::test]
    async fn enumeration_tracks_attached_detached_and_removed_worktrees() {
        let temp = tempfile::tempdir().unwrap();
        let main = temp.path().join("main");
        let attached = temp.path().join("attached");
        let detached = temp.path().join("detached");
        init_fixture(&main).await;
        let family = discover_git_checkout(&main).await.unwrap().unwrap();
        let unborn = list_git_worktrees(&family.common_dir).await.unwrap();
        assert_eq!(unborn.len(), 1);
        assert_eq!(
            unborn[0].branch.as_deref(),
            Some(std::ffi::OsStr::new("refs/heads/main"))
        );
        fixture_git(
            &main,
            &["commit", "--quiet", "--allow-empty", "-m", "initial"],
        )
        .await;
        fixture_git(
            &main,
            &[
                "worktree",
                "add",
                "-b",
                "feature",
                attached.to_str().unwrap(),
            ],
        )
        .await;
        fixture_git(
            &main,
            &["worktree", "add", "--detach", detached.to_str().unwrap()],
        )
        .await;
        let entries = list_git_worktrees(&family.common_dir).await.unwrap();
        assert_eq!(entries.len(), 3);
        let primary = entries.iter().find(|e| e.path == family.root).unwrap();
        let linked = entries
            .iter()
            .find(|e| e.path == attached.canonicalize().unwrap())
            .unwrap();
        let detached_entry = entries
            .iter()
            .find(|e| e.path == detached.canonicalize().unwrap())
            .unwrap();
        assert!(!primary.bare && !primary.detached);
        assert_eq!(
            linked.branch.as_deref(),
            Some(std::ffi::OsStr::new("refs/heads/feature"))
        );
        assert!(!linked.detached);
        assert!(detached_entry.detached);
        assert!(detached_entry.branch.is_none());
        assert!(primary.head.is_some());
        assert_eq!(primary.head, linked.head);
        assert_eq!(linked.head, detached_entry.head);
        assert_eq!(
            list_git_worktrees(
                &discover_git_checkout(&attached)
                    .await
                    .unwrap()
                    .unwrap()
                    .common_dir
            )
            .await
            .unwrap(),
            entries
        );

        fixture_git(&main, &["worktree", "remove", attached.to_str().unwrap()]).await;
        let remaining = list_git_worktrees(&family.common_dir).await.unwrap();
        assert_eq!(remaining.len(), 2);
        assert!(remaining.iter().all(|e| e.path != attached));

        // Manual deletion leaves metadata. Enumeration must not prune it.
        std::fs::remove_dir_all(&detached).unwrap();
        let missing = list_git_worktrees(&family.common_dir).await.unwrap();
        let missing_entry = missing.iter().find(|e| e.path == detached).unwrap();
        assert!(missing_entry.prunable.is_some());
        assert_eq!(
            list_git_worktrees(&family.common_dir).await.unwrap(),
            missing
        );
    }

    #[cfg(unix)]
    #[tokio::test]
    async fn enumeration_preserves_unusual_paths_and_missing_locked_worktrees() {
        use std::ffi::OsStr;
        use std::os::unix::ffi::OsStringExt;
        let temp = tempfile::tempdir().unwrap();
        let main = temp.path().join("main");
        let linked = temp
            .path()
            .join(OsString::from_vec(b"linked \xff\t\n\"\\\n".to_vec()));
        init_fixture(&main).await;
        fixture_git(
            &main,
            &["commit", "--quiet", "--allow-empty", "-m", "initial"],
        )
        .await;
        fixture_git(
            &main,
            &[
                OsStr::new("worktree"),
                OsStr::new("add"),
                OsStr::new("--detach"),
                linked.as_os_str(),
            ],
        )
        .await;
        let reason = "offline disk\nwith spaces";
        fixture_git(
            &main,
            &[
                OsStr::new("worktree"),
                OsStr::new("lock"),
                OsStr::new("--reason"),
                OsStr::new(reason),
                linked.as_os_str(),
            ],
        )
        .await;
        let family = discover_git_checkout(&main).await.unwrap().unwrap();
        let entries = list_git_worktrees(&family.common_dir).await.unwrap();
        let expected_path = linked.canonicalize().unwrap();
        let entry = entries.iter().find(|e| e.path == expected_path).unwrap();
        assert_eq!(entry.locked.as_deref(), Some(OsStr::new(reason)));
        std::fs::remove_dir_all(&linked).unwrap();
        let missing = list_git_worktrees(&family.common_dir).await.unwrap();
        assert_eq!(entries, missing);
    }

    #[tokio::test]
    async fn enumeration_distinguishes_bare_family_from_checkout_and_errors() {
        let temp = tempfile::tempdir().unwrap();
        let bare = temp.path().join("bare.git");
        std::fs::create_dir(&bare).unwrap();
        fixture_git(&bare, &["init", "--bare", "--quiet", "--template="]).await;
        let entries = list_git_worktrees(&bare).await.unwrap();
        assert_eq!(entries.len(), 1);
        assert!(entries[0].bare);
        assert_eq!(entries[0].path, bare.canonicalize().unwrap());
        assert!(entries[0].head.is_none());
        assert!(entries[0].branch.is_none());
        assert!(list_git_worktrees(temp.path()).await.is_err());
        assert!(list_git_worktrees(&temp.path().join("missing"))
            .await
            .is_err());
    }

    #[test]
    fn enumeration_rejects_incomplete_records_and_accepts_future_attributes() {
        // Use a native absolute path so this parser test also works on Windows.
        let root = std::env::temp_dir();
        let prefix = format!("worktree {}\0", root.display());
        for bytes in [
            Vec::new(),
            b"\0".to_vec(),
            b"branch refs/heads/main\0\0".to_vec(),
            b"worktree relative\0\0".to_vec(),
            prefix.as_bytes().to_vec(),
            format!("{prefix}{prefix}\0").into_bytes(),
            format!("{prefix}branch one\0branch two\0\0").into_bytes(),
        ] {
            assert!(parse_git_worktrees(&bytes).is_err());
        }
        let parsed =
            parse_git_worktrees(format!("{prefix}locked\0prunable\0future value\0\0").as_bytes())
                .unwrap();
        assert_eq!(parsed[0].path, root);
        assert_eq!(parsed[0].locked, Some(OsString::new()));
        assert_eq!(parsed[0].prunable, Some(OsString::new()));
    }

    #[tokio::test]
    async fn linked_and_detached_worktrees_share_family_but_keep_checkout_roots() {
        let temp = tempfile::tempdir().unwrap();
        let main = temp.path().join("main repo");
        let linked = temp.path().join("branch checkout");
        let detached = temp.path().join("detached checkout");
        init_fixture(&main).await;
        // Even an unborn repository has filesystem identity.
        let before_commit = discover_git_checkout(&main).await.unwrap().unwrap();
        fixture_git(
            &main,
            &["commit", "--quiet", "--allow-empty", "-m", "initial"],
        )
        .await;
        fixture_git(
            &main,
            &["worktree", "add", "-b", "feature", linked.to_str().unwrap()],
        )
        .await;
        fixture_git(
            &main,
            &["worktree", "add", "--detach", detached.to_str().unwrap()],
        )
        .await;
        std::fs::create_dir_all(linked.join("src/nested")).unwrap();

        let primary = discover_git_checkout(&main).await.unwrap().unwrap();
        let feature = discover_git_checkout(&linked.join("src/nested"))
            .await
            .unwrap()
            .unwrap();
        let detached_view = discover_git_checkout(&detached).await.unwrap().unwrap();
        assert_eq!(primary, before_commit);
        assert_eq!(
            primary.common_dir,
            main.join(".git").canonicalize().unwrap()
        );
        assert_eq!(feature.common_dir, primary.common_dir);
        assert_eq!(detached_view.common_dir, primary.common_dir);
        assert_eq!(primary.git_dir, primary.common_dir);
        assert_ne!(feature.git_dir, primary.git_dir);
        assert_ne!(detached_view.git_dir, feature.git_dir);
        assert_eq!(
            feature.git_dir,
            git_path(&linked, "--absolute-git-dir").await.unwrap()
        );
        assert_eq!(feature.root, linked.canonicalize().unwrap());
        assert_eq!(detached_view.root, detached.canonicalize().unwrap());
        assert_ne!(primary.root, feature.root);
        assert_ne!(feature.root, detached_view.root);

        let primary_input = crate::family_store::CheckoutIdentity::discover(&main)
            .await
            .unwrap();
        let linked_input = crate::family_store::CheckoutIdentity::discover(&linked)
            .await
            .unwrap();
        assert_eq!(primary_input.family, linked_input.family);
        assert_ne!(primary_input.root, linked_input.root);
        assert_ne!(primary_input.git_dir, linked_input.git_dir);
        linked_input.revalidate().await.unwrap();

        fixture_git(&linked, &["checkout", "--quiet", "-b", "another-branch"]).await;
        fixture_git(
            &linked,
            &["commit", "--quiet", "--allow-empty", "-m", "advance"],
        )
        .await;
        assert_eq!(discover_git_checkout(&linked).await.unwrap(), Some(feature));
        assert_eq!(discover_git_checkout(&main).await.unwrap(), Some(primary));
    }

    #[tokio::test]
    async fn independent_and_nested_repositories_have_distinct_families() {
        let temp = tempfile::tempdir().unwrap();
        let outer = temp.path().join("outer");
        let inner = outer.join("inner");
        let other = temp.path().join("other");
        for path in [&outer, &inner, &other] {
            init_fixture(path).await;
        }
        std::fs::create_dir_all(inner.join("src")).unwrap();
        let a = discover_git_checkout(&outer).await.unwrap().unwrap();
        let b = discover_git_checkout(&inner.join("src"))
            .await
            .unwrap()
            .unwrap();
        let c = discover_git_checkout(&other).await.unwrap().unwrap();
        assert_eq!(b.root, inner.canonicalize().unwrap());
        assert_ne!(a.common_dir, b.common_dir);
        assert_ne!(a.common_dir, c.common_dir);
        assert_ne!(b.common_dir, c.common_dir);
    }

    #[tokio::test]
    async fn non_git_and_bare_directories_have_no_checkout() {
        let temp = tempfile::tempdir().unwrap();
        assert_eq!(discover_git_checkout(temp.path()).await.unwrap(), None);
        let directory = crate::family_store::CheckoutIdentity::discover(temp.path())
            .await
            .unwrap();
        assert_eq!(
            directory.family.kind,
            crate::family_store::FamilyKind::Directory
        );
        assert_eq!(directory.family.key, directory.root);
        assert!(directory.git_dir.is_none());
        let bare = temp.path().join("bare.git");
        std::fs::create_dir(&bare).unwrap();
        fixture_git(&bare, &["init", "--bare", "--quiet", "--template="]).await;
        assert_eq!(discover_git_checkout(&bare).await.unwrap(), None);
        init_fixture(temp.path()).await;
        assert!(directory.revalidate().await.is_err());
    }

    #[tokio::test]
    async fn invalid_paths_and_broken_git_metadata_are_errors() {
        let temp = tempfile::tempdir().unwrap();
        assert!(discover_git_checkout(&temp.path().join("missing"))
            .await
            .is_err());
        let file = temp.path().join("file");
        std::fs::write(&file, "text").unwrap();
        assert!(discover_git_checkout(&file).await.is_err());
        std::fs::write(temp.path().join(".git"), "invalid gitfile\n").unwrap();
        assert!(discover_git_checkout(temp.path()).await.is_err());
    }

    #[cfg(unix)]
    #[tokio::test]
    async fn canonical_paths_preserve_non_utf8_and_trailing_newlines() {
        use std::os::unix::ffi::OsStringExt;
        let temp = tempfile::tempdir().unwrap();
        let root = temp
            .path()
            .join(OsString::from_vec(b"repo \xff\n".to_vec()));
        init_fixture(&root).await;
        let alias = temp.path().join("alias");
        std::os::unix::fs::symlink(&root, &alias).unwrap();
        let discovered = discover_git_checkout(&alias).await.unwrap().unwrap();
        assert_eq!(discovered.root, root.canonicalize().unwrap());
        assert_eq!(
            discovered.common_dir,
            root.join(".git").canonicalize().unwrap()
        );
    }
}
