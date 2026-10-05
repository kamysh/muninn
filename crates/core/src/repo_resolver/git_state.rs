use super::{
    check_git_output, discover_git_checkout, git_output, git_rev_parse, parse_git_path, GitCheckout,
};
use anyhow::{ensure, Context};
use std::path::{Path, PathBuf};

/// Observed blockers in one checkout. Ordinary staged/unstaged edits are allowed.
/// Rebase metadata remains a blocker after conflicts have been resolved, including
/// an interactive edit stop. `rebase-apply` also conservatively covers `git am`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct GitOperationState {
    pub merge: bool,
    pub rebase_merge: bool,
    pub rebase_apply: bool,
    pub unmerged_index: bool,
}

impl GitOperationState {
    pub fn is_blocked(self) -> bool {
        self.merge || self.rebase_merge || self.rebase_apply || self.unmerged_index
    }
}

/// Inspect without changing Git or Muninn state. Errors mean unknown, never clear:
/// callers must retain the previous snapshot as stale (or remain pending if none
/// exists) and retry. The result is not an atomic snapshot or a publication lock;
/// reconciliation must recheck state and checkout generation before publication.
pub async fn inspect_git_operation_state(
    checkout: &GitCheckout,
) -> anyhow::Result<GitOperationState> {
    validate_checkout(checkout).await?;
    // Ask Git to route every path to this checkout's administrative directory.
    // Canonicalization would fail precisely when these markers are absent.
    let mut paths = Vec::new();
    for name in ["MERGE_HEAD", "rebase-merge", "rebase-apply"] {
        let output = git_rev_parse(
            &checkout.root,
            &["--path-format=absolute", "--git-path", name],
        )
        .await?;
        check_git_output(&output, &checkout.root)?;
        paths.push(parse_git_path(&output.stdout)?);
    }
    let before = operation_markers(&paths).await?;
    let output = git_output(&checkout.root, &["ls-files", "--unmerged", "-z"]).await?;
    check_git_output(&output, &checkout.root)?;
    let after = operation_markers(&paths).await?;
    // A missing or replaced checkout must not be mistaken for a clear state in
    // an enclosing repository. This also catches disappearance of Git metadata.
    validate_checkout(checkout).await?;
    Ok(GitOperationState {
        merge: before[0] || after[0],
        rebase_merge: before[1] || after[1],
        rebase_apply: before[2] || after[2],
        unmerged_index: !output.stdout.is_empty(),
    })
}

async fn validate_checkout(checkout: &GitCheckout) -> anyhow::Result<()> {
    ensure!(
        discover_git_checkout(&checkout.root).await?.as_ref() == Some(checkout),
        "Git checkout identity changed or disappeared: {}",
        checkout.root.display()
    );
    Ok(())
}

async fn operation_markers(paths: &[PathBuf]) -> anyhow::Result<[bool; 3]> {
    let mut present = [false; 3];
    for (index, path) in paths.iter().enumerate() {
        present[index] = marker_present(path).await?;
    }
    Ok(present)
}

async fn marker_present(path: &Path) -> anyhow::Result<bool> {
    match tokio::fs::symlink_metadata(path).await {
        Ok(_) => Ok(true),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(false),
        Err(error) => Err(error).with_context(|| format!("inspect Git marker {}", path.display())),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::repo_resolver::tests::{fixture_git, fixture_git_output, init_fixture};

    async fn commit_file(root: &Path, name: &str, contents: &str) {
        std::fs::write(root.join(name), contents).unwrap();
        fixture_git(root, &["add", "--", name]).await;
        fixture_git(root, &["commit", "--quiet", "-m", contents]).await;
    }

    async fn inspect(root: &Path) -> GitOperationState {
        let checkout = discover_git_checkout(root).await.unwrap().unwrap();
        inspect_git_operation_state(&checkout).await.unwrap()
    }

    async fn conflicting_family(temp: &Path) -> (PathBuf, PathBuf) {
        let main = temp.join("main repo");
        let linked = temp.join("linked checkout");
        init_fixture(&main).await;
        commit_file(&main, "file", "base\n").await;
        fixture_git(
            &main,
            &["worktree", "add", "-b", "feature", linked.to_str().unwrap()],
        )
        .await;
        commit_file(&main, "file", "main\n").await;
        commit_file(&linked, "file", "feature\n").await;
        (main, linked)
    }

    #[tokio::test]
    async fn ordinary_edits_and_missing_operation_markers_are_clear() {
        let temp = tempfile::tempdir().unwrap();
        init_fixture(temp.path()).await;
        assert_eq!(inspect(temp.path()).await, GitOperationState::default());
        commit_file(temp.path(), "file", "base\n").await;
        std::fs::write(temp.path().join("file"), "staged\n").unwrap();
        fixture_git(temp.path(), &["add", "file"]).await;
        std::fs::write(temp.path().join("file"), "unstaged\n").unwrap();
        // Names in the source tree are not administrative operation markers.
        std::fs::write(temp.path().join("MERGE_HEAD"), "ordinary file").unwrap();
        std::fs::create_dir(temp.path().join("rebase-merge")).unwrap();
        assert!(!inspect(temp.path()).await.is_blocked());
    }

    #[tokio::test]
    async fn conflicted_merge_is_checkout_local_and_remains_blocked_until_continue() {
        let temp = tempfile::tempdir().unwrap();
        let (main, linked) = conflicting_family(temp.path()).await;
        let output = fixture_git_output(&linked, &["merge", "--no-edit", "main"]).await;
        assert_eq!(output.status.code(), Some(1));
        assert_eq!(
            inspect(&linked).await,
            GitOperationState {
                merge: true,
                unmerged_index: true,
                ..GitOperationState::default()
            }
        );
        assert!(!inspect(&main).await.is_blocked());
        std::fs::write(linked.join("file"), "resolved\n").unwrap();
        fixture_git(&linked, &["add", "file"]).await;
        assert_eq!(
            inspect(&linked).await,
            GitOperationState {
                merge: true,
                ..GitOperationState::default()
            }
        );
        fixture_git(&linked, &["merge", "--continue"]).await;
        assert!(!inspect(&linked).await.is_blocked());
    }

    #[tokio::test]
    async fn merge_abort_recovers_and_quit_does_not_hide_unmerged_index() {
        let temp = tempfile::tempdir().unwrap();
        let (main, linked) = conflicting_family(temp.path()).await;
        for finish in ["--abort", "--quit"] {
            let output = fixture_git_output(&main, &["merge", "--no-edit", "feature"]).await;
            assert_eq!(output.status.code(), Some(1));
            assert!(inspect(&main).await.merge);
            assert!(!inspect(&linked).await.is_blocked());
            fixture_git(&main, &["merge", finish]).await;
            let state = inspect(&main).await;
            assert!(!state.merge);
            assert_eq!(state.unmerged_index, finish == "--quit");
            assert_eq!(state.is_blocked(), finish == "--quit");
        }
        fixture_git(&main, &["reset", "--hard", "HEAD"]).await;
        assert!(!inspect(&main).await.is_blocked());
    }

    #[tokio::test]
    async fn merge_without_conflicts_stays_blocked_until_committed() {
        let temp = tempfile::tempdir().unwrap();
        let main = temp.path().join("main");
        init_fixture(&main).await;
        commit_file(&main, "base", "base\n").await;
        fixture_git(&main, &["checkout", "-b", "feature"]).await;
        commit_file(&main, "feature", "feature\n").await;
        fixture_git(&main, &["checkout", "main"]).await;
        fixture_git(&main, &["merge", "--no-ff", "--no-commit", "feature"]).await;
        assert_eq!(
            inspect(&main).await,
            GitOperationState {
                merge: true,
                ..GitOperationState::default()
            }
        );
        fixture_git(&main, &["merge", "--continue"]).await;
        assert!(!inspect(&main).await.is_blocked());
    }

    #[tokio::test]
    async fn both_rebase_backends_block_until_continue_skip_or_abort() {
        for backend in ["--merge", "--apply"] {
            for finish in ["--continue", "--skip", "--abort"] {
                let temp = tempfile::tempdir().unwrap();
                let (main, linked) = conflicting_family(temp.path()).await;
                let output = fixture_git_output(&linked, &["rebase", backend, "main"]).await;
                assert_eq!(output.status.code(), Some(1), "{backend} {finish}");
                let blocked = GitOperationState {
                    rebase_merge: backend == "--merge",
                    rebase_apply: backend == "--apply",
                    unmerged_index: true,
                    ..GitOperationState::default()
                };
                assert_eq!(inspect(&linked).await, blocked, "{backend} {finish}");
                assert!(!inspect(&main).await.is_blocked());
                if finish == "--continue" {
                    std::fs::write(linked.join("file"), "resolved\n").unwrap();
                    fixture_git(&linked, &["add", "file"]).await;
                    assert_eq!(
                        inspect(&linked).await,
                        GitOperationState {
                            unmerged_index: false,
                            ..blocked
                        }
                    );
                }
                fixture_git(&linked, &["rebase", finish]).await;
                assert!(!inspect(&linked).await.is_blocked(), "{backend} {finish}");
            }
        }
    }

    #[cfg(unix)]
    #[tokio::test]
    async fn interactive_edit_stop_is_blocked_without_conflicts() {
        let temp = tempfile::tempdir().unwrap();
        let main = temp.path().join("main");
        let linked = temp.path().join("linked\ncheckout");
        init_fixture(&main).await;
        commit_file(&main, "base", "base\n").await;
        fixture_git(
            &main,
            &["worktree", "add", "-b", "feature", linked.to_str().unwrap()],
        )
        .await;
        commit_file(&linked, "feature", "feature\n").await;
        fixture_git(
            &linked,
            &[
                "-c",
                "sequence.editor=sed -i.bak -e s/^pick/edit/",
                "rebase",
                "--interactive",
                "main",
            ],
        )
        .await;
        assert_eq!(
            inspect(&linked).await,
            GitOperationState {
                rebase_merge: true,
                ..GitOperationState::default()
            }
        );
        assert!(!inspect(&main).await.is_blocked());
        fixture_git(&linked, &["rebase", "--continue"]).await;
        assert!(!inspect(&linked).await.is_blocked());
    }

    #[tokio::test]
    async fn inspection_errors_and_lost_checkout_identity_never_report_clear() {
        let temp = tempfile::tempdir().unwrap();
        let outer = temp.path().join("outer");
        let inner = outer.join("inner");
        init_fixture(&outer).await;
        init_fixture(&inner).await;
        let checkout = discover_git_checkout(&inner).await.unwrap().unwrap();
        // Git itself reports corrupt index data as an error.
        std::fs::write(inner.join(".git/index"), "not an index").unwrap();
        assert!(inspect_git_operation_state(&checkout).await.is_err());
        std::fs::remove_file(inner.join(".git/index")).unwrap();
        assert!(!inspect_git_operation_state(&checkout)
            .await
            .unwrap()
            .is_blocked());
        // Discovery would otherwise fall back to the enclosing repository.
        std::fs::remove_dir_all(inner.join(".git")).unwrap();
        assert!(inspect_git_operation_state(&checkout).await.is_err());
        std::fs::remove_dir(&inner).unwrap();
        assert!(inspect_git_operation_state(&checkout).await.is_err());
    }
}
