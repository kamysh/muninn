use super::{observe_file, scan, Scan};
use crate::{family_policy::runtime::Selection, git_ignore, pipeline::Decision};
use anyhow::{ensure, Context, Result};
use std::{
    collections::BTreeSet,
    path::{Path, PathBuf},
};

async fn ls_files(root: &Path, option: &str) -> Result<Vec<u8>> {
    let output = tokio::process::Command::new("git")
        .arg("-C")
        .arg(root)
        .args(["ls-files", "-z", option])
        .env("GIT_OPTIONAL_LOCKS", "0")
        .kill_on_drop(true)
        .output()
        .await?;
    ensure!(
        output.status.success(),
        "Git checkout inventory failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    Ok(output.stdout)
}

fn selected_path(selection: &Selection, path: &Path) -> bool {
    selection.classify(path, false) != Decision::Drop
        && path
            .ancestors()
            .skip(1)
            .filter(|parent| !parent.as_os_str().is_empty())
            .all(|parent| selection.classify(parent, true) != Decision::Drop)
}

/// Git supplies the index and untracked paths. Selection may explicitly
/// include an ignored path, so leave ignored entries in the inventory.
/// The working bytes establish identity, including filters and unstaged edits.
pub(super) async fn read(root: &Path, selection: &Selection) -> Result<Scan> {
    let (tracked, untracked) =
        tokio::try_join!(ls_files(root, "--stage"), ls_files(root, "--others"))?;
    let mut candidates = BTreeSet::new();
    for entry in tracked
        .split(|byte| *byte == 0)
        .filter(|entry| !entry.is_empty())
    {
        let separator = entry
            .iter()
            .position(|byte| *byte == b'\t')
            .context("Git index entry is missing its path")?;
        let (index_entry, path) = entry.split_at(separator);
        let path = PathBuf::from(std::str::from_utf8(&path[1..])?);
        if selected_path(selection, &path) {
            // The existing scanner traverses initialized submodules.
            if index_entry.starts_with(b"160000 ") {
                return scan(root, selection).await;
            }
            candidates.insert(path);
        }
    }
    for entry in untracked
        .split(|byte| *byte == 0)
        .filter(|path| !path.is_empty())
    {
        let path = PathBuf::from(std::str::from_utf8(entry)?);
        if selected_path(selection, &path) {
            // Git reports a nested repository as one untracked directory.
            if entry.ends_with(b"/") {
                return scan(root, selection).await;
            }
            candidates.insert(path);
        }
    }
    let paths: Vec<_> = candidates
        .into_iter()
        .filter(|path| {
            // Git refuses check-ignore for a tracked descendant replaced by a
            // symlink or non-directory. That descendant is absent from the view.
            path.ancestors()
                .skip(1)
                .filter(|p| !p.as_os_str().is_empty())
                .all(|parent| {
                    !std::fs::symlink_metadata(root.join(parent))
                        .is_ok_and(|metadata| !metadata.is_dir())
                })
        })
        .collect();
    let ignored = git_ignore::check(root, &paths).await?;
    let mut scan = Scan::default();
    for (path, ignored) in paths.into_iter().zip(ignored) {
        if selection.classify_with_git(&path, false, ignored) != Decision::Drop {
            if let Some(file) = observe_file(root, selection, &path, &mut scan.unreadable)? {
                scan.files.push(file);
            }
        }
    }
    Ok(scan)
}
