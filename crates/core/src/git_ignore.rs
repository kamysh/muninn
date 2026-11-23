//! Obtain current Git defaults; do not infer them from filesystem timestamps.
use anyhow::{ensure, Context, Result};
use ignore::{
    gitignore::{Gitignore, GitignoreBuilder},
    Match,
};
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::process::Stdio;
use tokio::io::AsyncWriteExt;

pub(crate) async fn check(root: &Path, paths: &[PathBuf]) -> Result<Vec<bool>> {
    let (aliases, native): (Vec<_>, Vec<_>) = paths
        .iter()
        .enumerate()
        .partition(|(_, path)| crate::worktrees::symlinks::has_alias(root, path, false));
    let native_paths: Vec<_> = native.iter().map(|(_, path)| (*path).clone()).collect();
    let mut answers = vec![false; paths.len()];
    for ((index, _), ignored) in native
        .into_iter()
        .zip(check_native(root, &native_paths).await?)
    {
        answers[index] = ignored;
    }
    if !aliases.is_empty() {
        let mut rules = AliasRules::load(root).await?;
        for (index, path) in aliases {
            answers[index] = rules.ignored(path)?;
        }
    }
    Ok(answers)
}

/// Git rejects paths beyond a symlink. Evaluate the same sources against the
/// displayed path for these entries, with each ancestor's own ignore file.
struct AliasRules<'a> {
    root: &'a Path,
    global: Gitignore,
    directories: HashMap<PathBuf, Gitignore>,
    ignore_case: bool,
}

impl<'a> AliasRules<'a> {
    async fn load(root: &'a Path) -> Result<Self> {
        let git = crate::repo_resolver::discover_git_checkout(root)
            .await?
            .context("alias ignore rules require a Git checkout")?;
        let get = |key: &'static str| async move {
            let output = tokio::process::Command::new("git")
                .arg("-C")
                .arg(root)
                .args(["config", "--path", "--get", key])
                .env("GIT_OPTIONAL_LOCKS", "0")
                .kill_on_drop(true)
                .output()
                .await?;
            ensure!(
                matches!(output.status.code(), Some(0 | 1)),
                "cannot read Git setting {key}"
            );
            Ok::<_, anyhow::Error>(
                output
                    .stdout
                    .strip_suffix(b"\n")
                    .unwrap_or(&output.stdout)
                    .to_vec(),
            )
        };
        let (excludes, ignore_case) =
            tokio::try_join!(get("core.excludesFile"), get("core.ignoreCase"))?;
        let ignore_case = matches!(
            ignore_case.to_ascii_lowercase().as_slice(),
            b"true" | b"yes" | b"on" | b"1"
        );
        let excludes =
            if excludes.is_empty() {
                std::env::var_os("XDG_CONFIG_HOME")
                    .map(PathBuf::from)
                    .or_else(|| {
                        std::env::var_os("HOME").map(|home| PathBuf::from(home).join(".config"))
                    })
                    .map(|base| base.join("git/ignore"))
            } else {
                Some(root.join(
                    std::str::from_utf8(&excludes).context("Git excludes path is not UTF-8")?,
                ))
            };
        let mut builder = GitignoreBuilder::new(root);
        builder.case_insensitive(ignore_case)?;
        for path in excludes
            .into_iter()
            .chain([git.common_dir.join("info/exclude")])
        {
            if path.is_file() {
                builder.add(path);
            }
        }
        Ok(Self {
            root,
            global: builder.build()?,
            directories: HashMap::new(),
            ignore_case,
        })
    }

    fn ignored(&mut self, path: &Path) -> Result<bool> {
        let ancestors: Vec<_> = path
            .ancestors()
            .take_while(|part| !part.as_os_str().is_empty())
            .collect();
        let mut rules = Vec::new();
        for member in ancestors.into_iter().rev() {
            let parent = member.parent().context("alias path has no parent")?;
            if !self.directories.contains_key(parent) {
                let mut builder = GitignoreBuilder::new(self.root.join(parent));
                builder.case_insensitive(self.ignore_case)?;
                if let Some(physical) =
                    crate::worktrees::symlinks::internal_path(self.root, parent)?
                {
                    let file = physical.join(".gitignore");
                    if std::fs::symlink_metadata(&file).is_ok_and(|meta| meta.is_file()) {
                        builder.add(file);
                    }
                }
                self.directories.insert(parent.to_owned(), builder.build()?);
            }
            rules.push(parent);
            let absolute = self.root.join(member);
            let is_dir = member != path;
            let matched = rules
                .iter()
                .rev()
                .map(|parent| self.directories[*parent].matched(&absolute, is_dir))
                .find(|matched| !matches!(matched, Match::None))
                .unwrap_or_else(|| self.global.matched(&absolute, is_dir));
            if matched.is_ignore() {
                return Ok(true);
            }
        }
        Ok(false)
    }
}

pub(crate) async fn check_native(root: &Path, paths: &[PathBuf]) -> Result<Vec<bool>> {
    let mut answers = Vec::with_capacity(paths.len());
    for batch in paths.chunks(4096) {
        let mut input = Vec::new();
        for path in batch {
            input.extend_from_slice(path.to_str().context("Git path is not UTF-8")?.as_bytes());
            input.push(0);
        }
        let mut child = tokio::process::Command::new("git")
            .arg("-C")
            .arg(root)
            .args([
                "check-ignore",
                "--no-index",
                "--stdin",
                "-z",
                "--verbose",
                "--non-matching",
            ])
            .env("GIT_OPTIONAL_LOCKS", "0")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .kill_on_drop(true)
            .spawn()?;
        let mut stdin = child.stdin.take().context("Git stdin unavailable")?;
        let (written, output) = tokio::join!(
            async move {
                stdin.write_all(&input).await?;
                drop(stdin);
                Ok::<(), std::io::Error>(())
            },
            child.wait_with_output()
        );
        written?;
        let output = output?;
        ensure!(
            matches!(output.status.code(), Some(0 | 1)),
            "Git ignore query failed: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        let mut fields: Vec<_> = output.stdout.split(|b| *b == 0).collect();
        ensure!(
            fields.pop() == Some(&[][..]) && fields.len() == batch.len() * 4,
            "incomplete Git ignore response"
        );
        for (path, fields) in batch.iter().zip(fields.as_chunks::<4>().0) {
            ensure!(
                fields[3] == path.to_str().context("Git path is not UTF-8")?.as_bytes(),
                "Git ignore response path mismatch"
            );
            answers.push(!fields[2].is_empty() && !fields[2].starts_with(b"!"));
        }
    }
    Ok(answers)
}
