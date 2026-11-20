//! Obtain current Git defaults; do not infer them from filesystem timestamps.
use anyhow::{ensure, Context, Result};
use std::path::{Path, PathBuf};
use std::process::Stdio;
use tokio::io::AsyncWriteExt;

pub(crate) async fn check(root: &Path, paths: &[PathBuf]) -> Result<Vec<bool>> {
    let mut answers = Vec::with_capacity(paths.len());
    for batch in paths.chunks(128) {
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
