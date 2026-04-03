use std::path::{Path, PathBuf};

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

/// Walk up the directory tree from `cwd` (inclusive) until a directory
/// containing `.muninn.toml` is found. Returns the first (nearest) match.
/// Returns None if no ancestor contains .muninn.toml.
pub fn find_repo_root(cwd: &Path) -> Option<PathBuf> {
    let mut current = cwd.to_path_buf();
    loop {
        if current.join(crate::config::RepoConfig::FILE_NAME).exists() {
            return Some(current);
        }
        if !current.pop() {
            return None;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_tree(tmp: &Path, rel_paths: &[&str]) {
        for p in rel_paths {
            let full = tmp.join(p);
            if let Some(parent) = full.parent() {
                std::fs::create_dir_all(parent).unwrap();
            }
            std::fs::write(&full, "").unwrap();
        }
    }

    #[test]
    fn resolves_from_direct_repo_root() {
        let tmp = tempfile::tempdir().unwrap();
        make_tree(tmp.path(), &[".muninn.toml"]);
        let root = find_repo_root(tmp.path()).unwrap();
        assert_eq!(root, tmp.path());
    }

    #[test]
    fn resolves_from_nested_subdir() {
        let tmp = tempfile::tempdir().unwrap();
        make_tree(tmp.path(), &[".muninn.toml", "src/auth/handler.rs"]);
        let cwd = tmp.path().join("src/auth");
        let root = find_repo_root(&cwd).unwrap();
        assert_eq!(root, tmp.path());
    }

    #[test]
    fn returns_none_when_no_dot_muninn_toml() {
        let tmp = tempfile::tempdir().unwrap();
        std::fs::create_dir_all(tmp.path().join("src")).unwrap();
        let root = find_repo_root(&tmp.path().join("src"));
        assert!(root.is_none());
    }

    #[test]
    fn stops_at_nearest_not_outermost() {
        let tmp = tempfile::tempdir().unwrap();
        // outer has .muninn.toml AND outer/inner has .muninn.toml
        // cwd is inside inner — should resolve to inner, not outer
        make_tree(tmp.path(), &[".muninn.toml", "inner/.muninn.toml", "inner/src/file.rs"]);
        let cwd = tmp.path().join("inner/src");
        let root = find_repo_root(&cwd).unwrap();
        assert_eq!(root, tmp.path().join("inner"));
    }
}
