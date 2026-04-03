use std::path::{Path, PathBuf};

/// Walk `root` up to `max_depth` directory levels deep.
/// Return the path of every directory that contains a `.muninn.toml` file.
/// Does not descend into directories that are themselves repo roots.
pub fn discover_repos(root: &Path, max_depth: usize, include_hidden: bool) -> Vec<PathBuf> {
    let mut results = Vec::new();
    walk(root, 0, max_depth, include_hidden, &mut results);
    results
}

fn walk(dir: &Path, depth: usize, max_depth: usize, include_hidden: bool, out: &mut Vec<PathBuf>) {
    if depth > max_depth {
        return;
    }
    if dir.join(muninn_core::config::RepoConfig::FILE_NAME).exists() {
        out.push(dir.to_owned());
        return; // do not descend further into a repo root
    }
    let Ok(entries) = std::fs::read_dir(dir) else { return };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            let name = path.file_name().unwrap_or_default().to_string_lossy();
            if !include_hidden && name.starts_with('.') {
                continue; // skip hidden directories
            }
            walk(&path, depth + 1, max_depth, include_hidden, out);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn finds_dot_muninn_toml_in_direct_child() {
        let tmp = tempfile::tempdir().unwrap();
        let repo_dir = tmp.path().join("myrepo");
        std::fs::create_dir(&repo_dir).unwrap();
        std::fs::write(repo_dir.join(".muninn.toml"), "").unwrap();

        let found = discover_repos(tmp.path(), 3, false);
        assert_eq!(found.len(), 1);
        assert_eq!(found[0], repo_dir);
    }

    #[test]
    fn respects_depth_limit() {
        let tmp = tempfile::tempdir().unwrap();
        // depth 3 means a/b/c is at depth 3 from root (a=1, b=2, c=3)
        let deep = tmp.path().join("a").join("b").join("c");
        std::fs::create_dir_all(&deep).unwrap();
        std::fs::write(deep.join(".muninn.toml"), "").unwrap();

        let found = discover_repos(tmp.path(), 2, false);
        assert!(found.is_empty(), "depth 2 should not reach depth-3 dir");
    }

    #[test]
    fn finds_multiple_repos() {
        let tmp = tempfile::tempdir().unwrap();
        for name in &["alpha", "beta", "gamma"] {
            let d = tmp.path().join(name);
            std::fs::create_dir(&d).unwrap();
            std::fs::write(d.join(".muninn.toml"), "").unwrap();
        }
        let mut found = discover_repos(tmp.path(), 3, false);
        found.sort();
        assert_eq!(found.len(), 3);
    }

    #[test]
    fn does_not_descend_into_repo() {
        let tmp = tempfile::tempdir().unwrap();
        let outer = tmp.path().join("outer");
        let inner = outer.join("inner");
        std::fs::create_dir_all(&inner).unwrap();
        std::fs::write(outer.join(".muninn.toml"), "").unwrap();
        std::fs::write(inner.join(".muninn.toml"), "").unwrap();

        // stops descending at outer — inner is not returned separately
        let found = discover_repos(tmp.path(), 5, false);
        assert_eq!(found.len(), 1);
        assert_eq!(found[0], outer);
    }

    #[test]
    fn skips_hidden_directories() {
        let tmp = tempfile::tempdir().unwrap();
        let hidden = tmp.path().join(".hidden");
        std::fs::create_dir(&hidden).unwrap();
        std::fs::write(hidden.join(".muninn.toml"), "").unwrap();

        let found = discover_repos(tmp.path(), 3, false);
        assert!(found.is_empty(), "hidden dirs should be skipped");
    }

    #[test]
    fn includes_hidden_directories_when_enabled() {
        let tmp = tempfile::tempdir().unwrap();
        let hidden = tmp.path().join(".hidden");
        std::fs::create_dir(&hidden).unwrap();
        std::fs::write(hidden.join(".muninn.toml"), "").unwrap();

        let found = discover_repos(tmp.path(), 3, true);
        assert_eq!(found.len(), 1);
        assert_eq!(found[0], hidden);
    }
}
