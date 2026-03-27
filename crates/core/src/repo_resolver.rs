use std::path::{Path, PathBuf};

/// Walk up the directory tree from `cwd` (inclusive) until a directory
/// containing `muninn.toml` is found. Returns the first (nearest) match.
/// Returns None if no ancestor contains muninn.toml.
pub fn find_repo_root(cwd: &Path) -> Option<PathBuf> {
    let mut current = cwd.to_path_buf();
    loop {
        if current.join("muninn.toml").exists() {
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
        make_tree(tmp.path(), &["muninn.toml"]);
        let root = find_repo_root(tmp.path()).unwrap();
        assert_eq!(root, tmp.path());
    }

    #[test]
    fn resolves_from_nested_subdir() {
        let tmp = tempfile::tempdir().unwrap();
        make_tree(tmp.path(), &["muninn.toml", "src/auth/handler.rs"]);
        let cwd = tmp.path().join("src/auth");
        let root = find_repo_root(&cwd).unwrap();
        assert_eq!(root, tmp.path());
    }

    #[test]
    fn returns_none_when_no_muninn_toml() {
        let tmp = tempfile::tempdir().unwrap();
        std::fs::create_dir_all(tmp.path().join("src")).unwrap();
        let root = find_repo_root(&tmp.path().join("src"));
        assert!(root.is_none());
    }

    #[test]
    fn stops_at_nearest_not_outermost() {
        let tmp = tempfile::tempdir().unwrap();
        // outer has muninn.toml AND outer/inner has muninn.toml
        // cwd is inside inner — should resolve to inner, not outer
        make_tree(tmp.path(), &["muninn.toml", "inner/muninn.toml", "inner/src/file.rs"]);
        let cwd = tmp.path().join("inner/src");
        let root = find_repo_root(&cwd).unwrap();
        assert_eq!(root, tmp.path().join("inner"));
    }
}