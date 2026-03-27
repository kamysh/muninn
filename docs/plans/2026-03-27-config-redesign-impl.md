# Config Redesign Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Replace the single global config (with embedded repos list) with a two-layer system: `~/.config/muninn/config.toml` for global defaults and `muninn.toml` per repo for overrides and root marking.

**Architecture:** `GlobalConfig` + `RepoConfig` merge field-by-field into `EffectiveConfig`. The indexer discovers repos by scanning `scan_roots` for `muninn.toml` files. The MCP server resolves repos by walking up from `cwd`. Matches `spec/Muninn/Config.agda`.

**Tech Stack:** Rust, `toml` crate (already in deps), `ignore` crate (already in deps), existing `sqlx`/PostgreSQL stack.

---

### Task 1: New config types — `GlobalConfig`, `RepoConfig`, `EffectiveConfig`

**Files:**
- Modify: `crates/core/src/config.rs`

The current `AppConfig` becomes `GlobalConfig`. A new `RepoConfig` holds optional overrides. `EffectiveConfig` is the merged result consumed everywhere.

**Step 1: Write the failing tests**

Add to the bottom of `crates/core/src/config.rs` (inside `#[cfg(test)] mod tests`):

```rust
#[test]
fn effective_config_inherits_global_when_repo_empty() {
    let global = GlobalConfig::default();
    let repo = RepoConfig::default();
    let eff = EffectiveConfig::merge(&global, &repo, "my-repo");
    assert_eq!(eff.repo_name, "my-repo");
    assert_eq!(eff.embeddings.backend, EmbeddingBackend::Voyage);
    assert_eq!(eff.database.host, "localhost");
}

#[test]
fn effective_config_repo_overrides_embeddings() {
    let global = GlobalConfig::default();
    let repo = RepoConfig {
        repo_name: None,
        database: None,
        embeddings: Some(EmbeddingConfig {
            backend: EmbeddingBackend::Local,
            model: "all-minilm".to_string(),
            api_key: None,
            batch_size: 32,
        }),
        watcher: None,
    };
    let eff = EffectiveConfig::merge(&global, &repo, "proj");
    assert_eq!(eff.embeddings.backend, EmbeddingBackend::Local);
    assert_eq!(eff.embeddings.batch_size, 32);
    // database still from global
    assert_eq!(eff.database.port, 5432);
}

#[test]
fn effective_config_repo_name_override() {
    let global = GlobalConfig::default();
    let repo = RepoConfig { repo_name: Some("custom-name".to_string()), ..Default::default() };
    let eff = EffectiveConfig::merge(&global, &repo, "dir-name");
    assert_eq!(eff.repo_name, "custom-name");
}

#[test]
fn db_dsn_constructed_from_fields() {
    let db = DatabaseConfig {
        host: "db.internal".to_string(),
        port: 5433,
        dbname: "mydb".to_string(),
        user: "alice".to_string(),
        dsn_override: None,
    };
    assert_eq!(db.dsn(), "postgresql://alice@db.internal:5433/mydb");
}

#[test]
fn db_dsn_override_takes_precedence() {
    let db = DatabaseConfig {
        host: "localhost".to_string(),
        port: 5432,
        dbname: "muninn".to_string(),
        user: "bob".to_string(),
        dsn_override: Some("postgresql://pooler/muninn".to_string()),
    };
    assert_eq!(db.dsn(), "postgresql://pooler/muninn");
}
```

Run: `nix develop --command cargo test -p muninn-core config 2>&1 | tail -20`
Expected: FAIL — `GlobalConfig`, `RepoConfig`, `EffectiveConfig`, `DatabaseConfig::dsn` not defined yet.

**Step 2: Replace `AppConfig` with new types**

Replace the entire contents of `crates/core/src/config.rs` with:

```rust
use serde::{Deserialize, Serialize};

// ── Embedding backend ──────────────────────────────────────────────────────

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(rename_all = "lowercase")]
pub enum EmbeddingBackend {
    Voyage,
    OpenAI,
    Local,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct EmbeddingConfig {
    pub backend: EmbeddingBackend,
    pub model: String,
    pub api_key: Option<String>,
    pub batch_size: usize,
}

impl Default for EmbeddingConfig {
    fn default() -> Self {
        Self {
            backend: EmbeddingBackend::Voyage,
            model: "voyage-code-3".to_string(),
            api_key: None,
            batch_size: 64,
        }
    }
}

// ── Database config ────────────────────────────────────────────────────────

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct DatabaseConfig {
    pub host: String,
    pub port: u16,
    pub dbname: String,
    pub user: String,
    /// Optional escape hatch: if set, used verbatim instead of constructing DSN.
    /// For connection poolers or other non-standard setups.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub dsn_override: Option<String>,
}

impl DatabaseConfig {
    /// Construct a libpq DSN. Password is intentionally omitted — libpq reads
    /// it from ~/.pgpass (host:port:dbname:user:password).
    pub fn dsn(&self) -> String {
        if let Some(ref override_dsn) = self.dsn_override {
            return override_dsn.clone();
        }
        format!(
            "postgresql://{}@{}:{}/{}",
            self.user, self.host, self.port, self.dbname
        )
    }
}

impl Default for DatabaseConfig {
    fn default() -> Self {
        Self {
            host: "localhost".to_string(),
            port: 5432,
            dbname: "muninn".to_string(),
            user: std::env::var("USER").unwrap_or_else(|_| "muninn".to_string()),
            dsn_override: None,
        }
    }
}

// ── Watcher config ─────────────────────────────────────────────────────────

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct WatcherConfig {
    pub debounce_ms: u64,
}

impl Default for WatcherConfig {
    fn default() -> Self {
        Self { debounce_ms: 300 }
    }
}

// ── Indexer config ─────────────────────────────────────────────────────────

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct IndexerConfig {
    pub scan_roots: Vec<String>,
    pub scan_depth: usize,
}

impl Default for IndexerConfig {
    fn default() -> Self {
        Self {
            scan_roots: vec![],
            scan_depth: 5,
        }
    }
}

// ── Global config ──────────────────────────────────────────────────────────
// Loaded from ~/.config/muninn/config.toml

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct GlobalConfig {
    pub database: DatabaseConfig,
    pub embeddings: EmbeddingConfig,
    pub watcher: WatcherConfig,
    pub indexer: IndexerConfig,
}

impl GlobalConfig {
    pub fn config_path() -> std::path::PathBuf {
        let home = std::env::var("HOME").unwrap_or_default();
        std::path::PathBuf::from(home).join(".config/muninn/config.toml")
    }

    pub fn load() -> anyhow::Result<Self> {
        let path = Self::config_path();
        if !path.exists() {
            return Ok(Self::default());
        }
        let content = std::fs::read_to_string(&path)?;
        Ok(toml::from_str(&content)?)
    }

    pub fn save(&self) -> anyhow::Result<()> {
        let path = Self::config_path();
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        std::fs::write(&path, toml::to_string_pretty(self)?)?;
        Ok(())
    }
}

// ── Per-repo config ────────────────────────────────────────────────────────
// Loaded from <repo-root>/muninn.toml
// All fields optional — absent = inherit from GlobalConfig.

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct RepoConfig {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub repo_name: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub database: Option<DatabaseConfig>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub embeddings: Option<EmbeddingConfig>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub watcher: Option<WatcherConfig>,
}

impl RepoConfig {
    pub const FILE_NAME: &'static str = "muninn.toml";

    /// Load muninn.toml from a repo root. Returns empty config if file absent.
    pub fn load(repo_root: &std::path::Path) -> anyhow::Result<Self> {
        let path = repo_root.join(Self::FILE_NAME);
        if !path.exists() {
            return Ok(Self::default());
        }
        let content = std::fs::read_to_string(&path)?;
        Ok(toml::from_str(&content)?)
    }

    /// Create a template muninn.toml in repo_root (does nothing if already exists).
    pub fn create_template(repo_root: &std::path::Path, dir_name: &str) -> anyhow::Result<std::path::PathBuf> {
        let path = repo_root.join(Self::FILE_NAME);
        if !path.exists() {
            let content = format!(
                "# muninn.toml — repo config for {dir_name}\n\
                 # All sections are optional. Empty file marks this directory as a muninn repo root.\n\
                 # Uncomment and edit any section to override global defaults.\n\
                 \n\
                 [repo]\n\
                 name = \"{dir_name}\"\n\
                 # description = \"\"\n\
                 \n\
                 # [database]\n\
                 # host   = \"localhost\"\n\
                 # port   = 5432\n\
                 # dbname = \"muninn\"\n\
                 # user   = \"alice\"\n\
                 \n\
                 # [embeddings]\n\
                 # backend    = \"voyage\"   # voyage | openai | local\n\
                 # model      = \"voyage-code-3\"\n\
                 # api_key    = \"pa-...\"\n\
                 # batch_size = 64\n\
                 \n\
                 # [watcher]\n\
                 # debounce_ms = 300\n",
                dir_name = dir_name
            );
            std::fs::write(&path, content)?;
        }
        Ok(path)
    }
}

// ── Effective config ───────────────────────────────────────────────────────
// Merged result consumed by indexer and MCP server.

#[derive(Debug, Clone)]
pub struct EffectiveConfig {
    pub database: DatabaseConfig,
    pub embeddings: EmbeddingConfig,
    pub watcher: WatcherConfig,
    pub repo_name: String,
}

impl EffectiveConfig {
    /// Merge global defaults with per-repo overrides.
    /// `dir_name` is the fallback repo name when [repo].name is absent.
    pub fn merge(global: &GlobalConfig, repo: &RepoConfig, dir_name: &str) -> Self {
        Self {
            database:  repo.database.clone().unwrap_or_else(|| global.database.clone()),
            embeddings: repo.embeddings.clone().unwrap_or_else(|| global.embeddings.clone()),
            watcher:   repo.watcher.clone().unwrap_or_else(|| global.watcher.clone()),
            repo_name: repo.repo_name.clone().unwrap_or_else(|| dir_name.to_string()),
        }
    }
}

// ── Backward compat alias ──────────────────────────────────────────────────
// Callers that used AppConfig::load() can be migrated task by task.
pub type AppConfig = GlobalConfig;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::LineRange;

    #[test]
    fn line_range_valid() {
        let r = LineRange { start: 1, end: 10 };
        assert!(r.is_valid());
    }

    #[test]
    fn line_range_single_line_valid() {
        let r = LineRange { start: 5, end: 5 };
        assert!(r.is_valid());
    }

    #[test]
    fn line_range_inverted_invalid() {
        let r = LineRange { start: 10, end: 5 };
        assert!(!r.is_valid());
    }

    #[test]
    fn config_default_embedding_is_voyage() {
        let cfg = EmbeddingConfig::default();
        assert_eq!(cfg.backend, EmbeddingBackend::Voyage);
        assert_eq!(cfg.model, "voyage-code-3");
        assert_eq!(cfg.batch_size, 64);
    }

    #[test]
    fn config_default_debounce() {
        let cfg = WatcherConfig::default();
        assert_eq!(cfg.debounce_ms, 300);
    }

    #[test]
    fn effective_config_inherits_global_when_repo_empty() {
        let global = GlobalConfig::default();
        let repo = RepoConfig::default();
        let eff = EffectiveConfig::merge(&global, &repo, "my-repo");
        assert_eq!(eff.repo_name, "my-repo");
        assert_eq!(eff.embeddings.backend, EmbeddingBackend::Voyage);
        assert_eq!(eff.database.host, "localhost");
    }

    #[test]
    fn effective_config_repo_overrides_embeddings() {
        let global = GlobalConfig::default();
        let repo = RepoConfig {
            repo_name: None,
            database: None,
            embeddings: Some(EmbeddingConfig {
                backend: EmbeddingBackend::Local,
                model: "all-minilm".to_string(),
                api_key: None,
                batch_size: 32,
            }),
            watcher: None,
        };
        let eff = EffectiveConfig::merge(&global, &repo, "proj");
        assert_eq!(eff.embeddings.backend, EmbeddingBackend::Local);
        assert_eq!(eff.embeddings.batch_size, 32);
        assert_eq!(eff.database.port, 5432);
    }

    #[test]
    fn effective_config_repo_name_override() {
        let global = GlobalConfig::default();
        let repo = RepoConfig { repo_name: Some("custom-name".to_string()), ..Default::default() };
        let eff = EffectiveConfig::merge(&global, &repo, "dir-name");
        assert_eq!(eff.repo_name, "custom-name");
    }

    #[test]
    fn db_dsn_constructed_from_fields() {
        let db = DatabaseConfig {
            host: "db.internal".to_string(),
            port: 5433,
            dbname: "mydb".to_string(),
            user: "alice".to_string(),
            dsn_override: None,
        };
        assert_eq!(db.dsn(), "postgresql://alice@db.internal:5433/mydb");
    }

    #[test]
    fn db_dsn_override_takes_precedence() {
        let db = DatabaseConfig {
            host: "localhost".to_string(),
            port: 5432,
            dbname: "muninn".to_string(),
            user: "bob".to_string(),
            dsn_override: Some("postgresql://pooler/muninn".to_string()),
        };
        assert_eq!(db.dsn(), "postgresql://pooler/muninn");
    }
}
```

**Step 3: Run tests**

Run: `nix develop --command cargo test -p muninn-core 2>&1 | tail -20`
Expected: all tests pass including the 5 new ones.

**Step 4: Commit**

```bash
git add crates/core/src/config.rs
git commit -m "feat: replace AppConfig with GlobalConfig/RepoConfig/EffectiveConfig"
```

---

### Task 2: Update all callers of `AppConfig` → `GlobalConfig`

**Files:**
- Modify: `crates/indexer/src/main.rs`
- Modify: `crates/mcp/src/main.rs`
- Modify: `crates/cli/src/main.rs`

The `AppConfig` type alias added in Task 1 means this may be a no-op for callers that only use `AppConfig::load()`. Check each file and update any access to removed fields (e.g., `cfg.repos`, `cfg.database.dsn`).

**Step 1: Check current usages**

Run: `nix develop --command cargo build 2>&1`
Expected: compilation errors pointing to broken usages. Fix each:

- `cfg.database.dsn` → `cfg.database.dsn()`
- `cfg.repos` → removed (indexer no longer uses a repos list; MCP server resolves repo from cwd)

**Step 2: Fix `crates/indexer/src/main.rs`**

Replace the `AppConfig::load()` call and remove the repos loop. The indexer will get repo discovery in Task 3. For now, keep a stub that compiles:

```rust
use muninn_core::{config::GlobalConfig, db, embeddings::{make_backend, expected_dimension}};

let cfg = GlobalConfig::load()?;
let pool = db::connect(&cfg.database.dsn()).await?;
let embedder = Arc::from(make_backend(&cfg.embeddings));
let config_dim = expected_dimension(&cfg.embeddings);

// TODO Task 3: discover repos via scan_roots
```

**Step 3: Fix `crates/mcp/src/main.rs`**

```rust
use muninn_core::config::GlobalConfig;
let cfg = GlobalConfig::load()?;
let pool = db::connect(&cfg.database.dsn()).await?;
```

**Step 4: Fix `crates/cli/src/main.rs`**

```rust
use muninn_core::config::{GlobalConfig, RepoConfig};
let mut cfg = GlobalConfig::load()?;
let pool = db::connect(&cfg.database.dsn()).await?;
```

Also remove `cfg.repos.push(...)` and `cfg.save()` from `Commands::Register` — repo registration is now handled by `muninn.toml` creation (Task 5).

**Step 5: Build and test**

Run: `nix develop --command cargo build 2>&1 | tail -5`
Expected: `Finished` with no errors.

Run: `nix develop --command cargo test 2>&1 | grep "test result"`
Expected: all pass.

**Step 6: Commit**

```bash
git add crates/indexer/src/main.rs crates/mcp/src/main.rs crates/cli/src/main.rs
git commit -m "feat: update callers to use GlobalConfig and dsn()"
```

---

### Task 3: Indexer repo discovery via `scan_roots`

**Files:**
- Create: `crates/indexer/src/discovery.rs`
- Modify: `crates/indexer/src/main.rs`

**Step 1: Write the failing test**

Create `crates/indexer/src/discovery.rs`:

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn finds_muninn_toml_in_direct_child() {
        let tmp = tempfile::tempdir().unwrap();
        let repo_dir = tmp.path().join("myrepo");
        std::fs::create_dir(&repo_dir).unwrap();
        std::fs::write(repo_dir.join("muninn.toml"), "").unwrap();

        let found = discover_repos(tmp.path(), 3);
        assert_eq!(found.len(), 1);
        assert_eq!(found[0], repo_dir);
    }

    #[test]
    fn respects_depth_limit() {
        let tmp = tempfile::tempdir().unwrap();
        // depth 3: a/b/c/muninn.toml should not be found with scan_depth=2
        let deep = tmp.path().join("a").join("b").join("c");
        std::fs::create_dir_all(&deep).unwrap();
        std::fs::write(deep.join("muninn.toml"), "").unwrap();

        let found = discover_repos(tmp.path(), 2);
        assert!(found.is_empty());
    }

    #[test]
    fn finds_multiple_repos() {
        let tmp = tempfile::tempdir().unwrap();
        for name in &["alpha", "beta", "gamma"] {
            let d = tmp.path().join(name);
            std::fs::create_dir(&d).unwrap();
            std::fs::write(d.join("muninn.toml"), "").unwrap();
        }
        let mut found = discover_repos(tmp.path(), 3);
        found.sort();
        assert_eq!(found.len(), 3);
    }

    #[test]
    fn does_not_descend_into_repo() {
        // A nested muninn.toml inside a repo should not create a second entry
        let tmp = tempfile::tempdir().unwrap();
        let outer = tmp.path().join("outer");
        let inner = outer.join("inner");
        std::fs::create_dir_all(&inner).unwrap();
        std::fs::write(outer.join("muninn.toml"), "").unwrap();
        std::fs::write(inner.join("muninn.toml"), "").unwrap();

        // We stop descending once we find a muninn.toml, so only outer is returned
        let found = discover_repos(tmp.path(), 5);
        assert_eq!(found.len(), 1);
        assert_eq!(found[0], outer);
    }
}
```

Run: `nix develop --command cargo test -p muninn-index 2>&1 | tail -10`
Expected: FAIL — `discover_repos` not defined.

**Step 2: Add `tempfile` dev-dependency**

In `crates/indexer/Cargo.toml`:
```toml
[dev-dependencies]
tempfile = "3"
```

**Step 3: Implement `discover_repos`**

Add to `crates/indexer/src/discovery.rs`:

```rust
use std::path::{Path, PathBuf};

/// Walk `root` up to `max_depth` directory levels deep.
/// Return the path of every directory that contains a `muninn.toml` file.
/// Does not descend into directories that are themselves repo roots.
pub fn discover_repos(root: &Path, max_depth: usize) -> Vec<PathBuf> {
    let mut results = Vec::new();
    walk(root, 0, max_depth, &mut results);
    results
}

fn walk(dir: &Path, depth: usize, max_depth: usize, out: &mut Vec<PathBuf>) {
    if depth > max_depth {
        return;
    }
    if dir.join("muninn.toml").exists() {
        out.push(dir.to_owned());
        return; // do not descend further into a repo root
    }
    let Ok(entries) = std::fs::read_dir(dir) else { return };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            // skip hidden directories
            let name = path.file_name().unwrap_or_default().to_string_lossy();
            if name.starts_with('.') {
                continue;
            }
            walk(&path, depth + 1, max_depth, out);
        }
    }
}

#[cfg(test)]
mod tests {
    // ... (tests from Step 1)
}
```

Add `mod discovery;` to `crates/indexer/src/main.rs`.

**Step 4: Run tests**

Run: `nix develop --command cargo test -p muninn-index 2>&1 | tail -10`
Expected: 4 new tests pass.

**Step 5: Wire discovery into `main.rs`**

Replace the `// TODO Task 3` stub in `main.rs`:

```rust
let scan_roots = cfg.indexer.scan_roots.clone();
let scan_depth = cfg.indexer.scan_depth;

let mut repo_roots: Vec<std::path::PathBuf> = vec![];
for root in &scan_roots {
    let found = discovery::discover_repos(std::path::Path::new(root), scan_depth);
    repo_roots.extend(found);
}

for repo_path in repo_roots {
    let dir_name = repo_path.file_name()
        .unwrap_or_default()
        .to_string_lossy()
        .to_string();
    let repo_cfg = muninn_core::config::RepoConfig::load(&repo_path)?;
    let eff = muninn_core::config::EffectiveConfig::merge(&cfg, &repo_cfg, &dir_name);

    let pool2 = pool.clone();
    let embedder2 = embedder.clone();
    let eff2 = eff.clone();

    // register or update repo in DB
    let repo_dim = muninn_core::embeddings::expected_dimension_for(&eff.embeddings);
    let (repo, is_new) = match muninn_core::store::get_repo_by_path(&pool, &repo_path.to_string_lossy()).await? {
        Some(r) => (r, false),
        None => (muninn_core::store::register_repo(
            &pool, &repo_path.to_string_lossy(), &eff.repo_name, repo_dim,
        ).await?, true),
    };

    // ... rest of existing per-repo indexing + watcher logic
}
```

**Step 6: Add `expected_dimension_for` to embeddings**

In `crates/core/src/embeddings.rs`, add:

```rust
/// Return the expected embedding dimension for a given EmbeddingConfig.
pub fn expected_dimension_for(cfg: &crate::config::EmbeddingConfig) -> usize {
    match cfg.backend {
        crate::config::EmbeddingBackend::Voyage => 1024,
        crate::config::EmbeddingBackend::OpenAI => 1536,
        crate::config::EmbeddingBackend::Local  => 768,
    }
}
```

**Step 7: Build and test**

Run: `nix develop --command cargo build 2>&1 | tail -5`
Run: `nix develop --command cargo test 2>&1 | grep "test result"`
Expected: all pass.

**Step 8: Commit**

```bash
git add crates/indexer/src/discovery.rs crates/indexer/src/main.rs crates/indexer/Cargo.toml crates/core/src/embeddings.rs
git commit -m "feat: indexer discovers repos via scan_roots / muninn.toml walk"
```

---

### Task 4: MCP server — walk-up repo resolution from `cwd`

**Files:**
- Create: `crates/core/src/repo_resolver.rs`
- Modify: `crates/core/src/lib.rs`
- Modify: `crates/mcp/src/tools.rs`

**Step 1: Write the failing test**

Create `crates/core/src/repo_resolver.rs`:

```rust
#[cfg(test)]
mod tests {
    use super::*;

    fn make_tree(tmp: &std::path::Path, rel_paths: &[&str]) {
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
        // outer/muninn.toml AND outer/inner/muninn.toml — should resolve to inner
        make_tree(tmp.path(), &["muninn.toml", "inner/muninn.toml", "inner/src/file.rs"]);
        let cwd = tmp.path().join("inner/src");
        let root = find_repo_root(&cwd).unwrap();
        assert_eq!(root, tmp.path().join("inner"));
    }
}
```

Run: `nix develop --command cargo test -p muninn-core repo_resolver 2>&1 | tail -10`
Expected: FAIL — `find_repo_root` not defined.

**Step 2: Add `tempfile` dev-dependency to muninn-core**

In `crates/core/Cargo.toml`:
```toml
[dev-dependencies]
quickcheck = { workspace = true }
quickcheck_macros = { workspace = true }
tempfile = "3"
```

**Step 3: Implement `find_repo_root`**

```rust
use std::path::{Path, PathBuf};

/// Walk up the directory tree from `cwd` (inclusive) until a directory
/// containing `muninn.toml` is found. Returns the first (nearest) match.
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
```

Add `pub mod repo_resolver;` to `crates/core/src/lib.rs`.

**Step 4: Run tests**

Run: `nix develop --command cargo test -p muninn-core 2>&1 | grep "test result"`
Expected: all pass.

**Step 5: Update MCP tools to use walk-up resolution**

In `crates/mcp/src/tools.rs`, the `resolve_repo` function currently requires an explicit `repo` path. Update `SearchParams` so `repo` is optional, and fall back to walk-up from `cwd`:

```rust
#[derive(serde::Deserialize)]
struct SearchParams {
    query: String,
    repo: Option<String>,      // optional — resolved from cwd if absent
    cwd: Option<String>,       // current working directory (supplied by Claude Code)
    limit: Option<i64>,
}

async fn resolve_repo(pool: &sqlx::PgPool, params: &SearchParams) -> anyhow::Result<muninn_core::types::Repo> {
    let path = if let Some(ref explicit) = params.repo {
        explicit.clone()
    } else if let Some(ref cwd) = params.cwd {
        let cwd_path = std::path::Path::new(cwd);
        let root = muninn_core::repo_resolver::find_repo_root(cwd_path)
            .ok_or_else(|| anyhow::anyhow!("no muninn.toml found above {}", cwd))?;
        root.to_string_lossy().to_string()
    } else {
        anyhow::bail!("provide either 'repo' or 'cwd'");
    };

    muninn_core::store::get_repo_by_path(pool, &path)
        .await?
        .ok_or_else(|| anyhow::anyhow!("repo not found: {}", path))
}
```

**Step 6: Build and test**

Run: `nix develop --command cargo build 2>&1 | tail -5`
Run: `nix develop --command cargo test 2>&1 | grep "test result"`
Expected: all pass.

**Step 7: Commit**

```bash
git add crates/core/src/repo_resolver.rs crates/core/src/lib.rs crates/core/Cargo.toml crates/mcp/src/tools.rs
git commit -m "feat: MCP server resolves repo by walking up from cwd to nearest muninn.toml"
```

---

### Task 5: `muninn register` creates `muninn.toml` and opens `$EDITOR`

**Files:**
- Modify: `crates/cli/src/main.rs`

**Step 1: Update `Commands::Register`**

Replace the current `Register` handler (which adds to global config + DB) with:

```rust
Commands::Register { path, name } => {
    let repo_path = std::path::Path::new(&path);
    if !repo_path.exists() {
        anyhow::bail!("path does not exist: {}", path);
    }
    let dir_name = name.unwrap_or_else(|| {
        repo_path.file_name()
            .unwrap_or_default()
            .to_string_lossy()
            .to_string()
    });
    let toml_path = muninn_core::config::RepoConfig::create_template(repo_path, &dir_name)?;
    println!("Created: {}", toml_path.display());
    println!("Opening in $EDITOR… (save and close to finish)");

    let editor = std::env::var("EDITOR").unwrap_or_else(|_| "vi".to_string());
    std::process::Command::new(&editor)
        .arg(&toml_path)
        .status()?;

    println!("Done. Restart muninn-index to pick up the new repo.");
}
```

**Step 2: Update `Commands::Unregister`**

```rust
Commands::Unregister { path } => {
    let toml_path = std::path::Path::new(&path).join("muninn.toml");
    if !toml_path.exists() {
        println!("No muninn.toml found at: {}", path);
    } else {
        print!("Delete {}? [y/N] ", toml_path.display());
        use std::io::BufRead;
        let mut line = String::new();
        std::io::stdin().lock().read_line(&mut line)?;
        if line.trim().eq_ignore_ascii_case("y") {
            std::fs::remove_file(&toml_path)?;
            // clean up DB entry and chunks
            if let Some(repo) = muninn_core::store::get_repo_by_path(&pool, &path).await? {
                muninn_core::store::delete_repo(&pool, repo.id).await?;
            }
            println!("Unregistered: {}", path);
        } else {
            println!("Aborted.");
        }
    }
}
```

**Step 3: Build and test**

Run: `nix develop --command cargo build 2>&1 | tail -5`
Run: `nix develop --command cargo test 2>&1 | grep "test result"`
Expected: all pass.

**Step 4: Commit**

```bash
git add crates/cli/src/main.rs
git commit -m "feat: muninn register creates muninn.toml and opens \$EDITOR"
```

---

### Task 6: Remove legacy `RepoEntry` and `repos` list from global config

**Files:**
- Modify: `crates/core/src/config.rs`
- Modify: `crates/cli/src/main.rs` (remove any remaining `cfg.repos` references)

**Step 1: Verify `RepoEntry` is unused**

Run: `grep -rn "RepoEntry\|cfg\.repos" crates/`
Expected: no results (previous tasks cleaned them up). If any remain, remove them.

**Step 2: Remove `AppConfig` alias**

Remove the `pub type AppConfig = GlobalConfig;` line added in Task 1 — it was a migration aid and is no longer needed.

**Step 3: Build and test**

Run: `nix develop --command cargo build 2>&1 | tail -5`
Run: `nix develop --command cargo test 2>&1 | grep "test result"`
Expected: all pass.

**Step 4: Commit**

```bash
git add crates/core/src/config.rs crates/cli/src/main.rs
git commit -m "chore: remove legacy RepoEntry and AppConfig alias"
```

---

### Task 7: Update Agda spec — remove `Repo.config : Maybe String`

**Files:**
- Modify: `spec/Muninn/Types.agda`

The `config : Maybe String` field in `Repo` was a placeholder for a JSON blob that is now superseded by the `muninn.toml` per-repo config file. Remove it.

**Step 1: Edit `spec/Muninn/Types.agda`**

Remove the `config` field from the `Repo` record:

```agda
record Repo : Set where
  field id           : RepoId
        path         : FilePath
        name         : String
        indexedAt    : Maybe String
        embeddingDim : ℕ
```

**Step 2: Type-check**

Run: `cd spec && nix develop --command agda Muninn.agda 2>&1`
Expected: clean (no errors).

**Step 3: Remove `config` column from `types.rs`**

In `crates/core/src/types.rs`, remove `pub config: Option<serde_json::Value>` from `Repo`.

In `crates/core/src/store.rs`, remove `config` from all SELECT/INSERT queries and `row_to_repo`.

**Step 4: Build and test**

Run: `nix develop --command cargo build 2>&1 | tail -5`
Run: `nix develop --command cargo test 2>&1 | grep "test result"`
Expected: all pass.

**Step 5: Commit**

```bash
git add spec/Muninn/Types.agda crates/core/src/types.rs crates/core/src/store.rs
git commit -m "chore: remove unused Repo.config field from spec and implementation"
```