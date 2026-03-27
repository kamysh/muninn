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
    #[serde(skip_serializing_if = "Option::is_none")]
    pub dsn_override: Option<String>,
}

impl DatabaseConfig {
    /// Construct a libpq DSN. Password intentionally omitted — libpq reads
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
    /// Returns the path to the file.
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

// ── Backward compat alias (temporary — removed in Task 6) ─────────────────
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