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
    #[serde(skip_serializing_if = "Option::is_none")]
    pub cache_dir: Option<String>,
    pub batch_size: usize,
}

impl Default for EmbeddingConfig {
    fn default() -> Self {
        Self {
            backend: EmbeddingBackend::Voyage,
            model: "voyage-code-3".to_string(),
            api_key: None,
            cache_dir: None,
            batch_size: 64,
        }
    }
}

// ── SSL mode ──────────────────────────────────────────────────────────────────

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq)]
#[serde(rename_all = "kebab-case")]
pub enum SslMode {
    Disable,
    Allow,
    Prefer,
    Require,
    VerifyCa,
    VerifyFull,
}

// ── Database config ────────────────────────────────────────────────────────

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct DatabaseConfig {
    // Required fields — must be present in every config layer.
    pub host:   String,
    pub port:   u16,
    pub dbname: String,
    pub user:   String,

    // Optional fields — absent means use the driver or pool default.
    /// If set, used verbatim as the connection string; other fields are ignored
    /// for host/port/dbname/user but SSL and pool settings still apply.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub dsn_override: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub ssl_mode: Option<SslMode>,
    /// Path to a PEM CA bundle for server certificate verification.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub ssl_root_cert: Option<String>,
    /// Path to a PEM client certificate (mutual TLS).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub ssl_client_cert: Option<String>,
    /// Path to a PEM client private key (mutual TLS).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub ssl_client_key: Option<String>,
    /// Connection pool size. Default: 10.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub max_connections: Option<u32>,
    /// Seconds to wait for a connection before giving up. Default: no timeout.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub connect_timeout: Option<u64>,
    /// Shown in pg_stat_activity. Default: binary name chosen by driver.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub application_name: Option<String>,
}

impl Default for DatabaseConfig {
    fn default() -> Self {
        Self {
            host:             "localhost".to_string(),
            port:             5432,
            dbname:           "muninn".to_string(),
            user:             std::env::var("USER").unwrap_or_else(|_| "muninn".to_string()),
            dsn_override:     None,
            ssl_mode:         None,
            ssl_root_cert:    None,
            ssl_client_cert:  None,
            ssl_client_key:   None,
            max_connections:  None,
            connect_timeout:  None,
            application_name: None,
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

// ── MCP config ───────────────────────────────────────────────────────────────

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(default)]
pub struct McpLogConfig {
    pub enabled: bool,
    pub dir: String,
    pub retention_days: u64,
    pub prune_interval_hours: u64,
}

impl Default for McpLogConfig {
    fn default() -> Self {
        Self {
            enabled: true,
            dir: "~/.local/state/muninn/mcp".to_string(),
            retention_days: 7,
            prune_interval_hours: 24,
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(default)]
pub struct McpConfig {
    #[serde(default = "default_true")]
    pub record_usage: bool,
    #[serde(default)]
    pub logging: McpLogConfig,
}

impl Default for McpConfig {
    fn default() -> Self {
        Self {
            record_usage: true,
            logging: McpLogConfig::default(),
        }
    }
}

fn default_true() -> bool {
    true
}

// ── Global config ──────────────────────────────────────────────────────────

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct GlobalConfig {
    pub database: DatabaseConfig,
    pub embeddings: EmbeddingConfig,
    pub watcher: WatcherConfig,
    #[serde(default)]
    pub mcp: McpConfig,
}

impl GlobalConfig {
    pub fn config_path() -> std::path::PathBuf {
        let home = std::env::var("HOME").unwrap_or_default();
        std::path::PathBuf::from(home).join(".config/muninn/config.toml")
    }

    pub fn load() -> anyhow::Result<Self> {
        let path = Self::config_path();
        if !path.exists() {
            anyhow::bail!(
                "no config file found at {}\n\
                 Run `muninn config init` to create one.",
                path.display()
            );
        }
        // Config may contain API keys — warn if it is readable by group or world.
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            if let Ok(meta) = std::fs::metadata(&path) {
                let mode = meta.permissions().mode();
                if mode & 0o077 != 0 {
                    eprintln!(
                        "WARNING: {} has permissions {:04o} — it may contain API keys \
                         and should be readable only by the owner (chmod 600 {:?})",
                        path.display(), mode & 0o777, path
                    );
                }
            }
        }
        let content = std::fs::read_to_string(&path)?;
        Ok(toml::from_str(&content)?)
    }

    /// Create a template config at the default path.
    /// Returns an error if the file already exists.
    pub fn create_template() -> anyhow::Result<std::path::PathBuf> {
        let path = Self::config_path();
        if path.exists() {
            anyhow::bail!("config already exists at {}", path.display());
        }
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        std::fs::write(&path, CONFIG_TEMPLATE)?;
        Ok(path)
    }
}

const CONFIG_TEMPLATE: &str = r#"# ~/.config/muninn/config.toml — muninn global configuration
#
# Lines marked REQUIRED must be filled in before muninn will work correctly.
# Everything else can be left at its default value to start.
#
# After editing, run:  muninn register <path/to/your/repo>
#                then: muninn index    <path/to/your/repo>

# ── Database ──────────────────────────────────────────────────────────────────
# muninn stores chunks, embeddings, and the symbol graph in PostgreSQL.
# Make sure the database exists before running muninn:
#
#   createdb muninn
#   psql muninn -c 'CREATE EXTENSION IF NOT EXISTS vector;'
#   psql muninn -c 'CREATE EXTENSION IF NOT EXISTS age;'

[database]
host   = "localhost"
port   = 5432
dbname = "muninn"
user   = "YOUR_DB_USER"    # REQUIRED — replace with your PostgreSQL username (e.g. "alice")

# Password: muninn never stores a password here.
# Add a line to ~/.pgpass instead:  localhost:5432:muninn:alice:yourpassword
# (file must be chmod 600)

# ── Optional connection settings ──────────────────────────────────────────────
# ssl_mode = "prefer"        # disable | allow | prefer | require | verify-ca | verify-full
# ssl_root_cert   = "/path/to/ca.pem"           # CA bundle for server cert verification
# ssl_client_cert = "/path/to/client-cert.pem"  # client certificate (mutual TLS)
# ssl_client_key  = "/path/to/client-key.pem"   # client private key  (mutual TLS)
# max_connections = 10       # connection pool size
# connect_timeout = 30       # seconds; omit for no timeout
# application_name = "muninn"  # shown in pg_stat_activity

# If you need a fully custom connection string (e.g. Unix socket, special params),
# uncomment dsn_override — host/port/dbname/user above are ignored for routing,
# but ssl_mode and pool settings above still apply on top.
# dsn_override = "postgresql://alice@localhost:5432/muninn"

# ── Embeddings ────────────────────────────────────────────────────────────────
# Embeddings power semantic (vector) search.  Choose one backend:
#
#   voyage  — Voyage AI (https://www.voyageai.com).  Best quality for code.
#             Get a key at https://dash.voyageai.com  →  API Keys.
#             Default model: voyage-code-3 (1024 dims).
#
#   openai  — OpenAI Embeddings API.
#             Get a key at https://platform.openai.com  →  API keys.
#             Suggested model: text-embedding-3-small (1536 dims).
#
#   local   — No API key required.  Runs BGE-Base-EN-v1.5 (768 dims) entirely
#             on-device via ONNX (CPU).  ~200 MB download on first use.
#             Good quality; lower than code-trained API backends (voyage/openai).
#
# WARNING: the backend (and therefore the vector dimension) is frozen after the
# first index run.  To switch backends you must unregister and re-index the repo.

[embeddings]
backend    = "voyage"           # voyage | openai | local
model      = "voyage-code-3"
api_key    = "YOUR_API_KEY"     # REQUIRED for voyage/openai — paste your key here
cache_dir  = "/path/to/cache"   # optional: local model cache directory
batch_size = 64                 # texts sent to the API in one request; reduce if you hit rate limits

# ── Watcher ───────────────────────────────────────────────────────────────────
# The muninn-index daemon watches your repos for file changes and re-indexes
# modified files automatically.  debounce_ms is how long to wait after the last
# change before triggering a re-index (avoids thrashing during large saves/rebases).
# The daemon discovers repos automatically from the database — no scan_roots needed.
# Use `muninn register <path>` to add a repo and `muninn unregister <path>` to remove it.

[watcher]
debounce_ms = 300   # milliseconds; 300 is a good default for most editors

# ── MCP (Claude Code) ─────────────────────────────────────────────────────────
# muninn-mcp serves search tools to Claude Code and can keep a local usage log.
# Logs are rotated daily; old logs are pruned periodically.

[mcp]
record_usage = true  # write aggregate usage stats into the database

[mcp.logging]
enabled = true
dir = "~/.local/state/muninn/mcp"
retention_days = 7
prune_interval_hours = 24
"#;

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
    pub const FILE_NAME: &'static str = ".muninn.toml";

    /// Load .muninn.toml from a repo root. Returns empty config if file absent.
    pub fn load(repo_root: &std::path::Path) -> anyhow::Result<Self> {
        let path = repo_root.join(Self::FILE_NAME);
        if !path.exists() {
            return Ok(Self::default());
        }
        let content = std::fs::read_to_string(&path)?;
        Ok(toml::from_str(&content)?)
    }

    /// Create a template .muninn.toml in repo_root (does nothing if already exists).
    /// Returns the path to the file.
    pub fn create_template(repo_root: &std::path::Path, dir_name: &str) -> anyhow::Result<std::path::PathBuf> {
        let path = repo_root.join(Self::FILE_NAME);
        if !path.exists() {
            let content = format!(
                "# .muninn.toml — per-repo config for {dir_name}\n\
                 #\n\
                 # The presence of this file marks the directory as a muninn repo root.\n\
                 # An empty file (everything commented out) is perfectly valid — all settings\n\
                 # are inherited from ~/.config/muninn/config.toml.\n\
                 #\n\
                 # Uncomment and edit only the sections you need to override.\n\
                 # After editing, run:  muninn index <path/to/this/repo>\n\
                 \n\
                 # repo_name = \"{dir_name}\"\n\
                 # Override the display name shown in `muninn list` and `muninn status`.\n\
                 # Default: the directory name.\n\
                 \n\
                 # [database]\n\
                 # Override to use a different PostgreSQL database for this repo.\n\
                 # Useful when isolating large repos or using a remote database.\n\
                 # host   = \"localhost\"\n\
                 # port   = 5432\n\
                 # dbname = \"muninn\"\n\
                 # user   = \"alice\"\n\
                 # dsn_override = \"postgresql://alice@localhost:5432/muninn\"\n\
                 \n\
                 # [embeddings]\n\
                 # Override to use a different embedding backend for this repo.\n\
                 # WARNING: changing backend after the first index requires re-indexing\n\
                 # (run `muninn unregister` then `muninn register` + `muninn index`).\n\
                 # backend    = \"voyage\"   # voyage | openai | local\n\
                 # model      = \"voyage-code-3\"\n\
                 # api_key    = \"pa-...\"\n\
                 # cache_dir  = \"/path/to/cache\"   # local-only\n\
                 # batch_size = 64\n\
                 \n\
                 # [watcher]\n\
                 # Override the file-change debounce for this repo.\n\
                 # Increase if you see excessive re-indexing during large rebases.\n\
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
                cache_dir: None,
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
    fn repo_config_template_parses_without_error() {
        let tmp = tempfile::tempdir().unwrap();
        RepoConfig::create_template(tmp.path(), "test-repo").unwrap();
        let loaded = RepoConfig::load(tmp.path()).unwrap();
        // template has everything commented out — should load as all-None
        assert!(loaded.repo_name.is_none());
        assert!(loaded.database.is_none());
        assert!(loaded.embeddings.is_none());
        assert!(loaded.watcher.is_none());
    }
}
