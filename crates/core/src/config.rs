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
#[serde(deny_unknown_fields)]
pub struct EmbeddingConfig {
    pub backend: EmbeddingBackend,
    /// Required for `voyage` and `openai`; ignored (and not required) for `local`,
    /// which uses a hardcoded bundled model.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub model: Option<String>,
    pub api_key: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub cache_dir: Option<String>,
    pub batch_size: usize,
}

impl Default for EmbeddingConfig {
    fn default() -> Self {
        Self {
            backend: EmbeddingBackend::Voyage,
            model: Some("voyage-code-3".to_string()),
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
#[serde(deny_unknown_fields)]
pub struct DatabaseConfig {
    // Required fields — must be present in every config layer.
    pub host: String,
    pub port: u16,
    pub dbname: String,
    pub user: String,

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
            host: "localhost".to_string(),
            port: 5432,
            dbname: "muninn".to_string(),
            user: std::env::var("USER").unwrap_or_else(|_| "muninn".to_string()),
            dsn_override: None,
            ssl_mode: None,
            ssl_root_cert: None,
            ssl_client_cert: None,
            ssl_client_key: None,
            max_connections: None,
            connect_timeout: None,
            application_name: None,
        }
    }
}

// ── Watcher config ─────────────────────────────────────────────────────────

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct WatcherConfig {
    pub debounce_ms: u64,
}

impl Default for WatcherConfig {
    fn default() -> Self {
        Self { debounce_ms: 300 }
    }
}

// ── Index config ─────────────────────────────────────────────────────────────

/// Shipped default `exclude` globs (drop — degenerate / generated junk).
/// Spec: Muninn.Config.excludeDefaults.
pub const EXCLUDE_DEFAULTS: &[&str] = &[
    ".git/",
    "**/*.min.js",
    "**/*.min.css",
    "**/*.map",
    "**/*.snap",
    "**/package-lock.json",
    "**/yarn.lock",
    "**/pnpm-lock.yaml",
    "**/Cargo.lock",
    "**/poetry.lock",
    "**/Gemfile.lock",
    "**/composer.lock",
];

/// Shipped default `vendor` globs (down-weight — real code, rarely wanted first).
/// Spec: Muninn.Config.vendorDefaults.
pub const VENDOR_DEFAULTS: &[&str] = &[
    "**/node_modules/**",
    "**/vendor/**",
    "vendor/",
    "**/.venv/**",
    "**/venv/**",
    "**/site-packages/**",
    "**/target/**",
    "**/dist/**",
    "**/build/**",
    "**/.tox/**",
    "**/__pycache__/**",
];

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Default)]
#[serde(default, deny_unknown_fields)]
pub struct IndexConfig {
    /// Glob patterns (relative to the repo root) to DROP from indexing entirely.
    /// muninn indexes everything by default — including files normally hidden by
    /// .gitignore — because they are often worth searching. Resolution layers
    /// shipped defaults ++ global ++ repo (last-match-wins, `!pattern` negates);
    /// see `EffectiveConfig::merge`. Spec: Muninn.Config.exclude.
    pub exclude: Vec<String>,
    /// Glob patterns to classify as Tier 2 (vendored): indexed but down-weighted
    /// in search and embedded lazily, rather than dropped. Same layered-fold
    /// resolution as `exclude`. Spec: Muninn.Config.vendor.
    pub vendor: Vec<String>,
}

// ── MCP config ───────────────────────────────────────────────────────────────

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(default, deny_unknown_fields)]
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
#[serde(default, deny_unknown_fields)]
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
#[serde(deny_unknown_fields)]
pub struct GlobalConfig {
    pub database: DatabaseConfig,
    pub embeddings: EmbeddingConfig,
    pub watcher: WatcherConfig,
    #[serde(default)]
    pub index: IndexConfig,
    #[serde(default)]
    pub mcp: McpConfig,
}

impl GlobalConfig {
    pub fn config_path() -> std::path::PathBuf {
        let home = std::env::var("HOME").unwrap_or_default();
        std::path::PathBuf::from(home).join(".config/muninn/config.toml")
    }

    pub fn template_content() -> &'static str {
        CONFIG_TEMPLATE
    }

    pub fn from_toml_str(content: &str) -> anyhow::Result<Self> {
        toml::from_str(content).map_err(|e| anyhow::anyhow!("{}", e))
    }

    pub fn validate(&self) -> anyhow::Result<()> {
        anyhow::ensure!(
            !self.database.host.trim().is_empty(),
            "[database] host must not be empty"
        );
        anyhow::ensure!(
            !self.database.dbname.trim().is_empty(),
            "[database] dbname must not be empty"
        );
        anyhow::ensure!(
            !self.database.user.trim().is_empty(),
            "[database] user must not be empty"
        );
        anyhow::ensure!(
            self.embeddings.batch_size > 0,
            "[embeddings] batch_size must be greater than 0"
        );
        if self.embeddings.backend != EmbeddingBackend::Local {
            anyhow::ensure!(
                self.embeddings
                    .model
                    .as_deref()
                    .map(|s| !s.trim().is_empty())
                    .unwrap_or(false),
                "[embeddings] model is required for voyage and openai backends"
            );
        }
        Ok(())
    }

    pub fn load() -> anyhow::Result<Self> {
        let path = Self::config_path();
        if !path.exists() {
            anyhow::bail!(
                "no config file found at {}\n\
                 Run `muninn config` to create one.",
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
                        path.display(),
                        mode & 0o777,
                        path
                    );
                }
            }
        }
        let content = std::fs::read_to_string(&path)?;
        Ok(toml::from_str(&content)?)
    }

    pub fn load_from(path: &std::path::Path) -> anyhow::Result<Self> {
        let content = std::fs::read_to_string(path)
            .map_err(|e| anyhow::anyhow!("cannot read config {}: {}", path.display(), e))?;
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
# After editing, run:  muninn add <path/to/your/repo>

# ── Database ──────────────────────────────────────────────────────────────────
# muninn stores chunks, embeddings, and the symbol graph in PostgreSQL.
# See docs/get-started.md — Step 2 shows how to create the database and user.

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
#   local   — No API key required.  Runs potion-base-32M static embeddings
#             (512 dims) entirely on-device, pure-Rust.  ~120 MB download on
#             first use; embeds ~6k chunks/sec (fast enough to index deps too).
#             Lower contextual quality than a transformer (voyage/openai) but
#             ample for code search.
#
# WARNING: the backend (and therefore the vector dimension) is frozen after the
# first index run.  To switch backends you must unregister and re-index the repo.

[embeddings]
backend    = "voyage"           # voyage | openai | local
model      = "voyage-code-3"    # REQUIRED for voyage/openai; omit for local (model is bundled)
api_key    = "YOUR_API_KEY"     # REQUIRED for voyage/openai — paste your key here
cache_dir  = "/path/to/cache"   # optional: local model cache directory
batch_size = 64                 # texts sent to the API in one request; reduce if you hit rate limits

# ── Watcher ───────────────────────────────────────────────────────────────────
# The muninn-index daemon watches your repos for file changes and re-indexes
# modified files automatically.  debounce_ms is how long to wait after the last
# change before triggering a re-index (avoids thrashing during large saves/rebases).
# The daemon discovers repos automatically from the database — no scan_roots needed.
# Use `muninn add <path>` to add a repo and `muninn remove <path>` to remove it.

[watcher]
debounce_ms = 300   # milliseconds; 300 is a good default for most editors

# ── Index ─────────────────────────────────────────────────────────────────────
# muninn indexes EVERYTHING under a repo root by default — including files that
# .gitignore normally hides (node_modules, build output, dotfiles) — because
# those are often worth searching. Only `.git/`, binary files, and files larger
# than 10 MiB are skipped automatically. Add glob patterns here (relative to the
# repo root) to opt specific paths back out. Leave empty to index everything.

[index]
exclude = []   # e.g. ["target/", "dist/", "**/*.min.js"]

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
#[serde(deny_unknown_fields)]
pub struct RepoConfig {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub repo_name: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub database: Option<DatabaseConfig>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub embeddings: Option<EmbeddingConfig>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub watcher: Option<WatcherConfig>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub index: Option<IndexConfig>,
}

impl RepoConfig {
    pub const FILE_NAME: &'static str = ".muninn.toml";

    /// Parse a RepoConfig from a TOML string (e.g. read from a temp file).
    /// Returns an error with a descriptive message on unknown fields or bad syntax.
    pub fn from_toml_str(content: &str) -> anyhow::Result<Self> {
        toml::from_str(content).map_err(|e| anyhow::anyhow!("{}", e))
    }

    /// Load .muninn.toml from a repo root. Returns empty config if file absent.
    pub fn load(repo_root: &std::path::Path) -> anyhow::Result<Self> {
        let path = repo_root.join(Self::FILE_NAME);
        if !path.exists() {
            return Ok(Self::default());
        }
        let content = std::fs::read_to_string(&path)?;
        toml::from_str(&content).map_err(|e| anyhow::anyhow!("{}: {}", path.display(), e))
    }

    /// Validate semantic constraints on a parsed RepoConfig.
    /// Call after `load()` to surface configuration errors early.
    pub fn validate(&self) -> anyhow::Result<()> {
        if let Some(ref emb) = self.embeddings {
            anyhow::ensure!(
                emb.batch_size > 0,
                "[embeddings] batch_size must be greater than 0"
            );
            if emb.backend != EmbeddingBackend::Local {
                anyhow::ensure!(
                    emb.model
                        .as_deref()
                        .map(|s| !s.trim().is_empty())
                        .unwrap_or(false),
                    "[embeddings] model is required for voyage and openai backends"
                );
            }
        }
        if let Some(ref w) = self.watcher {
            anyhow::ensure!(
                w.debounce_ms > 0,
                "[watcher] debounce_ms must be greater than 0"
            );
        }
        Ok(())
    }

    /// Return the template content for a new .muninn.toml (all sections commented out).
    pub fn template_content(dir_name: &str) -> String {
        format!(
            "# .muninn.toml — per-repo config for {dir_name}\n\
                 #\n\
                 # The presence of this file marks the directory as a muninn repo root.\n\
                 # An empty file (everything commented out) is perfectly valid — all settings\n\
                 # are inherited from ~/.config/muninn/config.toml.\n\
                 #\n\
                 # Uncomment and edit only the sections you need to override.\n\
                 # After editing, run:  muninn add <path/to/this/repo>\n\
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
                 # (run `muninn remove <path>` then `muninn add <path>`).\n\
                 # backend    = \"voyage\"   # voyage | openai | local\n\
                 # model      = \"voyage-code-3\"\n\
                 # api_key    = \"pa-...\"\n\
                 # cache_dir  = \"/path/to/cache\"   # local-only\n\
                 # batch_size = 64\n\
                 \n\
                 # [watcher]\n\
                 # Override the file-change debounce for this repo.\n\
                 # Increase if you see excessive re-indexing during large rebases.\n\
                 # debounce_ms = 300\n\
                 \n\
                 # [index]\n\
                 # muninn indexes everything under the repo root by default (including\n\
                 # gitignored files like node_modules). Add globs (relative to the repo\n\
                 # root) to exclude specific paths. `.git/`, binaries, and files over\n\
                 # 10 MiB are always skipped.\n\
                 # exclude = [\"target/\", \"dist/\", \"**/*.min.js\"]\n",
            dir_name = dir_name
        )
    }

    /// Create a .muninn.toml template in repo_root (does nothing if already exists).
    /// Returns the path to the file.
    pub fn create_template(
        repo_root: &std::path::Path,
        dir_name: &str,
    ) -> anyhow::Result<std::path::PathBuf> {
        let path = repo_root.join(Self::FILE_NAME);
        if !path.exists() {
            std::fs::write(&path, Self::template_content(dir_name))?;
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
    /// Resolved exclude globs: shipped defaults ++ global ++ repo (last-match-wins).
    pub exclude: Vec<String>,
    /// Resolved vendor globs: shipped defaults ++ global ++ repo (last-match-wins).
    pub vendor: Vec<String>,
    pub repo_name: String,
}

/// Resolve one glob axis by layering shipped defaults, the global config list,
/// and the per-repo list IN THAT ORDER. The engine (`build_excludes`) then matches
/// a path against the concatenated list last-match-wins, with `!pattern` negating
/// a prior match — so a repo writes only its delta and inherits the rest, and can
/// `!`-subtract a default. Spec: Muninn.Config.layerAxis (supersedes the earlier
/// whole-list-replace merge).
fn layer_axis(defaults: &[&str], global: &[String], repo: Option<&[String]>) -> Vec<String> {
    let mut out: Vec<String> = defaults.iter().map(|s| s.to_string()).collect();
    out.extend(global.iter().cloned());
    if let Some(r) = repo {
        out.extend(r.iter().cloned());
    }
    out
}

impl EffectiveConfig {
    /// Merge global defaults with per-repo overrides.
    /// `dir_name` is the fallback repo name when [repo].name is absent.
    pub fn merge(global: &GlobalConfig, repo: &RepoConfig, dir_name: &str) -> Self {
        Self {
            database: repo
                .database
                .clone()
                .unwrap_or_else(|| global.database.clone()),
            embeddings: repo
                .embeddings
                .clone()
                .unwrap_or_else(|| global.embeddings.clone()),
            watcher: repo
                .watcher
                .clone()
                .unwrap_or_else(|| global.watcher.clone()),
            exclude: layer_axis(
                EXCLUDE_DEFAULTS,
                &global.index.exclude,
                repo.index.as_ref().map(|i| i.exclude.as_slice()),
            ),
            vendor: layer_axis(
                VENDOR_DEFAULTS,
                &global.index.vendor,
                repo.index.as_ref().map(|i| i.vendor.as_slice()),
            ),
            repo_name: repo
                .repo_name
                .clone()
                .unwrap_or_else(|| dir_name.to_string()),
        }
    }
}

// ── TOML key editing (config get/set/unset) ─────────────────────────────────
// Comment- and formatting-preserving edits to a TOML config file, keyed by a
// dotted path (e.g. "database.port", "index.exclude"). Pure content→content so
// the caller can validate the result (by typed parse) before writing. Used by
// the unified `muninn config get/set/unset` for both the global config and any
// per-repo `.muninn.toml`.

/// Set a dotted `key` to a TOML value literal (`value` is parsed as TOML, so
/// `7432`, `"voyage"`, `["a","b"]`, `true` all work). Intermediate tables are
/// created as needed. Returns the new file content.
pub fn toml_set(content: &str, key: &str, value: &str) -> anyhow::Result<String> {
    use toml_edit::{DocumentMut, Item, Table, Value};
    let mut doc: DocumentMut = content
        .parse()
        .map_err(|e| anyhow::anyhow!("config is not valid TOML: {}", e))?;
    // Parse the value as a TOML literal (number / bool / array / quoted string);
    // fall back to a bare string when it doesn't parse, so `backend=local` and
    // `model=voyage-code-3` work without shell-quoting the inner quotes. Type
    // mismatches are caught by the caller's typed validation after the edit.
    let val: Value = value.parse().unwrap_or_else(|_| Value::from(value));
    let segs: Vec<&str> = key.split('.').collect();
    anyhow::ensure!(
        !segs.iter().any(|s| s.is_empty()),
        "invalid config key `{}`",
        key
    );
    let (last, parents) = segs.split_last().unwrap();
    let mut tbl: &mut Table = doc.as_table_mut();
    for p in parents {
        let entry = tbl.entry(p).or_insert(Item::Table(Table::new()));
        tbl = entry
            .as_table_mut()
            .ok_or_else(|| anyhow::anyhow!("config key `{}`: `{}` is not a table", key, p))?;
    }
    tbl.insert(last, Item::Value(val));
    Ok(doc.to_string())
}

/// Remove a dotted `key`. Absent keys are a no-op. Returns the new file content.
pub fn toml_unset(content: &str, key: &str) -> anyhow::Result<String> {
    use toml_edit::DocumentMut;
    let mut doc: DocumentMut = content
        .parse()
        .map_err(|e| anyhow::anyhow!("config is not valid TOML: {}", e))?;
    let segs: Vec<&str> = key.split('.').collect();
    let (last, parents) = segs.split_last().unwrap();
    let mut tbl = doc.as_table_mut();
    for p in parents {
        match tbl.get_mut(p).and_then(|i| i.as_table_mut()) {
            Some(t) => tbl = t,
            None => return Ok(doc.to_string()),
        }
    }
    tbl.remove(last);
    Ok(doc.to_string())
}

/// Read a dotted `key`, returning its rendered TOML value, or None if absent.
pub fn toml_get(content: &str, key: &str) -> anyhow::Result<Option<String>> {
    use toml_edit::DocumentMut;
    let doc: DocumentMut = content
        .parse()
        .map_err(|e| anyhow::anyhow!("config is not valid TOML: {}", e))?;
    // Navigate with `.get()` (not `&item[seg]`, whose Index impl panics on a
    // missing or non-table segment). Any absent / through-scalar segment → None.
    let mut item = doc.as_item();
    for seg in key.split('.') {
        match item.as_table_like().and_then(|t| t.get(seg)) {
            Some(i) => item = i,
            None => return Ok(None),
        }
    }
    if item.is_none() {
        return Ok(None);
    }
    // Render just the value — never the surrounding decor (a trailing `# comment`
    // on the source line lives in the value's suffix decor, and `to_string()`
    // would include it). Strings come out unquoted for clean scripting.
    let rendered = match item.as_value() {
        Some(toml_edit::Value::String(s)) => s.value().clone(),
        Some(v) => {
            let mut v = v.clone();
            v.decor_mut().set_prefix("");
            v.decor_mut().set_suffix("");
            v.to_string().trim().to_string()
        }
        None => item.to_string().trim().to_string(),
    };
    Ok(Some(rendered))
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
    fn toml_get_missing_and_nested_does_not_panic() {
        // Verifier: does chained Item indexing panic on missing / through-scalar keys?
        assert_eq!(toml_get("a = 1\n", "a.b").unwrap(), None);
        assert_eq!(toml_get("", "x.y").unwrap(), None);
        assert_eq!(toml_get("[t]\nk = 1\n", "missing").unwrap(), None);
        assert_eq!(
            toml_get("[t]\nk = 1\n", "t.k").unwrap(),
            Some("1".to_string())
        );
        assert_eq!(toml_get("[t]\nk = 1\n", "t.k.deeper").unwrap(), None);
    }

    #[test]
    fn toml_set_then_get_roundtrip_and_string_fallback() {
        let s = toml_set("", "embeddings.backend", "local").unwrap();
        // strings render unquoted, no decor
        assert_eq!(
            toml_get(&s, "embeddings.backend").unwrap(),
            Some("local".to_string())
        );
        let s2 = toml_set(&s, "database.port", "7432").unwrap();
        assert_eq!(
            toml_get(&s2, "database.port").unwrap(),
            Some("7432".to_string())
        );
    }

    #[test]
    fn toml_get_strips_trailing_comment_and_quotes() {
        let content = "[embeddings]\nbackend = \"local\"           # voyage | openai | local\n";
        assert_eq!(
            toml_get(content, "embeddings.backend").unwrap(),
            Some("local".to_string())
        );
        let arr = "[index]\nexclude = [\"a\",\"b\"]  # globs\n";
        assert_eq!(
            toml_get(arr, "index.exclude").unwrap(),
            Some("[\"a\",\"b\"]".to_string())
        );
    }

    #[test]
    fn config_default_embedding_is_voyage() {
        let cfg = EmbeddingConfig::default();
        assert_eq!(cfg.backend, EmbeddingBackend::Voyage);
        assert_eq!(cfg.model, Some("voyage-code-3".to_string()));
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
                model: None,
                api_key: None,
                cache_dir: None,
                batch_size: 32,
            }),
            watcher: None,
            index: None,
        };
        let eff = EffectiveConfig::merge(&global, &repo, "proj");
        assert_eq!(eff.embeddings.backend, EmbeddingBackend::Local);
        assert_eq!(eff.embeddings.batch_size, 32);
        assert_eq!(eff.database.port, 5432);
    }

    #[test]
    fn effective_config_repo_name_override() {
        let global = GlobalConfig::default();
        let repo = RepoConfig {
            repo_name: Some("custom-name".to_string()),
            ..Default::default()
        };
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

    // ── exclude/vendor merge semantics (spec: Muninn.Config.layerAxis) ──
    // Resolution layers shipped defaults ++ global ++ repo, IN THAT ORDER; the
    // engine then matches a path last-match-wins with `!` negation. So the merged
    // list always starts with the shipped defaults, then global, then repo.

    fn global_with_exclude(globs: &[&str]) -> GlobalConfig {
        GlobalConfig {
            index: IndexConfig {
                exclude: globs.iter().map(|s| s.to_string()).collect(),
                vendor: vec![],
            },
            ..Default::default()
        }
    }

    fn repo_with_exclude(globs: Option<&[&str]>) -> RepoConfig {
        RepoConfig {
            index: globs.map(|gs| IndexConfig {
                exclude: gs.iter().map(|s| s.to_string()).collect(),
                vendor: vec![],
            }),
            ..Default::default()
        }
    }

    #[test]
    fn exclude_layers_defaults_then_global_then_repo() {
        let global = global_with_exclude(&["g_only/"]);
        let repo = repo_with_exclude(Some(&["r_only/"]));
        let eff = EffectiveConfig::merge(&global, &repo, "proj");
        // shipped defaults present, then global, then repo — in order, no replace.
        assert!(eff.exclude.iter().any(|g| g == ".git/")); // a shipped default
        assert!(eff.exclude.iter().any(|g| g == "g_only/"));
        assert!(eff.exclude.iter().any(|g| g == "r_only/"));
        // order: the last two entries are global then repo.
        let n = eff.exclude.len();
        assert_eq!(eff.exclude[n - 2], "g_only/");
        assert_eq!(eff.exclude[n - 1], "r_only/");
    }

    #[test]
    fn exclude_no_repo_index_inherits_defaults_plus_global() {
        let global = global_with_exclude(&["g_only/"]);
        let repo = repo_with_exclude(None);
        let eff = EffectiveConfig::merge(&global, &repo, "proj");
        assert!(eff.exclude.iter().any(|g| g == ".git/"));
        assert!(eff.exclude.iter().any(|g| g == "g_only/"));
        assert!(!eff.exclude.iter().any(|g| g == "r_only/"));
    }

    #[test]
    fn vendor_layers_defaults_plus_repo() {
        // vendor resolves the same way; defaults include node_modules.
        let global = GlobalConfig::default();
        let repo = RepoConfig {
            index: Some(IndexConfig {
                exclude: vec![],
                vendor: vec!["third_party/".to_string()],
            }),
            ..Default::default()
        };
        let eff = EffectiveConfig::merge(&global, &repo, "proj");
        assert!(eff.vendor.iter().any(|g| g == "**/node_modules/**")); // a default
        assert!(eff.vendor.iter().any(|g| g == "third_party/")); // repo addition
        assert_eq!(eff.vendor.last().unwrap(), "third_party/"); // repo is last
    }

    use quickcheck::quickcheck;

    quickcheck! {
        // The merged list is exactly defaults ++ global ++ repo, in that order.
        fn prop_exclude_merge_is_layered(global_globs: Vec<String>,
                                         repo_globs: Option<Vec<String>>) -> bool {
            let global = GlobalConfig {
                index: IndexConfig { exclude: global_globs.clone(), vendor: vec![] },
                ..Default::default()
            };
            let repo = RepoConfig {
                index: repo_globs.clone().map(|g| IndexConfig { exclude: g, vendor: vec![] }),
                ..Default::default()
            };
            let eff = EffectiveConfig::merge(&global, &repo, "proj");
            let mut expected: Vec<String> =
                EXCLUDE_DEFAULTS.iter().map(|s| s.to_string()).collect();
            expected.extend(global_globs);
            expected.extend(repo_globs.unwrap_or_default());
            eff.exclude == expected
        }
    }

    // ── config TOML parse / merge round-trip ──────────────────────────────────

    #[test]
    fn repo_config_exclude_parses_from_toml() {
        let toml = "[index]\nexclude = [\"target/\", \"**/*.min.js\"]\n";
        let rc = RepoConfig::from_toml_str(toml).unwrap();
        let idx = rc.index.expect("index section present");
        assert_eq!(idx.exclude, vec!["target/", "**/*.min.js"]);
    }

    #[test]
    fn exclude_survives_toml_set_get_round_trip() {
        let base = "[index]\nexclude = []\n";
        let set = toml_set(base, "index.exclude", "[\"a/\", \"b/\"]").unwrap();
        assert_eq!(
            toml_get(&set, "index.exclude").unwrap(),
            Some("[\"a/\", \"b/\"]".to_string())
        );
        // and the typed parse agrees with the textual round-trip
        let rc = RepoConfig::from_toml_str(&set).unwrap();
        assert_eq!(rc.index.unwrap().exclude, vec!["a/", "b/"]);
    }

    #[test]
    fn repo_config_rejects_unknown_field() {
        // deny_unknown_fields guards against silent typos in a hand-edited file.
        let toml = "[index]\nexcludes = [\"oops\"]\n"; // note the typo: excludes
        assert!(RepoConfig::from_toml_str(toml).is_err());
    }

    quickcheck! {
        // Any IndexConfig round-trips through TOML serialize→parse unchanged,
        // for glob strings that survive TOML quoting (no control chars / quotes).
        fn prop_index_config_toml_round_trip(globs: Vec<String>) -> quickcheck::TestResult {
            let safe: Vec<String> = globs
                .into_iter()
                .filter(|g| !g.contains(['"', '\\', '\n', '\r', '\t', '#']))
                .collect();
            let rc = RepoConfig {
                index: Some(IndexConfig {
                    exclude: safe.clone(),
                    vendor: vec![],
                }),
                ..Default::default()
            };
            let toml = match toml::to_string(&rc) {
                Ok(t) => t,
                Err(_) => return quickcheck::TestResult::discard(),
            };
            let back = match RepoConfig::from_toml_str(&toml) {
                Ok(b) => b,
                Err(_) => return quickcheck::TestResult::discard(),
            };
            let got = back.index.map(|i| i.exclude).unwrap_or_default();
            quickcheck::TestResult::from_bool(got == safe)
        }
    }
}
