use serde::{Deserialize, Serialize};
use uuid::Uuid;

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(rename_all = "lowercase")]
pub enum EmbeddingBackend {
    Voyage,
    OpenAI,
    Local,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DatabaseConfig {
    pub dsn: String,
}

impl Default for DatabaseConfig {
    fn default() -> Self {
        Self { dsn: "postgresql://localhost/muninn".to_string() }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EmbeddingConfig {
    pub backend: EmbeddingBackend,
    pub api_key: Option<String>,
    pub model: String,
    pub batch_size: usize,
}

impl Default for EmbeddingConfig {
    fn default() -> Self {
        Self {
            backend: EmbeddingBackend::Voyage,
            api_key: None,
            model: "voyage-code-3".to_string(),
            batch_size: 64,
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WatcherConfig {
    pub debounce_ms: u64,
}

impl Default for WatcherConfig {
    fn default() -> Self {
        Self { debounce_ms: 300 }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RepoEntry {
    pub id: Uuid,
    pub path: String,
    pub name: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct AppConfig {
    pub database: DatabaseConfig,
    pub embeddings: EmbeddingConfig,
    pub watcher: WatcherConfig,
    #[serde(default)]
    pub repos: Vec<RepoEntry>,
}

impl AppConfig {
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
}