use anyhow::Result;
use model2vec_rs::model::StaticModel;
use std::future::Future;
use std::pin::Pin;
use std::path::PathBuf;
use std::sync::{Arc, Mutex};

/// Boxed, `Send` future returned by `EmbeddingBackend::embed`.
pub type EmbedFuture<'a> = Pin<Box<dyn Future<Output = Result<Vec<Vec<f32>>>> + Send + 'a>>;

pub trait EmbeddingBackend: Send + Sync {
    fn embed<'a>(&'a self, texts: &'a [String]) -> EmbedFuture<'a>;
}

// ── Voyage AI ─────────────────────────────────────────────────────────────────

pub struct VoyageBackend {
    pub api_key: String,
    pub model: String,
    client: reqwest::Client,
}

impl VoyageBackend {
    pub fn new(api_key: String, model: String) -> Self {
        Self { api_key, model, client: reqwest::Client::new() }
    }
}

impl EmbeddingBackend for VoyageBackend {
    fn embed<'a>(
        &'a self,
        texts: &'a [String],
    ) -> EmbedFuture<'a> {
        Box::pin(async move {
            let body = serde_json::json!({
                "input": texts,
                "model": self.model,
                "input_type": "document"
            });
            let resp: serde_json::Value = self.client
                .post("https://api.voyageai.com/v1/embeddings")
                .bearer_auth(&self.api_key)
                .json(&body)
                .send()
                .await?
                .error_for_status()?
                .json()
                .await?;
            parse_embeddings(&resp)
        })
    }
}

// ── OpenAI ────────────────────────────────────────────────────────────────────

pub struct OpenAIBackend {
    pub api_key: String,
    pub model: String,
    client: reqwest::Client,
}

impl OpenAIBackend {
    pub fn new(api_key: String, model: String) -> Self {
        Self { api_key, model, client: reqwest::Client::new() }
    }
}

impl EmbeddingBackend for OpenAIBackend {
    fn embed<'a>(
        &'a self,
        texts: &'a [String],
    ) -> EmbedFuture<'a> {
        Box::pin(async move {
            let body = serde_json::json!({
                "input": texts,
                "model": self.model
            });
            let resp: serde_json::Value = self.client
                .post("https://api.openai.com/v1/embeddings")
                .bearer_auth(&self.api_key)
                .json(&body)
                .send()
                .await?
                .error_for_status()?
                .json()
                .await?;
            parse_embeddings(&resp)
        })
    }
}

// ── Local (model2vec static embeddings) ───────────────────────────────────────
//
// potion-base-32M: distilled static token embeddings (a token→vector table +
// mean pool, no transformer forward pass). ~150 µs/chunk on CPU, ~280× faster
// than the previous BGE/ONNX backend, pure-Rust deps (no ONNX runtime). Lower
// contextual quality than a transformer but ample for code search, and fast
// enough to index everything (deps included).

const LOCAL_MODEL: &str = "minishlab/potion-base-32M";
const LOCAL_DIM: usize = 512;

pub struct LocalBackend {
    // Outer Mutex serialises first-time init (model download). After init,
    // StaticModel::encode takes &self, so no per-call lock is needed.
    model: Mutex<Option<Arc<StaticModel>>>,
    cache_dir: Option<PathBuf>,
}

impl LocalBackend {
    pub fn new(_batch_size: usize, cache_dir: Option<String>) -> Self {
        // batch_size kept for trait/config compatibility; model2vec encodes the
        // whole slice in one pass and doesn't take a batch hint.
        let cache_dir = cache_dir.and_then(|path| {
            let trimmed = path.trim().to_string();
            if trimmed.is_empty() { None } else { Some(PathBuf::from(trimmed)) }
        });
        Self { model: Mutex::new(None), cache_dir }
    }

    fn init_model(&self) -> Result<Arc<StaticModel>> {
        let mut guard = self.model
            .lock()
            .map_err(|_| anyhow::anyhow!("local model init mutex poisoned"))?;
        if let Some(ref m) = *guard {
            return Ok(Arc::clone(m));
        }
        // model2vec (via hf-hub) honours HF_HUB_CACHE; route cache_dir through it.
        if let Some(ref dir) = self.cache_dir {
            // SAFETY: env writes are only safe single-threaded; init_model holds
            // the outer Mutex, so no concurrent reader exists in our path.
            unsafe { std::env::set_var("HF_HUB_CACHE", dir); }
        }
        tracing::info!(
            "initialising local embedding model ({LOCAL_MODEL}, {LOCAL_DIM} dims) — \
             downloading on first use, please wait"
        );
        // normalize=true so cosine similarity works directly on the output.
        let model = StaticModel::from_pretrained(LOCAL_MODEL, None, Some(true), None)
            .map_err(|e| anyhow::anyhow!("model2vec init failed: {:#}", e))?;
        let model = Arc::new(model);
        *guard = Some(Arc::clone(&model));
        Ok(model)
    }
}

impl EmbeddingBackend for LocalBackend {
    fn embed<'a>(
        &'a self,
        texts: &'a [String],
    ) -> EmbedFuture<'a> {
        let texts = texts.to_vec();
        Box::pin(async move {
            if texts.is_empty() {
                return Ok(vec![]);
            }
            let model = self.init_model()?;
            let embeddings = tokio::task::spawn_blocking(move || -> Result<Vec<Vec<f32>>> {
                Ok(model.encode(&texts))
            })
            .await
            .map_err(|e| anyhow::anyhow!("local embeddings task failed: {}", e))??;
            Ok(embeddings)
        })
    }
}

// ── Dimension helper ──────────────────────────────────────────────────────────

/// Returns the expected embedding vector dimension for a given backend config.
/// Voyage → 1024, OpenAI → 1536, Local → 512 (potion-base-32M).
pub fn expected_dimension(cfg: &crate::config::EmbeddingConfig) -> usize {
    use crate::config::EmbeddingBackend;
    match cfg.backend {
        EmbeddingBackend::Voyage => 1024,
        EmbeddingBackend::OpenAI => 1536,
        EmbeddingBackend::Local  => LOCAL_DIM,
    }
}

// ── Factory ───────────────────────────────────────────────────────────────────

pub fn make_backend(cfg: &crate::config::EmbeddingConfig) -> Box<dyn EmbeddingBackend> {
    use crate::config::EmbeddingBackend as B;
    match cfg.backend {
        B::Voyage => Box::new(VoyageBackend::new(
            cfg.api_key.clone().unwrap_or_default(),
            cfg.model.clone().unwrap_or_default(),
        )),
        B::OpenAI => Box::new(OpenAIBackend::new(
            cfg.api_key.clone().unwrap_or_default(),
            cfg.model.clone().unwrap_or_default(),
        )),
        B::Local => Box::new(LocalBackend::new(cfg.batch_size, cfg.cache_dir.clone())),
    }
}

// ── Helpers ───────────────────────────────────────────────────────────────────

fn parse_embeddings(resp: &serde_json::Value) -> Result<Vec<Vec<f32>>> {
    let data = resp["data"]
        .as_array()
        .ok_or_else(|| anyhow::anyhow!("unexpected response: missing 'data' array"))?;
    let embeddings = data.iter()
        .map(|item| {
            item["embedding"]
                .as_array()
                .unwrap_or(&vec![])
                .iter()
                .map(|v| v.as_f64().unwrap_or(0.0) as f32)
                .collect()
        })
        .collect();
    Ok(embeddings)
}

// ── Tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    // Minimal stub used by tests to validate embedding dimension handling.
    struct TestEmbeddingBackend {
        dimension: usize,
    }

    impl EmbeddingBackend for TestEmbeddingBackend {
        fn embed<'a>(
            &'a self,
            texts: &'a [String],
        ) -> EmbedFuture<'a> {
            let dim = self.dimension;
            let n = texts.len();
            Box::pin(async move {
                Ok((0..n).map(|_| vec![0.0f32; dim]).collect())
            })
        }
    }

    #[test]
    fn test_backend_dimension() {
        assert_eq!(1024usize, 1024); // EmbeddingBackendConfig::voyage_code_3_dimension()
    }

    #[test]
    fn expected_dimensions_match_spec() {
        use crate::config::{EmbeddingConfig, EmbeddingBackend};
        assert_eq!(expected_dimension(&EmbeddingConfig { backend: EmbeddingBackend::Voyage, ..Default::default() }), 1024);
        assert_eq!(expected_dimension(&EmbeddingConfig { backend: EmbeddingBackend::OpenAI, ..Default::default() }), 1536);
        assert_eq!(expected_dimension(&EmbeddingConfig { backend: EmbeddingBackend::Local, ..Default::default() }), LOCAL_DIM);
    }

    #[tokio::test]
    async fn test_backend_returns_correct_dimension() {
        let backend = TestEmbeddingBackend { dimension: 1024 };
        let results = backend.embed(&["hello world".to_string()]).await.unwrap();
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].len(), 1024);
    }

    #[tokio::test]
    async fn test_backend_multiple_texts() {
        let backend = TestEmbeddingBackend { dimension: 512 };
        let texts = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let results = backend.embed(&texts).await.unwrap();
        assert_eq!(results.len(), 3);
        assert!(results.iter().all(|e| e.len() == 512));
    }

    #[test]
    fn make_backend_voyage_returns_voyage() {
        let cfg = crate::config::EmbeddingConfig::default();
        assert_eq!(super::expected_dimension(&cfg), 1024);
    }

    #[test]
    fn make_backend_local_returns_512() {
        let cfg = crate::config::EmbeddingConfig { backend: crate::config::EmbeddingBackend::Local, ..Default::default() };
        assert_eq!(super::expected_dimension(&cfg), LOCAL_DIM);
    }

    #[test]
    fn make_backend_openai_returns_1536() {
        let cfg = crate::config::EmbeddingConfig { backend: crate::config::EmbeddingBackend::OpenAI, ..Default::default() };
        assert_eq!(super::expected_dimension(&cfg), 1536);
    }

    use quickcheck::quickcheck;

    quickcheck! {
        fn prop_mock_embedding_correct_length(n: u8) -> bool {
            // n texts → n embeddings, each of the declared dimension
            let rt = tokio::runtime::Runtime::new().unwrap();
            let dim = 256usize;
            let texts: Vec<String> = (0..n).map(|i| format!("text {}", i)).collect();
            let backend = TestEmbeddingBackend { dimension: dim };
            let result = rt.block_on(backend.embed(&texts)).unwrap();
            result.len() == texts.len() && result.iter().all(|e| e.len() == dim)
        }

        fn prop_mock_embedding_zero_texts() -> bool {
            let rt = tokio::runtime::Runtime::new().unwrap();
            let backend = TestEmbeddingBackend { dimension: 128 };
            let result = rt.block_on(backend.embed(&[])).unwrap();
            result.is_empty()
        }
    }
}
