use crate::config::{EmbeddingBackend, GlobalConfig, EXCLUDE_DEFAULTS, VENDOR_DEFAULTS};
use ignore::gitignore::{Gitignore, GitignoreBuilder};
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use std::{fmt, path::Path};
use uuid::Uuid;

/// Capture only nonsecret family settings. Later global edits cannot alter it.
pub fn policy_from_global(name: String, global: &GlobalConfig) -> Result<Policy> {
    let backend = match global.embeddings.backend {
        EmbeddingBackend::Voyage => Backend::Voyage,
        EmbeddingBackend::OpenAI => Backend::OpenAI,
        EmbeddingBackend::Local => Backend::Local,
    };
    let policy = Policy {
        name,
        index: Rules {
            exclude: Vec::new(),
            vendor: Vec::new(),
        },
        watcher: Watcher {
            debounce_ms: global.watcher.debounce_ms,
        },
        embeddings: Embeddings {
            backend,
            model: if backend == Backend::Local {
                None
            } else {
                global.embeddings.model.clone()
            },
            batch_size: global.embeddings.batch_size.try_into().map_err(|_| {
                PolicyError::new(
                    "invalid_global_defaults",
                    "Global embedding batch size exceeds the supported family range",
                )
            })?,
        },
    };
    policy.validate().map_err(|_| PolicyError::new("invalid_global_defaults", "Global embedding or watcher defaults are not supported for repository families; check the supported model and numeric ranges"))?;
    Ok(policy)
}

/// Shipped rules precede the global additions, captured once for a new family.
pub fn defaults_from_global(global: &GlobalConfig) -> Result<Defaults> {
    use sha2::{Digest, Sha256};
    let mut defaults = Defaults::shipped();
    defaults
        .index
        .exclude
        .extend(global.index.exclude.iter().cloned());
    defaults
        .index
        .vendor
        .extend(global.index.vendor.iter().cloned());
    if !global.index.exclude.is_empty() || !global.index.vendor.is_empty() {
        let bytes = serde_json::to_vec(&defaults.index).expect("serializable rule snapshot");
        defaults.revision = format!("global-snapshot-v1-{:x}", Sha256::digest(bytes));
    }
    defaults.validate().map_err(|_| {
        PolicyError::new(
            "invalid_global_defaults",
            "Global file-selection rules contain an invalid pattern",
        )
    })?;
    Ok(defaults)
}

pub const MAX_REVISION: u64 = 9_007_199_254_740_991;
pub type Result<T> = std::result::Result<T, PolicyError>;

#[derive(Debug, Clone, Serialize, PartialEq)]
pub struct PolicyError {
    pub code: &'static str,
    pub message: &'static str,
    pub details: Value,
}
impl PolicyError {
    pub(crate) fn new(code: &'static str, message: &'static str) -> Self {
        Self {
            code,
            message,
            details: json!({}),
        }
    }
    fn invalid(field: &str, index: Option<usize>, reason: &'static str) -> Self {
        Self {
            code: "invalid_policy",
            message: reason,
            details: json!({"field":field,"index":index}),
        }
    }
}
impl fmt::Display for PolicyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.code, self.message)
    }
}
impl std::error::Error for PolicyError {}
impl From<tokio_postgres::Error> for PolicyError {
    fn from(error: tokio_postgres::Error) -> Self {
        Self {
            code: "database_error",
            message: "policy database operation failed",
            details: json!({"sqlstate":error.code().map(|c|c.code())}),
        }
    }
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
pub enum Backend {
    Voyage,
    OpenAI,
    Local,
}
impl Backend {
    pub fn dimension(self) -> u32 {
        match self {
            Self::Voyage => 1024,
            Self::OpenAI => 1536,
            Self::Local => 512,
        }
    }
    pub fn model_identity(self) -> &'static str {
        match self {
            Self::Voyage => "voyage-code-3",
            Self::OpenAI => "text-embedding-3-small",
            Self::Local => "minishlab/potion-base-32M",
        }
    }
}
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct Rules {
    pub exclude: Vec<String>,
    pub vendor: Vec<String>,
}
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct Watcher {
    pub debounce_ms: u64,
}
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct Embeddings {
    pub backend: Backend,
    // Required on the wire, even when its value is null for local.
    #[serde(deserialize_with = "Option::<String>::deserialize")]
    pub model: Option<String>,
    pub batch_size: u32,
}
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct Policy {
    pub name: String,
    pub index: Rules,
    pub watcher: Watcher,
    pub embeddings: Embeddings,
}
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct Defaults {
    pub format_version: u32,
    pub revision: String,
    pub index: Rules,
}
impl Defaults {
    pub fn shipped() -> Self {
        Self {
            format_version: 1,
            revision: "shipped-v1".into(),
            index: Rules {
                exclude: EXCLUDE_DEFAULTS.iter().map(|s| s.to_string()).collect(),
                vendor: VENDOR_DEFAULTS.iter().map(|s| s.to_string()).collect(),
            },
        }
    }
    pub fn validate(&self) -> Result<()> {
        if self.format_version != 1
            || self.revision.trim().is_empty()
            || self.revision.contains('\0')
        {
            return Err(PolicyError::invalid(
                "defaults",
                None,
                "invalid defaults identity or format",
            ));
        }
        compile_axis(
            Path::new("."),
            &self.index.exclude,
            "defaults.index.exclude",
        )?;
        compile_axis(Path::new("."), &self.index.vendor, "defaults.index.vendor")?;
        Ok(())
    }
}
impl Policy {
    pub fn shipped(name: String) -> Self {
        Self {
            name,
            index: Rules {
                exclude: vec![],
                vendor: vec![],
            },
            watcher: Watcher { debounce_ms: 300 },
            embeddings: Embeddings {
                backend: Backend::Voyage,
                model: Some("voyage-code-3".into()),
                batch_size: 64,
            },
        }
    }
    pub fn validate(&self) -> Result<()> {
        if self.name.trim().is_empty() || self.name.contains('\0') {
            return Err(PolicyError::invalid(
                "name",
                None,
                "name must not be empty or contain NUL",
            ));
        }
        if self.watcher.debounce_ms > MAX_REVISION {
            return Err(PolicyError::invalid(
                "watcher.debounce_ms",
                None,
                "duration exceeds exact JSON integer range",
            ));
        }
        if self.embeddings.batch_size == 0 {
            return Err(PolicyError::invalid(
                "embeddings.batch_size",
                None,
                "batch size must be positive",
            ));
        }
        let valid_model = match self.embeddings.backend {
            Backend::Local => self.embeddings.model.is_none(),
            backend => self.embeddings.model.as_deref() == Some(backend.model_identity()),
        };
        if !valid_model {
            return Err(PolicyError::invalid(
                "embeddings.model",
                None,
                "model is not a supported adapter selection",
            ));
        }
        compile_axis(Path::new("."), &self.index.exclude, "index.exclude")?;
        compile_axis(Path::new("."), &self.index.vendor, "index.vendor")?;
        Ok(())
    }
    pub fn effective(&self, defaults: &Defaults) -> Self {
        let mut policy = self.clone();
        policy.index.exclude = defaults
            .index
            .exclude
            .iter()
            .chain(&self.index.exclude)
            .cloned()
            .collect();
        policy.index.vendor = defaults
            .index
            .vendor
            .iter()
            .chain(&self.index.vendor)
            .cloned()
            .collect();
        policy
    }
    pub fn impact(&self, other: &Self) -> Impact {
        if self.embeddings.backend != other.embeddings.backend
            || self.embeddings.model != other.embeddings.model
        {
            Impact::EmbeddingProfile
        } else if self.index != other.index {
            Impact::Selection
        } else if self.watcher != other.watcher
            || self.embeddings.batch_size != other.embeddings.batch_size
        {
            Impact::Runtime
        } else {
            Impact::Display
        }
    }
}

pub(crate) fn compile_axis(root: &Path, patterns: &[String], field: &str) -> Result<Gitignore> {
    let mut builder = GitignoreBuilder::new(root);
    builder.allow_unclosed_class(false);
    for (index, raw) in patterns.iter().enumerate() {
        let pattern = raw.trim();
        if pattern.is_empty() || pattern == "!" || pattern.contains('\0') {
            return Err(PolicyError::invalid(
                field,
                Some(index),
                "empty or invalid glob",
            ));
        }
        // The underlying gitignore engine has the required default-false fold.
        // Override adds an implicit ignore for unmatched files when any whitelist
        // exists; it is unsuitable for independent exclude/vendor axes.
        // Escape a leading #, which is a literal glob in the policy, not a comment.
        let entry = if pattern.starts_with('#') {
            format!("\\{pattern}")
        } else {
            pattern.to_owned()
        };
        builder
            .add_line(None, &entry)
            .map_err(|_| PolicyError::invalid(field, Some(index), "invalid glob syntax"))?;
    }
    builder
        .build()
        .map_err(|_| PolicyError::invalid(field, None, "invalid glob set"))
}
/// Shared strict compiler for stored-policy preflight, watcher and indexing.
pub struct CompiledRules {
    exclude: Gitignore,
    vendor: Gitignore,
}
impl CompiledRules {
    pub fn new(root: &Path, policy: &Policy, defaults: &Defaults) -> Result<Self> {
        policy.validate()?;
        defaults.validate()?;
        let effective = policy.effective(defaults);
        Ok(Self {
            exclude: compile_axis(root, &effective.index.exclude, "index.exclude")?,
            vendor: compile_axis(root, &effective.index.vendor, "index.vendor")?,
        })
    }
    pub fn classify(&self, relative: &Path) -> crate::pipeline::Decision {
        self.classify_entry(relative, false)
    }
    /// Directory-aware classification allows callers to prune before enumeration.
    pub fn classify_entry(&self, relative: &Path, is_dir: bool) -> crate::pipeline::Decision {
        use crate::pipeline::Decision;
        if relative.components().any(|c| c.as_os_str() == ".git")
            || axis_contains(&self.exclude, relative, is_dir)
        {
            Decision::Drop
        } else if axis_contains(&self.vendor, relative, is_dir) {
            Decision::Tier2
        } else {
            Decision::Tier1
        }
    }
}
fn axis_contains(axis: &Gitignore, relative: &Path, is_dir: bool) -> bool {
    axis.matched(relative, is_dir).is_ignore()
        || relative
            .ancestors()
            .skip(1)
            .take_while(|p| !p.as_os_str().is_empty())
            .any(|p| axis.matched(p, true).is_ignore())
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum Impact {
    Display,
    Runtime,
    Selection,
    EmbeddingProfile,
}

#[derive(Debug, Clone, Copy, Serialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum RuleOrigin {
    Defaults,
    Family,
}
#[derive(Debug, Clone, Serialize)]
pub struct ResolvedRule {
    pub pattern: String,
    pub origin: RuleOrigin,
    pub position: usize,
}
#[derive(Debug, Clone, Serialize)]
pub struct EffectiveRules {
    pub exclude: Vec<ResolvedRule>,
    pub vendor: Vec<ResolvedRule>,
}
impl EffectiveRules {
    pub fn resolve(policy: &Policy, defaults: &Defaults) -> Self {
        fn axis(defaults: &[String], family: &[String]) -> Vec<ResolvedRule> {
            defaults
                .iter()
                .map(|p| (p, RuleOrigin::Defaults))
                .chain(family.iter().map(|p| (p, RuleOrigin::Family)))
                .enumerate()
                .map(|(position, (pattern, origin))| ResolvedRule {
                    pattern: pattern.clone(),
                    origin,
                    position,
                })
                .collect()
        }
        Self {
            exclude: axis(&defaults.index.exclude, &policy.index.exclude),
            vendor: axis(&defaults.index.vendor, &policy.index.vendor),
        }
    }
}
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct InitialRequest {
    pub api_version: u32,
    pub policy: Policy,
}
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ApplyRequest {
    pub api_version: u32,
    pub expected_family_id: Uuid,
    pub expected_revision: u64,
    #[serde(default)]
    pub acknowledge_reindex: bool,
    pub policy: Policy,
}
fn parse<T: serde::de::DeserializeOwned>(input: &str) -> Result<T> {
    serde_json::from_str(input).map_err(|error| PolicyError {
        code: "invalid_request",
        message: "invalid JSON request shape",
        details: json!({"line":error.line(),"column":error.column()}),
    })
}
impl InitialRequest {
    pub fn parse(input: &str) -> Result<Self> {
        let request: Self = parse(input)?;
        request.validate()?;
        Ok(request)
    }
    pub fn validate(&self) -> Result<()> {
        version(self.api_version)?;
        self.policy.validate()
    }
}
impl ApplyRequest {
    pub fn parse(input: &str) -> Result<Self> {
        let request: Self = parse(input)?;
        request.validate()?;
        Ok(request)
    }
    pub fn validate(&self) -> Result<()> {
        version(self.api_version)?;
        if !(1..=MAX_REVISION).contains(&self.expected_revision) {
            return Err(PolicyError::new(
                "invalid_request",
                "expected revision outside supported range",
            ));
        }
        self.policy.validate()
    }
}
fn version(version: u32) -> Result<()> {
    if version != 1 {
        Err(PolicyError::new(
            "invalid_request",
            "unsupported API version",
        ))
    } else {
        Ok(())
    }
}
#[derive(Debug, Clone, Serialize)]
pub struct PolicyView {
    pub family_id: Uuid,
    pub revision: u64,
    pub defaults_revision: String,
    pub policy: Policy,
    pub effective_policy: Policy,
    pub effective_rules: EffectiveRules,
    pub defaults: Defaults,
    pub dimension: u32,
    pub indexing_enabled: bool,
    pub paused: bool,
    pub schema_state: &'static str,
    pub capabilities: Value,
}
#[derive(Debug, Clone, Serialize)]
pub struct ApplyResult {
    pub view: PolicyView,
    pub changed: bool,
    pub impact: Option<Impact>,
    pub reconciliation_needed: bool,
}
#[derive(Debug, Clone, Serialize)]
pub struct CandidateResult {
    pub family_id: Uuid,
    pub revision: u64,
    pub changed: bool,
    pub impact: Option<Impact>,
    pub requires_reindex_acknowledgement: bool,
    pub apply_supported: bool,
}

pub fn capabilities() -> Value {
    json!({
        "api_version":1,"max_revision":MAX_REVISION,"debounce_ms":{"min":0,"max":MAX_REVISION},
        "batch_size":{"min":1,"max":u32::MAX,"validation":"adapter integer range, not a remote service guarantee"},
        "embedding_selections":[{"backend":"voyage","model":"voyage-code-3","dimension":1024},{"backend":"openai","model":"text-embedding-3-small","dimension":1536},{"backend":"local","model":null,"model_identity":"minishlab/potion-base-32M","dimension":512}],
        "profile_changes":false,"defaults_adoption":false,
        "rules":{"ordering":"last_match_wins","negation":"!","exclude_precedes_vendor":true,"pruned_parent_requires_reinclusion":true},
        "policy_fields":["name","index.exclude","index.vendor","watcher.debounce_ms","embeddings.backend","embeddings.model","embeddings.batch_size"],
        "credential_availability":"not_checked_by_persistence_service"
    })
}
/// JSON envelope helpers do not print/log rejected requests or credentials.
pub fn success<T: Serialize>(data: T) -> Value {
    json!({"api_version":1,"ok":true,"data":data})
}
pub fn failure(error: &PolicyError) -> Value {
    json!({"api_version":1,"ok":false,"error":error})
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn global_creation_defaults_are_nonsecret_owned_snapshots() {
        let mut global = GlobalConfig::default();
        global.embeddings.backend = EmbeddingBackend::Local;
        global.embeddings.model = None;
        global.embeddings.batch_size = 16;
        global.embeddings.api_key = Some("private-global-key".into());
        global.watcher.debounce_ms = 450;
        global.index.exclude = vec!["generated/".into()];
        global.index.vendor = vec!["third_party/".into()];
        let policy = policy_from_global("Example".into(), &global).unwrap();
        let defaults = defaults_from_global(&global).unwrap();
        assert_eq!(policy.embeddings.backend, Backend::Local);
        assert_eq!(policy.embeddings.model, None);
        assert_eq!(policy.embeddings.batch_size, 16);
        assert_eq!(policy.watcher.debounce_ms, 450);
        assert!(policy.index.exclude.is_empty());
        assert_eq!(defaults.index.exclude.last().unwrap(), "generated/");
        assert_eq!(defaults.index.vendor.last().unwrap(), "third_party/");
        assert!(defaults.revision.starts_with("global-snapshot-v1-"));
        assert!(!json!({"policy":policy,"defaults":defaults})
            .to_string()
            .contains("private-global-key"));
        let saved = policy.effective(&defaults);
        global.embeddings.batch_size = 32;
        global.index.exclude.push("src/".into());
        assert_eq!(policy.effective(&defaults), saved);
        assert_ne!(
            defaults_from_global(&global).unwrap().revision,
            defaults.revision
        );
        assert_eq!(
            policy_from_global("Other".into(), &global)
                .unwrap()
                .embeddings
                .batch_size,
            32
        );
    }

    #[test]
    fn invalid_global_family_defaults_are_rejected_without_substitution() {
        let mut global = GlobalConfig::default();
        global.embeddings.model = Some("unsupported-model".into());
        assert_eq!(
            policy_from_global("Example".into(), &global)
                .unwrap_err()
                .code,
            "invalid_global_defaults"
        );
        global.index.exclude = vec!["[".into()];
        assert_eq!(
            defaults_from_global(&global).unwrap_err().code,
            "invalid_global_defaults"
        );
    }
    use crate::pipeline::Decision;
    fn request() -> ApplyRequest {
        ApplyRequest {
            api_version: 1,
            expected_family_id: Uuid::new_v4(),
            expected_revision: 1,
            acknowledge_reindex: false,
            policy: Policy::shipped("fixture".into()),
        }
    }
    #[test]
    fn wire_rejects_unknown_duplicate_missing_and_wrongly_typed_fields() {
        let value = serde_json::to_value(request()).unwrap();
        for pointer in [
            "/api_version",
            "/expected_family_id",
            "/expected_revision",
            "/policy/name",
            "/policy/index/exclude",
            "/policy/embeddings/model",
        ] {
            let mut invalid = value.clone();
            let (parent, key) = pointer.rsplit_once('/').unwrap();
            invalid
                .pointer_mut(parent)
                .unwrap()
                .as_object_mut()
                .unwrap()
                .remove(key);
            assert!(
                ApplyRequest::parse(&invalid.to_string()).is_err(),
                "{pointer}"
            );
        }
        for pointer in [
            "",
            "/policy",
            "/policy/index",
            "/policy/watcher",
            "/policy/embeddings",
        ] {
            let mut invalid = value.clone();
            invalid
                .pointer_mut(pointer)
                .unwrap()
                .as_object_mut()
                .unwrap()
                .insert("api_key".into(), json!("SECRET_MARKER"));
            let error = ApplyRequest::parse(&invalid.to_string()).unwrap_err();
            assert!(!failure(&error).to_string().contains("SECRET_MARKER"));
        }
        let raw = value.to_string();
        for (from, to) in [
            ("\"api_version\":1", "\"api_version\":1,\"api_version\":1"),
            (
                "\"name\":\"fixture\"",
                "\"name\":\"fixture\",\"name\":\"fixture\"",
            ),
            ("\"batch_size\":64", "\"batch_size\":64,\"batch_size\":64"),
            ("\"expected_revision\":1", "\"expected_revision\":1.0"),
            ("\"expected_revision\":1", "\"expected_revision\":\"1\""),
        ] {
            assert!(raw.contains(from));
            assert!(ApplyRequest::parse(&raw.replace(from, to)).is_err());
        }
        assert!(ApplyRequest::parse(&(raw + " true")).is_err());
    }
    #[test]
    fn validation_reports_rule_index_without_echoing_input() {
        for pattern in ["", "  ", "!", "[", "a\0b"] {
            let mut request = request();
            request.policy.index.exclude = vec!["target/".into(), pattern.into()];
            let error = request.validate().unwrap_err();
            assert_eq!(error.details["field"], "index.exclude");
            assert_eq!(error.details["index"], 1);
        }
    }
    #[test]
    fn shipped_defaults_stay_frozen_and_rule_order_is_preserved() {
        let old = Defaults::shipped();
        let mut newer = old.clone();
        newer.index.exclude.push("src/**".into());
        let mut policy = Policy::shipped("fixture".into());
        policy.index.vendor = vec!["!**/target/**".into()];
        let frozen = policy.effective(&old);
        let resolved = EffectiveRules::resolve(&policy, &old);
        assert_eq!(resolved.vendor.last().unwrap().origin, RuleOrigin::Family);
        assert_eq!(
            resolved.vendor.last().unwrap().position,
            old.index.vendor.len()
        );
        assert_eq!(
            resolved.vendor.first().unwrap().origin,
            RuleOrigin::Defaults
        );
        assert_eq!(
            resolved
                .vendor
                .iter()
                .map(|r| r.pattern.clone())
                .collect::<Vec<_>>(),
            frozen.index.vendor
        );
        assert_ne!(frozen, policy.effective(&newer));
        assert_eq!(frozen, policy.effective(&old));
        let mut defaults = Defaults::shipped();
        defaults.index.exclude = vec![];
        defaults.index.vendor = vec![];
        policy.index.exclude = vec!["*.rs".into(), "!main.rs".into()];
        let compiled = CompiledRules::new(Path::new("/repo"), &policy, &defaults).unwrap();
        assert_eq!(compiled.classify(Path::new("main.rs")), Decision::Tier1);
        assert_eq!(compiled.classify(Path::new("lib.rs")), Decision::Drop);
        policy.index.exclude.reverse();
        assert_eq!(
            CompiledRules::new(Path::new("/repo"), &policy, &defaults)
                .unwrap()
                .classify(Path::new("main.rs")),
            Decision::Drop
        );
    }
    #[test]
    fn exclusion_pruning_vendor_and_git_guards_match_runtime() {
        let mut policy = Policy::shipped("fixture".into());
        policy.index.exclude = vec!["target/".into(), "!target/keep.rs".into(), "!.git/".into()];
        policy.index.vendor = vec!["src/**".into()];
        let defaults = Defaults::shipped();
        let compiled = CompiledRules::new(Path::new("/repo"), &policy, &defaults).unwrap();
        assert_eq!(
            compiled.classify(Path::new("target/keep.rs")),
            Decision::Drop
        );
        assert_eq!(compiled.classify(Path::new(".git/config")), Decision::Drop);
        assert_eq!(compiled.classify(Path::new("src/main.rs")), Decision::Tier2);
        assert_eq!(
            compiled.classify(Path::new("node_modules/pkg/a.js")),
            Decision::Tier2
        );
    }
    #[test]
    fn scalar_boundaries_and_profile_choices_are_explicit() {
        let mut r = request();
        for revision in [0, MAX_REVISION + 1] {
            r.expected_revision = revision;
            assert!(r.validate().is_err());
        }
        r.expected_revision = MAX_REVISION;
        assert!(r.validate().is_ok());
        r.policy.embeddings.batch_size = 0;
        assert!(r.validate().is_err());
        r.policy.embeddings.batch_size = u32::MAX;
        assert!(r.validate().is_ok());
        r.policy.embeddings.backend = Backend::Local;
        assert!(r.validate().is_err());
        r.policy.embeddings.model = None;
        assert!(r.validate().is_ok());
        let mut value = serde_json::to_value(&r).unwrap();
        value["policy"]["embeddings"]
            .as_object_mut()
            .unwrap()
            .remove("model");
        assert!(ApplyRequest::parse(&value.to_string()).is_err());
        let raw = serde_json::to_string(&r)
            .unwrap()
            .replace("\"model\":null", "\"model\":null,\"model\":null");
        assert!(ApplyRequest::parse(&raw).is_err());
        r.api_version = 2;
        assert!(r.validate().is_err());
    }
    #[test]
    fn impact_distinguishes_work_without_weakening_revision_guards() {
        let policy = request().policy;
        let mut candidate = policy.clone();
        candidate.name = "other".into();
        assert_eq!(policy.impact(&candidate), Impact::Display);
        candidate.watcher.debounce_ms += 1;
        assert_eq!(policy.impact(&candidate), Impact::Runtime);
        candidate.index.exclude.push("target/".into());
        assert_eq!(policy.impact(&candidate), Impact::Selection);
        candidate.embeddings.backend = Backend::Local;
        candidate.embeddings.model = None;
        assert_eq!(policy.impact(&candidate), Impact::EmbeddingProfile);
    }
}
