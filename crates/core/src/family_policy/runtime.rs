//! Runtime adapter for stored policy and global defaults for unbound registrations.
use super::{Backend, CompiledRules, PolicyView};
use crate::config::{EffectiveConfig, EmbeddingBackend, GlobalConfig, WatcherConfig};
use anyhow::{ensure, Result};
use std::{path::Path, sync::Arc};
use tokio_postgres::{GenericClient, Transaction};
use uuid::Uuid;

pub async fn policy(client: &impl GenericClient, id: Uuid) -> Result<Option<PolicyView>> {
    let bound: bool = client
        .query_one(
            "SELECT family_key IS NOT NULL FROM public.repos WHERE id=$1 AND retired_at IS NULL",
            &[&id],
        )
        .await?
        .get(0);
    if bound {
        Ok(Some(super::inspect(client, id).await?))
    } else {
        Ok(None)
    }
}

/// Hold the current pointer against concurrent apply until publication commits.
/// A saved policy cannot be followed by publication using the previous rules.
pub async fn lock_policy(tx: &Transaction<'_>, id: Uuid) -> Result<Option<PolicyView>> {
    if policy(tx, id).await?.is_none() {
        return Ok(None);
    }
    tx.query_one(
        &format!(
            "SELECT current_revision FROM {}.family_policy WHERE singleton FOR SHARE",
            crate::store::repo_schema(id)
        ),
        &[],
    )
    .await?;
    let view = policy(tx, id).await?.expect("bound family");
    ensure!(
        view.indexing_enabled,
        "indexing has not been started; use muninn start PATH"
    );
    ensure!(!view.paused, "family is paused");
    Ok(Some(view))
}

pub fn effective(global: &GlobalConfig, view: &PolicyView) -> EffectiveConfig {
    let p = &view.effective_policy;
    let backend = match p.embeddings.backend {
        Backend::Voyage => EmbeddingBackend::Voyage,
        Backend::OpenAI => EmbeddingBackend::OpenAI,
        Backend::Local => EmbeddingBackend::Local,
    };
    let mut embeddings = global.embeddings.clone();
    if embeddings.backend != backend {
        embeddings.api_key = None;
    }
    embeddings.backend = backend;
    embeddings.model = p.embeddings.model.clone();
    embeddings.batch_size = p.embeddings.batch_size as usize;
    EffectiveConfig {
        database: global.database.clone(),
        embeddings,
        watcher: WatcherConfig {
            debounce_ms: p.watcher.debounce_ms,
        },
        exclude: p.index.exclude.clone(),
        vendor: p.index.vendor.clone(),
        repo_name: p.name.clone(),
    }
}

pub async fn config(
    client: &impl GenericClient,
    id: Uuid,
    root: &Path,
    global: &GlobalConfig,
) -> Result<(EffectiveConfig, Option<PolicyView>)> {
    let view = policy(client, id).await?;
    let config = match &view {
        Some(view) => effective(global, view),
        None => EffectiveConfig::from_global(
            global,
            &root.file_name().unwrap_or_default().to_string_lossy(),
        ),
    };
    Ok((config, view))
}

/// Both inventory and runtime use CompiledRules, including parent pruning.
#[derive(Clone)]
pub enum Selection {
    Policy(Arc<CompiledRules>),
    Legacy(ignore::overrides::Override, ignore::overrides::Override),
}
impl Selection {
    pub fn new(
        root: &Path,
        view: Option<&PolicyView>,
        exclude: &[String],
        vendor: &[String],
    ) -> Result<Self> {
        Ok(match view {
            Some(v) => Self::Policy(Arc::new(CompiledRules::new(root, &v.policy, &v.defaults)?)),
            None => Self::Legacy(
                crate::pipeline::build_excludes(root, exclude),
                crate::pipeline::build_excludes(root, vendor),
            ),
        })
    }
    pub fn classify(&self, relative: &Path, directory: bool) -> crate::pipeline::Decision {
        use crate::pipeline::{path_excluded, Decision};
        match self {
            Self::Policy(rules) => rules.classify_entry(relative, directory),
            Self::Legacy(exclude, vendor) => {
                if relative.components().any(|c| c.as_os_str() == ".git")
                    || path_excluded(exclude, relative)
                {
                    Decision::Drop
                } else if path_excluded(vendor, relative) {
                    Decision::Tier2
                } else {
                    Decision::Tier1
                }
            }
        }
    }
    pub fn walker(&self, root: &Path) -> ignore::Walk {
        let mut builder = ignore::WalkBuilder::new(root);
        builder.standard_filters(false);
        match self {
            Self::Legacy(exclude, _) => {
                builder
                    .overrides(exclude.clone())
                    .filter_entry(|e| e.file_name() != ".git");
            }
            Self::Policy(_) => {
                let selection = self.clone();
                let root = root.to_owned();
                builder.filter_entry(move |entry| {
                    entry.path() == root
                        || entry.path().strip_prefix(&root).is_ok_and(|p| {
                            selection.classify(p, entry.file_type().is_some_and(|t| t.is_dir()))
                                != crate::pipeline::Decision::Drop
                        })
                });
            }
        }
        builder.build()
    }
}

/// The primary Git checkout remains the runtime anchor even when add selected
/// a linked worktree which is later removed.
pub async fn root(
    client: &impl GenericClient,
    id: Uuid,
    legacy: &Path,
) -> Result<std::path::PathBuf> {
    let family = crate::family_store::get_family(client, id)
        .await?
        .ok_or_else(|| anyhow::anyhow!("family removed"))?;
    if let Some(identity) = family.identity {
        if identity.kind == crate::family_store::FamilyKind::Git {
            let entries =
                crate::repo_resolver::list_git_worktrees(&identity.key.to_path_buf()?).await?;
            let primary = entries
                .first()
                .ok_or_else(|| anyhow::anyhow!("empty worktree registry"))?;
            ensure!(!primary.bare, "non-bare primary checkout required");
            return Ok(primary.path.clone());
        }
        return identity.key.to_path_buf();
    }
    Ok(legacy.to_owned())
}
