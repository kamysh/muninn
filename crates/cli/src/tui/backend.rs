use super::model::Draft;
use crate::readonly::{credential_availability, enrich_credentials, error};
use muninn_core::{
    config::GlobalConfig,
    family_policy::{
        self as policy,
        readonly::{self, Operation},
    },
    family_store::{self, CheckoutIdentity, PreparationConnection},
};
use serde_json::{json, Value};
use std::{
    future::Future,
    path::{Path, PathBuf},
};
use tokio_postgres::Client;

pub trait Backend {
    async fn load(&mut self) -> policy::Result<Value>;
    async fn check(&mut self, draft: &Draft) -> policy::Result<Value>;
    async fn save(&mut self, draft: &Draft) -> policy::Result<Value>;
    async fn start(&mut self, draft: &Draft) -> policy::Result<Value>;
    async fn start_with_progress(
        &mut self,
        draft: &Draft,
        _progress: impl Fn(usize, usize, &Path),
    ) -> policy::Result<Value> {
        self.start(draft).await
    }
}
pub struct Database<F> {
    pub client: Client,
    pub config: GlobalConfig,
    pub path: PathBuf,
    pub add_mode: bool,
    pub prepare: F,
}

fn accept_refreshed_config(current: &mut GlobalConfig, latest: GlobalConfig) -> policy::Result<()> {
    if current.database != latest.database {
        return Err(error(
            "global_connection_changed",
            "Global database settings changed. Close and reopen configuration before continuing.",
        ));
    }
    *current = latest;
    Ok(())
}

fn refresh_config(current: &mut GlobalConfig) -> policy::Result<()> {
    let latest = GlobalConfig::load().map_err(|_| {
        error(
            "bootstrap_config_error",
            "Cannot reload global configuration. Check it, then retry.",
        )
    })?;
    accept_refreshed_config(current, latest)
}

fn require_start_credentials(
    config: &GlobalConfig,
    backend: policy::Backend,
) -> policy::Result<()> {
    if credential_availability(config, backend) == "missing_for_selected_backend" {
        return Err(error(
            "missing_credentials",
            "The selected hosted provider needs a matching API key in global configuration. Configure it and rescan before starting.",
        ));
    }
    Ok(())
}
impl<F, Fut> Backend for Database<F>
where
    F: Fn() -> Fut,
    Fut: Future<Output = anyhow::Result<PreparationConnection>>,
{
    async fn load(&mut self) -> policy::Result<Value> {
        refresh_config(&mut self.config)?;
        let mut data = readonly::query_with_creation(
            &mut self.client,
            &self.path,
            Operation::Preflight,
            None,
            |root| {
                let name = root
                    .file_name()
                    .unwrap_or(root.as_os_str())
                    .to_string_lossy()
                    .into_owned();
                Ok((
                    policy::policy_from_global(name, &self.config)?,
                    policy::defaults_from_global(&self.config)?,
                ))
            },
        )
        .await?;
        if !self.add_mode && data["family_id"].is_null() {
            return Err(error(
                "not_registered",
                "use muninn add PATH to configure a new family",
            ));
        }
        enrich_credentials(&mut data, &self.config, false)?;
        Ok(data)
    }
    async fn check(&mut self, draft: &Draft) -> policy::Result<Value> {
        refresh_config(&mut self.config)?;
        let initial: policy::Policy = serde_json::from_value(draft.base["policy"].clone())
            .map_err(|_| {
                error(
                    "invalid_stored_policy",
                    "Cannot read the initial policy snapshot",
                )
            })?;
        let mut data = readonly::query_with_creation(
            &mut self.client,
            &self.path,
            Operation::Check,
            Some(&draft.request().to_string()),
            |_| Ok((initial, draft.defaults.clone())),
        )
        .await?;
        enrich_credentials(&mut data, &self.config, true)?;
        Ok(data)
    }
    async fn start(&mut self, draft: &Draft) -> policy::Result<Value> {
        self.start_with_progress(draft, |_, _, _| {}).await
    }
    async fn start_with_progress(
        &mut self,
        draft: &Draft,
        progress: impl Fn(usize, usize, &Path),
    ) -> policy::Result<Value> {
        refresh_config(&mut self.config)?;
        require_start_credentials(&self.config, draft.policy.embeddings.backend)?;
        let request = policy::start::Request {
            api_version: 1,
            expected_family_id: draft
                .family_id()
                .ok_or_else(|| error("not_registered", "save the family before starting"))?,
            expected_revision: draft
                .revision()
                .ok_or_else(|| error("not_registered", "save the family before starting"))?,
        };
        crate::writes::start_configured_with_progress(
            &mut self.client,
            &self.config,
            &self.path,
            &request,
            progress,
        )
        .await
    }
    async fn save(&mut self, draft: &Draft) -> policy::Result<Value> {
        refresh_config(&mut self.config)?;
        let mut data = if let Some(family_id) = draft.family_id() {
            let request = policy::ApplyRequest::parse(&draft.request().to_string())?;
            let mut receipt = policy::apply_path(&mut self.client, &self.path, &request).await?;
            if self.add_mode {
                // The policy receipt remains authoritative if associating the
                // selected checkout subsequently fails. Never report rollback.
                let association = async {
                    let context = readonly::resolve(&self.client, &self.path).await?;
                    if context.view.as_ref().map(|v| v.family_id) != Some(family_id) {
                        return Err(error("family_conflict", "path changed after saving policy"));
                    }
                    let identity = CheckoutIdentity::discover(&context.root)
                        .await
                        .map_err(|_| error("invalid_path", "cannot discover selected checkout"))?;
                    let checkout =
                        family_store::register_checkout(&mut self.client, family_id, &identity)
                            .await
                            .map_err(|_| {
                                error(
                                    "registration_error",
                                    "policy saved; checkout association failed",
                                )
                            })?;
                    Ok(checkout)
                }
                .await;
                match association {
                    Ok(checkout) => {
                        receipt["checkout_id"] = json!(checkout.token.id);
                        receipt["checkout"]["checkout_id"] = json!(checkout.token.id);
                        receipt["checkout"]["registration_state"] =
                            json!(checkout.registration_state.as_str());
                        receipt["checkout"]["paused"] = json!(checkout.paused);
                    }
                    Err(error) => receipt["registration_error"] = json!(error),
                }
            }
            receipt
        } else {
            let request = policy::InitialRequest::parse(&draft.request().to_string())?;
            let initial: policy::Policy = serde_json::from_value(draft.base["policy"].clone())
                .map_err(|_| {
                    error(
                        "invalid_stored_policy",
                        "Cannot read the initial policy snapshot",
                    )
                })?;
            policy::registration::add_with_creation(
                &mut self.client,
                &self.prepare,
                &self.path,
                Some(&request),
                |_| Ok((initial, draft.defaults.clone())),
            )
            .await?
        };
        enrich_credentials(&mut data, &self.config, false)?;
        Ok(data)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use muninn_core::config::EmbeddingBackend;

    #[test]
    fn refreshing_credentials_preserves_the_connected_database_target() {
        let mut current = GlobalConfig::default();
        let mut latest = current.clone();
        latest.embeddings.api_key = Some("new-private-key".into());
        accept_refreshed_config(&mut current, latest).unwrap();
        assert_eq!(
            current.embeddings.api_key.as_deref(),
            Some("new-private-key")
        );
        let before = current.clone();
        let mut moved = current.clone();
        moved.database.dbname = "different_database".into();
        assert_eq!(
            accept_refreshed_config(&mut current, moved)
                .unwrap_err()
                .code,
            "global_connection_changed"
        );
        assert_eq!(current.database, before.database);
        assert_eq!(current.embeddings, before.embeddings);
    }

    #[test]
    fn missing_or_wrong_provider_key_cannot_authorize_a_hosted_start() {
        let mut config = GlobalConfig::default();
        assert!(require_start_credentials(&config, policy::Backend::Local).is_ok());
        assert_eq!(
            require_start_credentials(&config, policy::Backend::Voyage)
                .unwrap_err()
                .code,
            "missing_credentials"
        );
        config.embeddings.backend = EmbeddingBackend::OpenAI;
        config.embeddings.api_key = Some("private-test-key".into());
        assert!(require_start_credentials(&config, policy::Backend::OpenAI).is_ok());
        assert!(require_start_credentials(&config, policy::Backend::Voyage).is_err());
    }
}
