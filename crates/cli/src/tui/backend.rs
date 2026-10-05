use super::model::Draft;
use crate::readonly::{enrich_credentials, error};
use muninn_core::{
    config::GlobalConfig,
    family_policy::{
        self as policy,
        readonly::{self, Operation},
    },
    family_store::{self, CheckoutIdentity, PreparationConnection},
};
use serde_json::{json, Value};
use std::{future::Future, path::PathBuf};
use tokio_postgres::Client;

pub trait Backend {
    async fn load(&mut self) -> policy::Result<Value>;
    async fn check(&mut self, draft: &Draft) -> policy::Result<Value>;
    async fn save(&mut self, draft: &Draft) -> policy::Result<Value>;
    async fn start(&mut self, draft: &Draft) -> policy::Result<Value>;
}
pub struct Database<F> {
    pub client: Client,
    pub config: GlobalConfig,
    pub path: PathBuf,
    pub add_mode: bool,
    pub prepare: F,
}
impl<F, Fut> Backend for Database<F>
where
    F: Fn() -> Fut,
    Fut: Future<Output = anyhow::Result<PreparationConnection>>,
{
    async fn load(&mut self) -> policy::Result<Value> {
        let mut data =
            readonly::query(&mut self.client, &self.path, Operation::Preflight, None).await?;
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
        let mut data = readonly::query(
            &mut self.client,
            &self.path,
            Operation::Check,
            Some(&draft.request().to_string()),
        )
        .await?;
        enrich_credentials(&mut data, &self.config, true)?;
        Ok(data)
    }
    async fn start(&mut self, draft: &Draft) -> policy::Result<Value> {
        let request = policy::start::Request {
            api_version: 1,
            expected_family_id: draft
                .family_id()
                .ok_or_else(|| error("not_registered", "save the family before starting"))?,
            expected_revision: draft
                .revision()
                .ok_or_else(|| error("not_registered", "save the family before starting"))?,
        };
        crate::writes::start_configured(&mut self.client, &self.config, &self.path, &request).await
    }
    async fn save(&mut self, draft: &Draft) -> policy::Result<Value> {
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
            policy::registration::add(&mut self.client, &self.prepare, &self.path, Some(&request))
                .await?
        };
        enrich_credentials(&mut data, &self.config, false)?;
        Ok(data)
    }
}
