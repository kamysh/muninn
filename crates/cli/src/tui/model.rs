use muninn_core::family_policy::{self as policy, ApplyRequest, Defaults, InitialRequest, Policy};
use serde_json::{json, Value};
use uuid::Uuid;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Field {
    Name,
    Debounce,
    Backend,
    Batch,
    Exclude(usize),
    AddExclude,
    Vendor(usize),
    AddVendor,
}
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum View {
    Policy,
    Rules,
    Defaults,
    Agent,
    Conflict,
    Message,
    Help,
    Details,
}

pub struct Draft {
    pub base: Value,
    pub policy: Policy,
    pub defaults: Defaults,
    pub checked: Option<Value>,
    pub latest: Option<Value>,
    pub status: String,
    pub view: View,
    pub selected: usize,
    pub scroll: usize,
}
impl Draft {
    pub fn new(base: Value) -> anyhow::Result<Self> {
        let policy: Policy = serde_json::from_value(base["policy"].clone())?;
        let defaults: Defaults = serde_json::from_value(base["defaults"].clone())?;
        policy.validate()?;
        defaults.validate()?;
        anyhow::ensure!(
            base["family_id"].is_null()
                || (base["family_id"]
                    .as_str()
                    .and_then(|id| id.parse::<Uuid>().ok())
                    .is_some()
                    && base["revision"].as_u64().is_some()),
            "Malformed family identity or revision"
        );
        let checked = base.get("preflight").map(|_| base.clone());
        Ok(Self {
            base,
            policy,
            defaults,
            checked,
            latest: None,
            status: String::new(),
            view: View::Policy,
            selected: 0,
            scroll: 0,
        })
    }
    pub fn family_id(&self) -> Option<Uuid> {
        self.base["family_id"]
            .as_str()
            .and_then(|id| id.parse().ok())
    }
    pub fn revision(&self) -> Option<u64> {
        self.base["revision"].as_u64()
    }
    pub fn dirty(&self) -> bool {
        json!(self.policy) != self.base["policy"]
    }
    pub fn request(&self) -> Value {
        match self.family_id() {
            Some(family) => json!(ApplyRequest {
                api_version: 1,
                expected_family_id: family,
                expected_revision: self.revision().expect("registered policy has a revision"),
                acknowledge_reindex: false,
                policy: self.policy.clone()
            }),
            None => json!(InitialRequest {
                api_version: 1,
                policy: self.policy.clone()
            }),
        }
    }
    pub fn fields(&self) -> Vec<Field> {
        let mut fields = vec![Field::Name, Field::Debounce, Field::Backend, Field::Batch];
        fields.extend((0..self.policy.index.exclude.len()).map(Field::Exclude));
        fields.push(Field::AddExclude);
        fields.extend((0..self.policy.index.vendor.len()).map(Field::Vendor));
        fields.push(Field::AddVendor);
        fields
    }
    pub fn selected(&self) -> Field {
        self.fields()[self.selected.min(self.fields().len() - 1)]
    }
    pub fn edit(&mut self, field: Field, value: String) -> anyhow::Result<()> {
        let mut next = self.policy.clone();
        match field {
            Field::Name => next.name = value,
            Field::Debounce => {
                next.watcher.debounce_ms = value
                    .parse()
                    .map_err(|_| anyhow::anyhow!("Enter nonnegative whole milliseconds"))?
            }
            Field::Batch => {
                next.embeddings.batch_size = value
                    .parse()
                    .map_err(|_| anyhow::anyhow!("Enter a positive whole batch size"))?
            }
            Field::Backend => {
                anyhow::ensure!(
                    self.family_id().is_none(),
                    "Embedding profile is fixed for this registered family"
                );
                next.embeddings.backend = match value.as_str() {
                    "voyage" => policy::Backend::Voyage,
                    "openai" => policy::Backend::OpenAI,
                    "local" => policy::Backend::Local,
                    _ => anyhow::bail!("Choose voyage, openai or local"),
                };
                next.embeddings.model = match next.embeddings.backend {
                    policy::Backend::Local => None,
                    backend => Some(backend.model_identity().into()),
                };
            }
            Field::Exclude(i) => next.index.exclude[i] = value,
            Field::Vendor(i) => next.index.vendor[i] = value,
            Field::AddExclude => next.index.exclude.push(value),
            Field::AddVendor => next.index.vendor.push(value),
        }
        next.validate()?;
        self.policy = next;
        self.invalidate();
        Ok(())
    }
    pub fn remove(&mut self) {
        match self.selected() {
            Field::Exclude(i) => {
                self.policy.index.exclude.remove(i);
            }
            Field::Vendor(i) => {
                self.policy.index.vendor.remove(i);
            }
            _ => return,
        }
        self.selected = self.selected.min(self.fields().len() - 1);
        self.invalidate();
    }
    pub fn move_rule(&mut self, up: bool) {
        let (rules, index) = match self.selected() {
            Field::Exclude(i) => (&mut self.policy.index.exclude, i),
            Field::Vendor(i) => (&mut self.policy.index.vendor, i),
            _ => return,
        };
        let target = if up {
            index.checked_sub(1)
        } else {
            (index + 1 < rules.len()).then_some(index + 1)
        };
        if let Some(target) = target {
            rules.swap(index, target);
            if up {
                self.selected -= 1;
            } else {
                self.selected += 1;
            }
            self.invalidate();
        }
    }
    fn invalidate(&mut self) {
        self.checked = None;
        self.status = "Draft changed. Refresh the preview before saving.".into();
    }
    pub fn receive_latest(&mut self, latest: Value) {
        self.latest = Some(latest);
        self.view = View::Conflict;
        self.scroll = 0;
        self.status =
            "Current policy loaded for review. Your draft is retained; nothing overwritten.".into();
    }
    pub fn keep_draft_on_latest(&mut self) -> anyhow::Result<()> {
        let latest = self
            .latest
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("Load current policy first"))?;
        anyhow::ensure!(
            latest["family_id"] == self.base["family_id"] && self.family_id().is_some(),
            "Family identity changed: load current policy or leave with your old draft"
        );
        let policy = self.policy.clone();
        let mut replacement = Self::new(latest.clone())?;
        replacement.policy = policy;
        replacement.invalidate();
        replacement.status =
            "Reviewed current revision; draft retained. Check and save explicitly to apply it."
                .into();
        *self = replacement;
        Ok(())
    }
}

/// Terminal control characters are never interpreted as rendering instructions.
pub fn visible(text: &str) -> String {
    text.chars()
        .flat_map(|c| {
            if c.is_control() {
                c.escape_default().collect::<Vec<_>>()
            } else {
                vec![c]
            }
        })
        .collect()
}
/// Copyable Bash/Zsh argument, preserving unusual native path bytes.
pub fn shell_path(path: &std::path::Path) -> String {
    if let Some(text) = path.to_str().filter(|s| !s.chars().any(char::is_control)) {
        return format!("'{}'", text.replace('\'', "'\\''"));
    }
    #[cfg(unix)]
    {
        use std::os::unix::ffi::OsStrExt;
        format!(
            "$'{}'",
            path.as_os_str()
                .as_bytes()
                .iter()
                .map(|b| format!("\\x{b:02x}"))
                .collect::<String>()
        )
    }
    #[cfg(not(unix))]
    {
        "<use the selected directory as your working directory>".into()
    }
}
