use super::StoredPath;
use crate::repo_resolver::{discover_git_checkout, GitOperationState};
use anyhow::{bail, ensure, Result};
use chrono::{DateTime, Utc};
use std::path::Path;
use uuid::Uuid;

macro_rules! db_enum {
    ($name:ident { $($variant:ident => $value:literal),+ $(,)? }) => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        pub enum $name { $($variant),+ }
        impl $name {
            pub fn as_str(self) -> &'static str {
                match self { $(Self::$variant => $value),+ }
            }
            pub(crate) fn from_db(value: &str) -> Result<Self> {
                match value { $($value => Ok(Self::$variant)),+, _ => bail!("invalid {}: {value}", stringify!($name)) }
            }
        }
    };
}

db_enum!(FamilyKind { Git => "git", Directory => "directory" });
db_enum!(SchemaState { Pending => "pending", Migrating => "migrating", Ready => "ready", Failed => "failed" });
db_enum!(StorageGeneration { Legacy => "legacy", Snapshots => "snapshots" });
db_enum!(EnableOrigin { ExplicitStart => "explicit-start", LegacyImport => "legacy-import" });
db_enum!(RegistrationState { Active => "active", Suppressed => "suppressed", Retired => "retired" });
db_enum!(Availability { Unknown => "unknown", Available => "available", Unavailable => "unavailable" });

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FamilyIdentity {
    pub kind: FamilyKind,
    pub key: StoredPath,
}

/// Filesystem-validated registration input, not a database registration itself.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckoutIdentity {
    pub family: FamilyIdentity,
    pub root: StoredPath,
    pub git_dir: Option<StoredPath>,
}

impl CheckoutIdentity {
    pub async fn discover(directory: &Path) -> Result<Self> {
        if let Some(git) = discover_git_checkout(directory).await? {
            Ok(Self {
                family: FamilyIdentity {
                    kind: FamilyKind::Git,
                    key: StoredPath::canonicalize(&git.common_dir).await?,
                },
                root: StoredPath::canonicalize(&git.root).await?,
                git_dir: Some(StoredPath::canonicalize(&git.git_dir).await?),
            })
        } else {
            let root = StoredPath::canonicalize(directory).await?;
            Ok(Self {
                family: FamilyIdentity {
                    kind: FamilyKind::Directory,
                    key: root.clone(),
                },
                root,
                git_dir: None,
            })
        }
    }

    pub(crate) async fn revalidate(&self) -> Result<()> {
        ensure!(
            Self::discover(&self.root.to_path_buf()?).await? == *self,
            "checkout identity changed during registration"
        );
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct Family {
    pub id: Uuid,
    pub legacy_path: String,
    pub name: String,
    pub embedding_dim: u32,
    pub paused: bool,
    pub identity: Option<FamilyIdentity>,
    pub retired_at: Option<DateTime<Utc>>,
    pub schema_state: SchemaState,
    pub schema_error: Option<String>,
    pub storage_generation: StorageGeneration,
    pub indexing_enabled_at: Option<DateTime<Utc>>,
    pub indexing_enable_origin: Option<EnableOrigin>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CheckoutToken {
    pub id: Uuid,
    pub incarnation: Uuid,
    pub dirty_generation: i64,
}

/// Unknown is separate from a successful observation with no blockers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ObservedGitState {
    Unknown,
    NotGit,
    Known(GitOperationState),
}

impl ObservedGitState {
    pub(crate) fn columns(self) -> (&'static str, [Option<bool>; 4]) {
        match self {
            Self::Unknown => ("unknown", [None; 4]),
            Self::NotGit => ("not-git", [None; 4]),
            Self::Known(s) => (
                if s.is_blocked() { "blocked" } else { "clear" },
                [
                    Some(s.merge),
                    Some(s.rebase_merge),
                    Some(s.rebase_apply),
                    Some(s.unmerged_index),
                ],
            ),
        }
    }
    pub(crate) fn from_db(state: &str, flags: [Option<bool>; 4]) -> Result<Self> {
        match (state, flags) {
            ("unknown", [None, None, None, None]) => Ok(Self::Unknown),
            ("not-git", [None, None, None, None]) => Ok(Self::NotGit),
            (
                "clear" | "blocked",
                [Some(merge), Some(rebase_merge), Some(rebase_apply), Some(unmerged_index)],
            ) => {
                let s = GitOperationState {
                    merge,
                    rebase_merge,
                    rebase_apply,
                    unmerged_index,
                };
                ensure!(
                    s.is_blocked() == (state == "blocked"),
                    "inconsistent Git observation"
                );
                Ok(Self::Known(s))
            }
            _ => bail!("invalid Git observation"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Checkout {
    pub token: CheckoutToken,
    pub root: StoredPath,
    pub git_dir: Option<StoredPath>,
    pub registration_state: RegistrationState,
    pub paused: bool,
    pub created_at: DateTime<Utc>,
    pub retired_at: Option<DateTime<Utc>>,
    pub availability: Availability,
    pub git_state: ObservedGitState,
    pub observed_at: Option<DateTime<Utc>>,
    pub last_seen_at: Option<DateTime<Utc>>,
    pub observation_error: Option<String>,
}

#[derive(Debug, Clone)]
pub struct ResolvedCheckout {
    pub family: Family,
    pub checkout: Checkout,
}

/// Diagnostic text supplied here must already have secrets removed.
#[derive(Debug, Clone)]
pub struct CheckoutObservation {
    pub availability: Availability,
    pub git_state: ObservedGitState,
    pub error: Option<String>,
}

impl CheckoutObservation {
    pub(crate) fn validate(&self) -> Result<()> {
        ensure!(
            self.availability == Availability::Available
                || self.git_state == ObservedGitState::Unknown,
            "unavailable or unknown checkout cannot have a known Git state"
        );
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn git_observation_preserves_unknown_and_all_blocker_combinations() {
        for bits in 0..16 {
            let state = ObservedGitState::Known(GitOperationState {
                merge: bits & 1 != 0,
                rebase_merge: bits & 2 != 0,
                rebase_apply: bits & 4 != 0,
                unmerged_index: bits & 8 != 0,
            });
            let (name, flags) = state.columns();
            assert_eq!(ObservedGitState::from_db(name, flags).unwrap(), state);
        }
        assert!(ObservedGitState::from_db("clear", [None; 4]).is_err());
        assert!(ObservedGitState::from_db("unknown", [Some(false); 4]).is_err());
        assert!(ObservedGitState::from_db("blocked", [Some(false); 4]).is_err());
        assert!(CheckoutObservation {
            availability: Availability::Unavailable,
            git_state: ObservedGitState::NotGit,
            error: None
        }
        .validate()
        .is_err());
    }
}
