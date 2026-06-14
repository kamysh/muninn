use clap::{Args, Parser, Subcommand};
use muninn_core::{
    config::{self, GlobalConfig, RepoConfig},
    db, store,
};
use std::io::Write as _;
use std::path::Path;
use tokio_postgres::Client;

#[derive(Parser)]
#[command(name = "muninn", about = "muninn repository index manager", version)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Bootstrap the global config (~/.config/muninn/config.toml) and run migrations
    Init {
        /// Initial key=value settings (non-interactive); omit to edit in $EDITOR
        #[arg(value_name = "KEY=VALUE")]
        set: Vec<String>,
    },
    /// Get, set, edit, or unset config keys (--global or --repo <path>)
    Config {
        #[command(subcommand)]
        op: ConfigOp,
    },
    /// Register a repository and run its initial index
    Add {
        /// Repository path
        path: String,
        /// Initial key=value settings for the repo's .muninn.toml
        #[arg(value_name = "KEY=VALUE")]
        set: Vec<String>,
        /// Register without running the initial index
        #[arg(long)]
        no_index: bool,
    },
    /// Re-index a repository in the foreground (or all repos / detached)
    Reindex {
        path: Option<String>,
        #[arg(long, conflicts_with = "path")]
        all: bool,
        /// Hand the reindex to the background daemon instead of running it here
        #[arg(long, conflicts_with = "all")]
        detach: bool,
    },
    /// Pause daemon indexing for a repo (keeps its index data)
    Pause { path: String },
    /// Resume daemon indexing for a repo
    Resume { path: String },
    /// Unregister a repository and delete all its index data
    Remove {
        path: String,
        /// Skip the confirmation prompt
        #[arg(long)]
        yes: bool,
    },
    /// Show fleet status (no path) or per-repo detail (with a path)
    Status { path: Option<String> },
    /// Show MCP usage stats from the database
    Usage {
        /// How many days back to include
        #[arg(long, default_value_t = 30)]
        days: i64,
    },
}

/// Scope selector for `config`: exactly one of --global or --repo <path>.
/// There is no cwd default — the repo is always explicit.
#[derive(Args)]
#[group(required = true, multiple = false)]
struct ScopeArgs {
    /// Target the global config (~/.config/muninn/config.toml)
    #[arg(long)]
    global: bool,
    /// Target a repository's .muninn.toml at this path
    #[arg(long, value_name = "PATH")]
    repo: Option<String>,
}

#[derive(Subcommand)]
enum ConfigOp {
    /// Print a key's value (or the whole config if no key given)
    Get {
        key: Option<String>,
        #[command(flatten)]
        scope: ScopeArgs,
    },
    /// Set one or more key=value (non-interactive)
    Set {
        #[arg(value_name = "KEY=VALUE", required = true)]
        assignments: Vec<String>,
        #[command(flatten)]
        scope: ScopeArgs,
    },
    /// Open the config in $EDITOR
    Edit {
        #[command(flatten)]
        scope: ScopeArgs,
    },
    /// Remove a key
    Unset {
        key: String,
        #[command(flatten)]
        scope: ScopeArgs,
    },
}

impl ConfigOp {
    fn scope(&self) -> &ScopeArgs {
        match self {
            ConfigOp::Get { scope, .. }
            | ConfigOp::Set { scope, .. }
            | ConfigOp::Edit { scope }
            | ConfigOp::Unset { scope, .. } => scope,
        }
    }
}

// ── helpers ──────────────────────────────────────────────────────────────────

/// Split a `key=value` argument on the first `=`.
fn parse_assign(s: &str) -> anyhow::Result<(String, String)> {
    let (k, v) = s
        .split_once('=')
        .ok_or_else(|| anyhow::anyhow!("expected key=value, got `{}`", s))?;
    anyhow::ensure!(!k.trim().is_empty(), "empty key in `{}`", s);
    Ok((k.trim().to_string(), v.to_string()))
}

/// Apply `key=value` assignments to TOML content (comment-preserving).
fn apply_assigns(content: &str, assigns: &[String]) -> anyhow::Result<String> {
    let mut out = content.to_string();
    for a in assigns {
        let (k, v) = parse_assign(a)?;
        out = config::toml_set(&out, &k, &v)?;
    }
    Ok(out)
}

#[cfg(unix)]
fn set_owner_only(path: &Path) -> anyhow::Result<()> {
    use std::os::unix::fs::PermissionsExt;
    std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o600))?;
    Ok(())
}
#[cfg(not(unix))]
fn set_owner_only(_path: &Path) -> anyhow::Result<()> {
    Ok(())
}

/// Validate per-repo config content: parse, semantic validate, and the DimFrozen
/// invariant against the repo's registered embedding dimension.
fn validate_repo_cfg(
    content: &str,
    cfg: &GlobalConfig,
    dir_name: &str,
    embedding_dim: u32,
) -> anyhow::Result<()> {
    let rc = RepoConfig::from_toml_str(content)?;
    rc.validate()?;
    let eff = config::EffectiveConfig::merge(cfg, &rc, dir_name);
    let new_dim = muninn_core::embeddings::expected_dimension(&eff.embeddings);
    anyhow::ensure!(
        new_dim == embedding_dim as usize,
        "DimFrozen: this repo uses embedding_dim {embedding_dim} but the edited config \
         yields {new_dim}.\nRemove the [embeddings] section to inherit the global backend, \
         or `muninn remove` + `muninn add` to re-register.",
    );
    Ok(())
}

/// Open `initial_content` in $EDITOR inside a named temp file, validate with
/// `check`, and loop until the user produces a valid file or aborts. Returns the
/// validated content; the caller writes it to the real destination.
fn edit_toml_in_temp(
    initial_content: &str,
    check: impl Fn(&str) -> anyhow::Result<()>,
) -> anyhow::Result<String> {
    let mut tmp = tempfile::Builder::new().suffix(".muninn.toml").tempfile()?;
    tmp.write_all(initial_content.as_bytes())?;
    tmp.flush()?;
    let tmp_path = tmp.path().to_path_buf();

    loop {
        let editor = std::env::var("EDITOR").unwrap_or_else(|_| "vi".to_string());
        std::process::Command::new(&editor).arg(&tmp_path).status()?;

        let content = std::fs::read_to_string(&tmp_path)?;
        match check(&content) {
            Ok(()) => return Ok(content),
            Err(e) => {
                eprintln!("\nConfiguration error: {e}");
                print!("Open editor again to fix it? [Y/n] ");
                std::io::stdout().flush()?;
                let mut line = String::new();
                std::io::stdin().read_line(&mut line)?;
                if !line.trim().is_empty() && !line.trim().eq_ignore_ascii_case("y") {
                    anyhow::bail!("Aborted — changes not applied.");
                }
            }
        }
    }
}

/// Acquire the repo's advisory lock, run a foreground index with a progress bar,
/// then release the lock. Reads the effective config from the repo's
/// `.muninn.toml` on disk (caller must have written it already).
async fn run_foreground_index(
    client: &Client,
    cfg: &GlobalConfig,
    repo_path: &Path,
) -> anyhow::Result<()> {
    let dir_name = repo_path
        .file_name()
        .unwrap_or_default()
        .to_string_lossy()
        .to_string();
    let repo_cfg = RepoConfig::load(repo_path)?;
    let eff = config::EffectiveConfig::merge(cfg, &repo_cfg, &dir_name);

    let embedder: std::sync::Arc<dyn muninn_core::embeddings::EmbeddingBackend> =
        std::sync::Arc::from(muninn_core::embeddings::make_backend(&eff.embeddings));
    let repo_dim = muninn_core::embeddings::expected_dimension(&eff.embeddings);

    let repo = store::get_repo_by_path(client, &repo_path.to_string_lossy())
        .await?
        .ok_or_else(|| anyhow::anyhow!("repo not found in database"))?;

    if repo.embedding_dim as usize != repo_dim {
        anyhow::bail!(
            "DimFrozen: repo '{}' was registered with embedding_dim {} but current config yields {}",
            repo_path.display(),
            repo.embedding_dim,
            repo_dim
        );
    }

    // Acquire the repo's advisory lock. A foreground job always takes priority:
    // if anything already holds it (the daemon, or another CLI), ask the holder
    // to yield — the daemon polls the preempt flag every ~10 s — and block until
    // it releases. No fixed timeout: a dead holder releases the lock when its
    // session ends. The returned connection holds the lock for the index's
    // duration. Spec: Muninn.AdvisoryLock.
    let lock_conn = match store::try_lock(&cfg.database, repo.id).await? {
        Some(conn) => conn,
        None => {
            print!("Index in progress; waiting for the lock…");
            std::io::stdout().flush()?;
            store::request_preempt(client, repo.id).await?;
            let conn = store::lock_blocking(&cfg.database, repo.id).await?;
            println!(" acquired.");
            conn
        }
    };
    store::clear_preempt(client, repo.id).await?;

    // Mark the index owed before doing any work, so an interruption (Ctrl-C,
    // crash, or the advisory lock auto-releasing on a dropped connection) leaves
    // the repo needing a reindex rather than pointing at a half-rebuilt index.
    store::mark_unindexed(client, repo.id).await?;

    println!(
        "Indexing {} ({} dims, {} backend)…",
        repo_path.display(),
        repo_dim,
        format!("{:?}", eff.embeddings.backend).to_lowercase()
    );

    let started = std::time::Instant::now();
    const MAX_PROGRESS_PATH_CHARS: usize = 80;

    let repo_path_for_progress = repo_path.to_path_buf();
    // Race the index against Ctrl-C. On interrupt we just exit: the advisory lock
    // is released when this process's session ends, and indexed_at is already
    // NULL (mark_unindexed above), so the next command resumes a clean reindex.
    // Spec: Muninn.IndexFsm.interrupt.
    let index_result = tokio::select! {
        r = muninn_core::pipeline::index_repo(
            client,
            repo.id,
            repo_path,
            embedder,
            eff.embeddings.batch_size,
            repo_dim,
            &eff.exclude,
            |done, total, file| {
                let rel = file.strip_prefix(&repo_path_for_progress).unwrap_or(file);
                let prefix = format!(
                    "  [{:>width$}/{}] ",
                    done,
                    total,
                    width = total.to_string().len()
                );
                let mut path = rel.display().to_string();
                if path.len() > MAX_PROGRESS_PATH_CHARS {
                    let keep = MAX_PROGRESS_PATH_CHARS.saturating_sub(3);
                    let suffix: String = path.chars().rev().take(keep).collect();
                    path = format!("...{}", suffix.chars().rev().collect::<String>());
                }
                print!("\r\x1b[K{prefix}{path}");
                use std::io::Write;
                let _ = std::io::stdout().flush();
            },
        ) => r,
        _ = tokio::signal::ctrl_c() => {
            println!();
            eprintln!(
                "Interrupted. Index left incomplete — re-run `muninn reindex {p}` to finish it.",
                p = repo_path.display()
            );
            std::process::exit(130);
        }
    };

    if let Err(e) = store::unlock(&lock_conn, repo.id).await {
        eprintln!("warning: advisory unlock failed: {e}");
    }
    let (outcome, skips) = index_result?;

    println!();
    if !skips.is_empty() {
        eprintln!("Skipped {} file(s):", skips.len());
        for s in &skips {
            let rel = s.path.strip_prefix(&repo.path).unwrap_or(&s.path);
            eprintln!("  {}: {}", rel.display(), s.reason);
        }
    }

    let note = match outcome {
        muninn_core::types::BatchOutcome::AllSucceeded => "",
        muninn_core::types::BatchOutcome::SomeSucceeded => " (see skipped files above)",
    };
    println!("Done in {:.1}s.{note}", started.elapsed().as_secs_f64());
    store::notify_repos_changed(client).await?;

    Ok(())
}

// ── config handlers ────────────────────────────────────────────────────────

/// `config <op> --global`: edits the global config file directly, then runs
/// migrations. Does not require an already-loaded config, so it works on a fresh
/// system (alongside `init`).
async fn handle_global_config(op: &ConfigOp) -> anyhow::Result<()> {
    let path = GlobalConfig::config_path();

    if let ConfigOp::Get { key, .. } = op {
        anyhow::ensure!(path.exists(), "no global config at {}", path.display());
        let content = std::fs::read_to_string(&path)?;
        match key {
            Some(k) => match config::toml_get(&content, k)? {
                Some(v) => println!("{v}"),
                None => {
                    eprintln!("(unset) {k}");
                    std::process::exit(1);
                }
            },
            None => print!("{content}"),
        }
        return Ok(());
    }

    let base = if path.exists() {
        std::fs::read_to_string(&path)?
    } else {
        GlobalConfig::template_content().to_string()
    };
    let new = match op {
        ConfigOp::Set { assignments, .. } => apply_assigns(&base, assignments)?,
        ConfigOp::Edit { .. } => {
            println!("Opening {} in $EDITOR…", path.display());
            edit_toml_in_temp(&base, |c| GlobalConfig::from_toml_str(c)?.validate())?
        }
        ConfigOp::Unset { key, .. } => config::toml_unset(&base, key)?,
        ConfigOp::Get { .. } => unreachable!(),
    };
    GlobalConfig::from_toml_str(&new)?.validate()?;
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)?;
    }
    std::fs::write(&path, &new)?;
    set_owner_only(&path)?;
    println!("Updated {}", path.display());

    let cfg = GlobalConfig::from_toml_str(&new)?;
    let mut client = db::connect(&cfg.database).await?;
    db::run_migrations(&mut client).await?;
    Ok(())
}

/// `config <op> --repo <path>`: edits a repo's `.muninn.toml`, then reindexes in
/// the foreground if the content changed or the index is owed.
async fn handle_repo_config(
    client: &Client,
    cfg: &GlobalConfig,
    op: ConfigOp,
) -> anyhow::Result<()> {
    let repo_path = match op.scope().repo.as_deref() {
        Some(p) => muninn_core::repo_resolver::resolve_path(p)?,
        None => unreachable!("global scope handled before client load"),
    };
    let toml_path = repo_path.join(RepoConfig::FILE_NAME);

    if let ConfigOp::Get { key, .. } = &op {
        anyhow::ensure!(
            toml_path.exists(),
            "no {} at {}",
            RepoConfig::FILE_NAME,
            repo_path.display()
        );
        let content = std::fs::read_to_string(&toml_path)?;
        match key {
            Some(k) => match config::toml_get(&content, k)? {
                Some(v) => println!("{v}"),
                None => {
                    eprintln!("(unset) {k}");
                    std::process::exit(1);
                }
            },
            None => print!("{content}"),
        }
        return Ok(());
    }

    let repo = store::get_repo_by_path(client, &repo_path.to_string_lossy())
        .await?
        .ok_or_else(|| {
            anyhow::anyhow!(
                "repo not registered: {} — run `muninn add {}` first",
                repo_path.display(),
                repo_path.display()
            )
        })?;
    let dir_name = repo_path
        .file_name()
        .unwrap_or_default()
        .to_string_lossy()
        .to_string();
    let existing = std::fs::read_to_string(&toml_path)?;

    let new = match &op {
        ConfigOp::Set { assignments, .. } => apply_assigns(&existing, assignments)?,
        ConfigOp::Edit { .. } => {
            println!("Opening {} in $EDITOR…", toml_path.display());
            let cfg2 = cfg.clone();
            let dn = dir_name.clone();
            let edim = repo.embedding_dim;
            edit_toml_in_temp(&existing, move |c| validate_repo_cfg(c, &cfg2, &dn, edim))?
        }
        ConfigOp::Unset { key, .. } => config::toml_unset(&existing, key)?,
        ConfigOp::Get { .. } => unreachable!(),
    };
    validate_repo_cfg(&new, cfg, &dir_name, repo.embedding_dim)?;

    let changed = new != existing;
    if changed {
        std::fs::write(&toml_path, &new)?;
        let rc = RepoConfig::from_toml_str(&new)?;
        let eff = config::EffectiveConfig::merge(cfg, &rc, &dir_name);
        if eff.repo_name != repo.name {
            client
                .execute(
                    "UPDATE repos SET name = $1 WHERE id = $2",
                    &[&eff.repo_name, &repo.id],
                )
                .await?;
            println!("Renamed: {} → {}", repo.name, eff.repo_name);
        }
        println!("Updated {}", toml_path.display());
    }

    // Reindex from DB state, not just the byte-diff: reindex if the config changed
    // OR the index is owed (indexed_at NULL). Spec: Muninn.IndexFsm.configureAction.
    if changed {
        println!("Reindexing…");
        run_foreground_index(client, cfg, &repo_path).await?;
    } else if repo.indexed_at.is_none() {
        println!("Config unchanged, but the index is incomplete — reindexing…");
        run_foreground_index(client, cfg, &repo_path).await?;
    } else {
        println!("No changes; index is up to date.");
    }
    Ok(())
}

// ── main ─────────────────────────────────────────────────────────────────────

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let cli = Cli::parse();

    // Bootstrap-ish commands manage the global config and do NOT require an
    // already-loaded config: `init`, and any `config … --global`.
    match &cli.command {
        Commands::Init { set } => return handle_init(set).await,
        Commands::Config { op } if op.scope().global => return handle_global_config(op).await,
        _ => {}
    }

    let cfg = GlobalConfig::load()?;
    let client = db::connect(&cfg.database).await?;
    // Self-apply migrations so any command works against a DB that hasn't been
    // migrated yet (e.g. right after a binary upgrade). Idempotent.
    let mut migrate_client = db::connect(&cfg.database).await?;
    db::run_migrations(&mut migrate_client).await?;
    drop(migrate_client);

    match cli.command {
        Commands::Config { op } => handle_repo_config(&client, &cfg, op).await?,

        Commands::Add { path, set, no_index } => {
            let repo_path = muninn_core::repo_resolver::resolve_path(&path)?;
            anyhow::ensure!(repo_path.exists(), "path does not exist: {}", repo_path.display());
            anyhow::ensure!(repo_path.is_dir(), "path is not a directory: {}", repo_path.display());
            anyhow::ensure!(
                store::get_repo_by_path(&client, &repo_path.to_string_lossy()).await?.is_none(),
                "repo '{}' is already registered. Use `muninn config set --repo {} k=v` to change it.",
                repo_path.display(),
                path
            );

            let dir_name = repo_path
                .file_name()
                .unwrap_or_default()
                .to_string_lossy()
                .to_string();
            let toml_path = repo_path.join(RepoConfig::FILE_NAME);
            let template = RepoConfig::template_content(&dir_name);

            let content = apply_assigns(&template, &set)?;
            RepoConfig::from_toml_str(&content)?.validate()?;

            std::fs::write(&toml_path, &content)?;
            println!("Created {}", toml_path.display());

            let rc = RepoConfig::from_toml_str(&content)?;
            let eff = config::EffectiveConfig::merge(&cfg, &rc, &dir_name);
            let repo_dim = muninn_core::embeddings::expected_dimension(&eff.embeddings);
            store::register_repo(&client, &repo_path.to_string_lossy(), &eff.repo_name, repo_dim)
                .await?;

            if no_index {
                println!(
                    "Registered (not indexed). Run `muninn reindex {}` to index it.",
                    path
                );
            } else {
                run_foreground_index(&client, &cfg, &repo_path).await?;
            }
        }

        Commands::Reindex { path, all, detach } => {
            if all {
                // Fleet operation: always detached. Visibility via `muninn status`.
                client
                    .execute("UPDATE repos SET indexed_at = NULL", &[])
                    .await?;
                store::notify_repos_changed(&client).await?;
                println!("Marked all repos for reindex. The daemon will pick them up shortly.");
            } else if let Some(p) = path {
                let resolved = muninn_core::repo_resolver::resolve_path(&p)?;
                anyhow::ensure!(
                    store::get_repo_by_path(&client, &resolved.to_string_lossy()).await?.is_some(),
                    "no registered repo found at '{}' — run `muninn status` to see registered repos",
                    resolved.display()
                );
                if detach {
                    client
                        .execute(
                            "UPDATE repos SET indexed_at = NULL WHERE path = $1",
                            &[&resolved.to_string_lossy().as_ref()],
                        )
                        .await?;
                    store::notify_repos_changed(&client).await?;
                    println!(
                        "Marked {} for reindex. The daemon will pick it up shortly.",
                        resolved.display()
                    );
                } else {
                    run_foreground_index(&client, &cfg, &resolved).await?;
                }
            } else {
                eprintln!("Specify a path or --all");
                std::process::exit(1);
            }
        }

        Commands::Pause { path } => {
            let repo_path = muninn_core::repo_resolver::resolve_path(&path)?;
            let repo = store::get_repo_by_path(&client, &repo_path.to_string_lossy())
                .await?
                .ok_or_else(|| anyhow::anyhow!("no registered repo at {}", repo_path.display()))?;
            store::set_paused(&client, repo.id, true).await?;
            store::request_preempt(&client, repo.id).await?;
            store::notify_repos_changed(&client).await?;
            println!(
                "Paused {}. The daemon will stop indexing it; index data is kept.",
                repo_path.display()
            );
        }

        Commands::Resume { path } => {
            let repo_path = muninn_core::repo_resolver::resolve_path(&path)?;
            let repo = store::get_repo_by_path(&client, &repo_path.to_string_lossy())
                .await?
                .ok_or_else(|| anyhow::anyhow!("no registered repo at {}", repo_path.display()))?;
            store::set_paused(&client, repo.id, false).await?;
            store::clear_preempt(&client, repo.id).await?;
            store::notify_repos_changed(&client).await?;
            println!("Resumed {}.", repo_path.display());
        }

        Commands::Remove { path, yes } => {
            let repo_path = muninn_core::repo_resolver::resolve_path(&path)?;
            let toml_path = repo_path.join(RepoConfig::FILE_NAME);
            let repo = store::get_repo_by_path(&client, &repo_path.to_string_lossy()).await?;

            if !toml_path.exists() && repo.is_none() {
                println!(
                    "No {} or registered repo found at: {}",
                    RepoConfig::FILE_NAME,
                    repo_path.display()
                );
                return Ok(());
            }

            // UnregisterSafe: hold the advisory lock across removal so no index
            // runs concurrently and none can start.
            let lock_conn = match &repo {
                Some(r) => {
                    let conn = match store::try_lock(&cfg.database, r.id).await? {
                        Some(conn) => conn,
                        None => {
                            print!("Index in progress; waiting for the lock…");
                            std::io::stdout().flush()?;
                            store::request_preempt(&client, r.id).await?;
                            let conn = store::lock_blocking(&cfg.database, r.id).await?;
                            println!(" acquired.");
                            conn
                        }
                    };
                    store::clear_preempt(&client, r.id).await?;
                    Some((conn, r.id))
                }
                None => None,
            };

            let confirmed = if yes {
                true
            } else {
                let prompt = if toml_path.exists() {
                    format!("Delete {} and remove index data? [y/N] ", toml_path.display())
                } else {
                    format!(
                        "{} not found at {}. Remove index data anyway? [y/N] ",
                        RepoConfig::FILE_NAME,
                        repo_path.display()
                    )
                };
                print!("{prompt}");
                std::io::stdout().flush()?;
                let mut line = String::new();
                std::io::stdin().read_line(&mut line)?;
                line.trim().eq_ignore_ascii_case("y")
            };

            if confirmed {
                if toml_path.exists() {
                    std::fs::remove_file(&toml_path)?;
                }
                if let Some(ref r) = repo {
                    store::delete_repo(&client, r.id).await?;
                    println!("Removed index data for: {}", repo_path.display());
                }
                println!("Removed: {}", repo_path.display());
                store::notify_repos_changed(&client).await?;
            } else {
                println!("Aborted.");
            }

            if let Some((conn, id)) = lock_conn {
                let _ = store::unlock(&conn, id).await;
            }
        }

        Commands::Status { path } => match path {
            None => {
                let repos = store::list_repos(&client).await?;
                println!("Registered repos: {}", repos.len());
                for r in &repos {
                    let status = r
                        .indexed_at
                        .map(|t| format!("indexed {}", t.format("%Y-%m-%d %H:%M UTC")))
                        .unwrap_or_else(|| {
                            if r.ever_indexed {
                                "reindex pending".to_string()
                            } else {
                                "not indexed".to_string()
                            }
                        });
                    let paused = if r.paused { "  [paused]" } else { "" };
                    println!("  {:24}  {}  [{}]{}", r.name, r.path, status, paused);
                }
            }
            Some(p) => {
                let repo_path = muninn_core::repo_resolver::resolve_path(&p)?;
                let r = store::get_repo_by_path(&client, &repo_path.to_string_lossy())
                    .await?
                    .ok_or_else(|| {
                        anyhow::anyhow!("no registered repo at {}", repo_path.display())
                    })?;
                println!("Repo:         {}", r.name);
                println!("Path:         {}", r.path);
                println!(
                    "Indexed:      {}",
                    r.indexed_at.map(|t| t.to_string()).unwrap_or_else(|| "no".to_string())
                );
                println!("Ever indexed: {}", r.ever_indexed);
                println!("Embedding:    {} dims", r.embedding_dim);
                println!("Paused:       {}", r.paused);
                println!("Reindex owed: {}", r.indexed_at.is_none());
            }
        },

        Commands::Usage { days } => {
            anyhow::ensure!(days >= 0, "days must be non-negative");
            let total: i64 = client
                .query_one(
                    "SELECT COUNT(*) FROM mcp_usage \
                     WHERE ts >= now() - ($1::int * interval '1 day')",
                    &[&days],
                )
                .await?
                .get(0);

            println!("MCP usage (last {days} days): {total}");

            let rows = client
                .query(
                    "SELECT tool, COUNT(*) AS count \
                     FROM mcp_usage \
                     WHERE ts >= now() - ($1::int * interval '1 day') \
                     GROUP BY tool \
                     ORDER BY count DESC",
                    &[&days],
                )
                .await?;

            for row in rows {
                let tool: String = row.try_get("tool")?;
                let count: i64 = row.try_get("count")?;
                println!("  {:18} {}", tool, count);
            }
        }

        Commands::Init { .. } => unreachable!("handled before config load"),
    }

    Ok(())
}

/// `muninn init`: bootstrap the global config (template if absent, `--set`/EDITOR
/// to fill it) and run migrations. Idempotent.
async fn handle_init(set: &[String]) -> anyhow::Result<()> {
    let path = GlobalConfig::config_path();
    let existed = path.exists();
    let base = if existed {
        std::fs::read_to_string(&path)?
    } else {
        GlobalConfig::template_content().to_string()
    };

    let content = if !set.is_empty() {
        let new = apply_assigns(&base, set)?;
        GlobalConfig::from_toml_str(&new)?.validate()?;
        new
    } else if !existed {
        println!("Creating {} — opening in $EDITOR…", path.display());
        edit_toml_in_temp(&base, |c| GlobalConfig::from_toml_str(c)?.validate())?
    } else {
        base
    };

    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)?;
    }
    std::fs::write(&path, &content)?;
    set_owner_only(&path)?;
    if !existed || !set.is_empty() {
        println!("Wrote {}", path.display());
    }

    let cfg = GlobalConfig::from_toml_str(&content)?;
    let mut client = db::connect(&cfg.database).await?;
    println!("Applying database migrations…");
    db::run_migrations(&mut client).await?;
    println!("Done. Run `muninn add <repo-path>` to index a repository.");
    Ok(())
}
