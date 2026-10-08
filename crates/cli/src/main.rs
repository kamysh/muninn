use clap::{Args, Parser, Subcommand};
use muninn_core::{
    config::{self, GlobalConfig},
    db, store,
};
use std::io::Write as _;
use std::path::Path;
use tokio_postgres::Client;
mod readonly;
mod removal;
mod tui;
mod writes;

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
        /// Initial key=value settings (non-interactive); omit to open the TUI
        #[arg(value_name = "KEY=VALUE")]
        set: Vec<String>,
    },
    /// Configure a family in the TUI/JSON, or edit global settings with --global
    Config {
        #[command(flatten)]
        scope: ScopeArgs,
        #[command(subcommand)]
        op: Option<ConfigOp>,
        /// Selected checkout/directory for family policy operations
        #[arg(value_name = "PATH", conflicts_with = "ScopeArgs")]
        path: Option<std::path::PathBuf>,
        #[arg(long, requires = "path")]
        json: bool,
        /// Validate a complete candidate from stdin without saving
        #[arg(long, value_name = "-", value_parser = ["-"], requires = "json", conflicts_with = "apply")]
        check: Option<String>,
        /// Atomically replace policy from stdin using expected family/revision
        #[arg(long, value_name = "-", value_parser = ["-"], requires = "json")]
        apply: Option<String>,
    },
    /// Bounded metadata inventory; never registers, migrates or starts indexing
    Preflight {
        path: std::path::PathBuf,
        #[arg(long, required = true)]
        json: bool,
    },
    /// Configure/register a family interactively or with --json
    Add {
        /// Repository path
        path: std::path::PathBuf,
        /// Database-backed registration only; never starts indexing
        #[arg(long)]
        json: bool,
        /// Initial complete JSON policy from stdin (new family or incomplete retry)
        #[arg(long, value_name = "-", value_parser = ["-"], requires = "json")]
        input: Option<String>,
    },
    /// Explicitly enable a configured family and run its index in the foreground
    Start {
        path: std::path::PathBuf,
        #[arg(long)]
        json: bool,
        /// Guarded start request with expected_family_id and expected_revision
        #[arg(long, value_name = "-", value_parser = ["-"], requires = "json")]
        input: Option<String>,
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

/// Global settings are explicit; family policy uses a positional PATH.
#[derive(Args)]
#[group(multiple = false)]
struct ScopeArgs {
    /// Target the global config (~/.config/muninn/config.toml)
    #[arg(long, global = true)]
    global: bool,
}

#[derive(Subcommand)]
enum ConfigOp {
    /// Print a key's value (or the whole config if no key given)
    Get { key: Option<String> },
    /// Set one or more key=value (non-interactive)
    Set {
        #[arg(value_name = "KEY=VALUE", required = true)]
        assignments: Vec<String>,
    },
    /// Open the global configuration TUI
    Edit,
    /// Remove a key
    Unset { key: String },
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

/// Acquire the repo's advisory lock, run a foreground index with a progress bar,
/// then release the lock. Stored-policy families use the DB; unbound registrations
/// use global defaults.
async fn run_foreground_index(
    client: &mut Client,
    cfg: &GlobalConfig,
    repo_path: &Path,
) -> anyhow::Result<()> {
    let family = muninn_core::worktrees::registered_family(client, repo_path)
        .await?
        .ok_or_else(|| anyhow::anyhow!("repo not found in database"))?;
    let root =
        muninn_core::family_policy::runtime::root(client, family.id, Path::new(&family.path))
            .await?;
    let repo_path = root.as_path();
    let (eff, policy) =
        muninn_core::family_policy::runtime::config(client, family.id, repo_path, cfg).await?;
    anyhow::ensure!(
        !policy.as_ref().is_some_and(|p| !p.indexing_enabled),
        "Use muninn start PATH for the first index"
    );

    let embedder: std::sync::Arc<dyn muninn_core::embeddings::EmbeddingBackend> =
        std::sync::Arc::from(muninn_core::embeddings::make_backend(&eff.embeddings));
    let repo_dim = muninn_core::embeddings::expected_dimension(&eff.embeddings);

    let repo = family;

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

    // Bring this repo's schema current via kryzhen before touching its table —
    // covers repos registered on an older version of the schema template.
    // Done as its own short &mut borrow, before index_repo (which only needs
    // &Client and runs concurrently with preempt polling below).
    muninn_core::db::run_repo_migrations(client, &store::repo_schema(repo.id)).await?;

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
            &eff.vendor,
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

fn global_template() -> anyhow::Result<String> {
    let content = config::toml_set(
        GlobalConfig::template_content(),
        "database.user",
        &serde_json::to_string(&GlobalConfig::default().database.user)?,
    )?;
    let content = config::toml_unset(&content, "embeddings.api_key")?;
    config::toml_unset(&content, "embeddings.cache_dir")
}

fn persist_global(path: &Path, existed: bool, base: &str, content: &str) -> anyhow::Result<()> {
    anyhow::ensure!(
        if existed {
            std::fs::read_to_string(path)? == base
        } else {
            !path.exists()
        },
        "Global configuration changed while editing; reopen it before saving"
    );
    let parent = path
        .parent()
        .ok_or_else(|| anyhow::anyhow!("configuration path has no parent"))?;
    std::fs::create_dir_all(parent)?;
    let mut file = tempfile::NamedTempFile::new_in(parent)?;
    set_owner_only(file.path())?;
    file.write_all(content.as_bytes())?;
    file.as_file().sync_all()?;
    file.persist(path)?;
    Ok(())
}

// ── config handlers ────────────────────────────────────────────────────────

/// Global interactive creation/editing and noninteractive updates share
/// validation, owner-only persistence and database preparation after Save.
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

    let existed = path.exists();
    anyhow::ensure!(
        existed || matches!(op, ConfigOp::Edit),
        "no global config at {}; run muninn init first",
        path.display()
    );
    let base = if existed {
        std::fs::read_to_string(&path)?
    } else {
        global_template()?
    };
    let new = match op {
        ConfigOp::Set { assignments, .. } => apply_assigns(&base, assignments)?,
        ConfigOp::Edit => {
            let Some(content) = tui::global::run(&base, &path)? else {
                return Ok(());
            };
            content
        }
        ConfigOp::Unset { key, .. } => config::toml_unset(&base, key)?,
        ConfigOp::Get { .. } => unreachable!(),
    };
    GlobalConfig::from_toml_str(&new)?.validate()?;
    persist_global(&path, existed, &base, &new)?;
    println!("Updated {}", path.display());

    let cfg = GlobalConfig::from_toml_str(&new)?;
    let mut client = db::connect(&cfg.database).await?;
    db::run_migrations(&mut client).await?;
    Ok(())
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let cli = match Cli::try_parse() {
        Ok(cli) => cli,
        Err(error) => {
            if error.use_stderr() && std::env::args_os().any(|arg| arg == "--json") {
                readonly::finish(Err(readonly::error(
                    "invalid_request",
                    "invalid command arguments; see command --help",
                )));
            }
            error.exit();
        }
    };

    // Family TUI/JSON routes MUST return before legacy migration/indexing startup.
    match &cli.command {
        Commands::Start { path, json, input } => {
            let result = writes::start(path, input.is_some()).await;
            if *json {
                readonly::finish(result);
            }
            let data = result?;
            println!(
                "Indexing enabled. Pass completed: {}. Skipped: {}.",
                data["indexing_completed"], data["skipped_checkouts_or_files"]
            );
            return Ok(());
        }
        Commands::Add {
            path, json: false, ..
        } => {
            return tui::run(path, true).await;
        }
        Commands::Config {
            path: Some(path),
            json: false,
            op: None,
            ..
        } => {
            return tui::run(path, false).await;
        }
        Commands::Config {
            path: Some(_),
            json: false,
            op: Some(_),
            ..
        } => {
            anyhow::bail!("Global config operations cannot be combined with a family PATH");
        }
        Commands::Add {
            path,
            json: true,
            input,
            ..
        } => {
            readonly::finish(writes::add(path, input.is_some()).await);
        }
        Commands::Config {
            path: Some(path),
            json: true,
            check,
            apply,
            op,
            ..
        } => {
            if op.is_some() {
                readonly::finish(Err(readonly::error(
                    "invalid_request",
                    "global operations cannot be combined with family JSON",
                )));
            }
            if apply.is_some() {
                readonly::finish(writes::apply(path).await);
            }
            let mode = if check.is_some() {
                readonly::Mode::Check
            } else {
                readonly::Mode::Inspect
            };
            readonly::finish(readonly::run(path, mode).await);
        }
        Commands::Preflight { path, .. } => {
            readonly::finish(readonly::run(path, readonly::Mode::Preflight).await)
        }
        Commands::Config { scope, .. } => {
            anyhow::ensure!(
                scope.global,
                "use config PATH for family policy, or config --global"
            );
        }
        _ => {}
    }

    // Bootstrap-ish commands manage the global config and do NOT require an
    // already-loaded config: `init`, and any `config … --global`.
    match &cli.command {
        Commands::Init { set } => return handle_init(set).await,
        Commands::Config { scope, op, .. } if scope.global => {
            return handle_global_config(op.as_ref().unwrap_or(&ConfigOp::Edit)).await
        }
        _ => {}
    }

    let cfg = GlobalConfig::load()?;
    let mut client = db::connect(&cfg.database).await?;
    // Self-apply migrations so any command works against a DB that hasn't been
    // migrated yet (e.g. right after a binary upgrade). Idempotent.
    let mut migrate_client = db::connect(&cfg.database).await?;
    db::run_migrations(&mut migrate_client).await?;
    drop(migrate_client);

    match cli.command {
        Commands::Config { .. }
        | Commands::Preflight { .. }
        | Commands::Start { .. }
        | Commands::Add { .. } => {
            unreachable!("family/global commands dispatched before migrations")
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
                let family = muninn_core::worktrees::registered_family(&client, &resolved)
                    .await?
                    .ok_or_else(|| {
                        anyhow::anyhow!("no registered repository for {}", resolved.display())
                    })?;
                let resolved = std::path::PathBuf::from(family.path);
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
                    run_foreground_index(&mut client, &cfg, &resolved).await?;
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
            let repo = store::get_repo_by_path(&client, &repo_path.to_string_lossy()).await?;

            let target = removal::Target {
                path: &repo_path,
                registered_name: repo.as_ref().map(|r| r.name.as_str()),
            };
            let confirmed = removal::confirm(
                &target,
                yes,
                &mut std::io::stdin().lock(),
                &mut std::io::stdout().lock(),
            )?;
            if !confirmed {
                return Ok(());
            }

            // Only an approved removal may wait for indexing or preempt it.
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

            if let Some(ref r) = repo {
                store::delete_repo(&mut client, r.id).await?;
                println!("Removed index data for: {}", repo_path.display());
            }
            println!("Removed: {}", repo_path.display());
            store::notify_repos_changed(&client).await?;

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
                    r.indexed_at
                        .map(|t| t.to_string())
                        .unwrap_or_else(|| "no".to_string())
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
                     WHERE ts >= now() - ($1::bigint * interval '1 day')",
                    &[&days],
                )
                .await?
                .get(0);

            println!("MCP usage (last {days} days): {total}");

            let rows = client
                .query(
                    "SELECT tool, COUNT(*) AS count \
                     FROM mcp_usage \
                     WHERE ts >= now() - ($1::bigint * interval '1 day') \
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

/// `muninn init`: bootstrap the global config (TUI or noninteractive assignments)
/// and run migrations after an explicit save.
async fn handle_init(set: &[String]) -> anyhow::Result<()> {
    let path = GlobalConfig::config_path();
    let existed = path.exists();
    let base = if existed {
        std::fs::read_to_string(&path)?
    } else {
        global_template()?
    };

    let content = if !set.is_empty() {
        let new = apply_assigns(&base, set)?;
        GlobalConfig::from_toml_str(&new)?.validate()?;
        new
    } else {
        let Some(content) = tui::global::run(&base, &path)? else {
            return Ok(());
        };
        content
    };

    persist_global(&path, existed, &base, &content)?;
    if !existed || !set.is_empty() {
        println!("Wrote {}", path.display());
    }

    let cfg = GlobalConfig::from_toml_str(&content)?;
    let mut client = db::connect(&cfg.database).await?;
    println!("Applying database migrations…");
    db::run_migrations(&mut client).await?;
    println!("Done. Run `muninn add <repo-path>` to configure a repository.");
    Ok(())
}

#[cfg(test)]
mod command_tests {
    use super::*;
    #[test]
    fn native_family_forms_parse_without_legacy_arguments() {
        assert!(matches!(
            Cli::try_parse_from(["muninn", "config", "/repo"])
                .unwrap()
                .command,
            Commands::Config {
                path: Some(_),
                json: false,
                op: None,
                ..
            }
        ));
        assert!(matches!(
            Cli::try_parse_from(["muninn", "add", "/repo"])
                .unwrap()
                .command,
            Commands::Add { json: false, .. }
        ));
    }
    #[test]
    fn family_read_commands_and_global_config_parse_without_overlap() {
        for args in [
            vec!["muninn", "config", "/repo", "--json"],
            vec!["muninn", "config", "/repo", "--check", "-", "--json"],
            vec!["muninn", "config", "/repo", "--apply", "-", "--json"],
        ] {
            assert!(matches!(
                Cli::try_parse_from(args).unwrap().command,
                Commands::Config {
                    path: Some(_),
                    json: true,
                    op: None,
                    ..
                }
            ));
        }
        assert!(matches!(
            Cli::try_parse_from(["muninn", "preflight", "/repo", "--json"])
                .unwrap()
                .command,
            Commands::Preflight { .. }
        ));
        for args in [
            vec!["muninn", "config", "--global", "get"],
            vec!["muninn", "config", "get", "--global"],
        ] {
            assert!(matches!(
                Cli::try_parse_from(args).unwrap().command,
                Commands::Config {
                    path: None,
                    json: false,
                    op: Some(_),
                    ..
                }
            ));
        }
    }
    #[test]
    fn global_tui_command_parses_without_a_family_path() {
        for args in [
            vec!["muninn", "config", "--global"],
            vec!["muninn", "config", "edit", "--global"],
        ] {
            assert!(matches!(
                Cli::try_parse_from(args).unwrap().command,
                Commands::Config { path: None, .. }
            ));
        }
    }
    #[test]
    fn incomplete_or_mixed_json_forms_are_rejected_by_parser() {
        for args in [
            vec!["muninn", "config", "--json"],
            vec!["muninn", "config", "/repo", "--json", "--global"],
            vec![
                "muninn", "config", "/repo", "--json", "--apply", "-", "--check", "-",
            ],
            vec!["muninn", "add", "/repo", "--json", "--no-index"],
            vec!["muninn", "add", "/repo", "--json", "name=legacy"],
            vec!["muninn", "add", "/repo", "--input", "-"],
            vec![
                "muninn",
                "config",
                "/repo",
                "--json",
                "--check",
                "file.json",
            ],
            vec!["muninn", "preflight", "/repo"],
        ] {
            assert!(
                Cli::try_parse_from(args.clone()).is_err(),
                "accepted {args:?}"
            );
        }
    }

    #[test]
    fn registration_uses_family_forms_only() {
        for args in [
            vec!["muninn", "add", "/repo", "--json"],
            vec!["muninn", "add", "/repo", "--json", "--input", "-"],
        ] {
            assert!(matches!(
                Cli::try_parse_from(args).unwrap().command,
                Commands::Add { json: true, .. }
            ));
        }
        for args in [
            vec!["muninn", "add", "/repo", "name=example"],
            vec!["muninn", "add", "/repo", "--no-index"],
            vec!["muninn", "config", "set", "--repo", "/repo", "name=example"],
            vec!["muninn", "config", "--repo", "/repo", "edit"],
        ] {
            assert!(Cli::try_parse_from(args).is_err());
        }
    }
}
