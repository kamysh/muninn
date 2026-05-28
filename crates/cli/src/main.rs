use clap::{Parser, Subcommand};
use muninn_core::{config::GlobalConfig, db, store};
use sqlx::{PgPool, Row};
use std::io::Write as _;

#[derive(Parser)]
#[command(name = "muninn", about = "muninn repository index manager")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Create or edit ~/.config/muninn/config.toml and apply DB migrations
    Config,
    /// Register a repository, configure it, and run the initial index
    Add {
        path: String,
        #[arg(long)]
        name: Option<String>,
    },
    /// Edit .muninn.toml, validate it, and reindex if anything changed
    Configure { path: String },
    /// Unregister a repository and delete all its index data
    Remove { path: String },
    /// List registered repositories and their index status
    List,
    /// Mark a repository for re-indexing (daemon picks it up on next run)
    Reindex {
        path: Option<String>,
        #[arg(long, conflicts_with = "path")]
        all: bool,
    },
    /// Show registered repos and index status
    Status,
    /// Show MCP usage stats from the database
    Stats {
        /// How many days back to include
        #[arg(long, default_value_t = 30)]
        days: i64,
    },
}

/// Open `initial_content` in $EDITOR inside a named temp file (`.muninn.toml` suffix for syntax
/// highlighting), validate with `check`, and loop until the user produces a valid file or aborts.
///
/// Returns the validated TOML content.  The caller writes it to the real destination.
fn edit_toml_in_temp(
    initial_content: &str,
    check: impl Fn(&str) -> anyhow::Result<()>,
) -> anyhow::Result<String> {
    let mut tmp = tempfile::Builder::new()
        .suffix(".muninn.toml")
        .tempfile()?;
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

/// Acquire the distributed lock, run a foreground index with a progress bar, then release the
/// lock.  Reads the effective config from the repo's `.muninn.toml` on disk (caller must have
/// written it already).
async fn run_foreground_index(
    pool: &PgPool,
    cfg: &GlobalConfig,
    repo_path: &std::path::Path,
) -> anyhow::Result<()> {
    let dir_name = repo_path
        .file_name()
        .unwrap_or_default()
        .to_string_lossy()
        .to_string();
    let repo_cfg = muninn_core::config::RepoConfig::load(repo_path)?;
    let eff = muninn_core::config::EffectiveConfig::merge(cfg, &repo_cfg, &dir_name);

    let embedder: std::sync::Arc<dyn muninn_core::embeddings::EmbeddingBackend> =
        std::sync::Arc::from(muninn_core::embeddings::make_backend(&eff.embeddings));
    let repo_dim = muninn_core::embeddings::expected_dimension(&eff.embeddings);

    let repo = store::get_repo_by_path(pool, &repo_path.to_string_lossy())
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

    if !store::try_lock_repo(pool, repo.id).await? {
        anyhow::bail!(
            "repo '{}' is currently being indexed by another process. \
             Wait for it to finish, or wait 2 minutes for a stale lock to expire.",
            repo_path.display()
        );
    }

    println!(
        "Indexing {} ({} dims, {} backend)…",
        repo_path.display(),
        repo_dim,
        format!("{:?}", eff.embeddings.backend).to_lowercase()
    );

    let started = std::time::Instant::now();
    const MAX_PROGRESS_PATH_CHARS: usize = 80;

    let pool_hb = pool.clone();
    let hb_repo_id = repo.id;
    let heartbeat = tokio::spawn(async move {
        let mut interval = tokio::time::interval(std::time::Duration::from_secs(60));
        interval.tick().await;
        loop {
            interval.tick().await;
            if let Err(e) = store::pulse_heartbeat(&pool_hb, hb_repo_id).await {
                eprintln!("warning: heartbeat pulse failed: {e}");
            }
        }
    });

    let repo_path_for_progress = repo_path.to_path_buf();
    let index_result = muninn_core::pipeline::index_repo(
        pool,
        repo.id,
        repo_path,
        embedder,
        eff.embeddings.batch_size,
        repo_dim,
        &eff.exclude,
        |done, total, file| {
            let rel = file
                .strip_prefix(&repo_path_for_progress)
                .unwrap_or(file);
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
    )
    .await;

    heartbeat.abort();
    if let Err(e) = store::release_lock(pool, repo.id).await {
        eprintln!("warning: release_lock failed: {e}");
    }
    let (outcome, skips) = index_result?;

    println!();

    // Print skipped files after the progress bar (which would otherwise
    // overwrite them via \r-redraw). Each line has the path relative to the
    // repo root and the full cause chain.
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
    store::notify_repos_changed(pool).await?;

    Ok(())
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let cli = Cli::parse();

    // `muninn config` runs before loading global config — it is the bootstrap command.
    if let Commands::Config = &cli.command {
        let config_path = GlobalConfig::config_path();
        let is_new = !config_path.exists();

        let initial_content = if is_new {
            GlobalConfig::template_content().to_string()
        } else {
            std::fs::read_to_string(&config_path)?
        };

        if is_new {
            println!("Creating: {}", config_path.display());
        }
        println!("Opening in $EDITOR… (save and close to finish)");

        let validated = edit_toml_in_temp(&initial_content, |content| {
            GlobalConfig::from_toml_str(content)?.validate()
        })?;

        if let Some(parent) = config_path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        std::fs::write(&config_path, &validated)?;

        // Restrict permissions to owner-only (config may contain API keys).
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            std::fs::set_permissions(&config_path, std::fs::Permissions::from_mode(0o600))?;
        }

        let cfg = GlobalConfig::from_toml_str(&validated)?;
        let pool = db::connect(&cfg.database).await?;
        println!("Applying database migrations…");
        db::run_migrations(&pool).await?;
        println!("Done. Run `muninn add <repo-path>` to add a repository.");
        return Ok(());
    }

    let cfg = GlobalConfig::load()?;
    let pool = db::connect(&cfg.database).await?;

    match cli.command {
        Commands::Add { path, name } => {
            let repo_path = muninn_core::repo_resolver::resolve_path(&path)?;
            if !repo_path.exists() {
                anyhow::bail!("path does not exist: {}", repo_path.display());
            }
            if !repo_path.is_dir() {
                anyhow::bail!("path is not a directory: {}", repo_path.display());
            }

            // Fail early if the repo is already registered — use `muninn configure` to reconfigure.
            if store::get_repo_by_path(&pool, &repo_path.to_string_lossy())
                .await?
                .is_some()
            {
                anyhow::bail!(
                    "repo '{}' is already registered. \
                     Use `muninn configure {}` to change its configuration.",
                    repo_path.display(),
                    path
                );
            }

            let dir_name = name.unwrap_or_else(|| {
                repo_path
                    .file_name()
                    .unwrap_or_default()
                    .to_string_lossy()
                    .to_string()
            });
            let toml_path = repo_path.join(muninn_core::config::RepoConfig::FILE_NAME);
            let template = muninn_core::config::RepoConfig::template_content(&dir_name);

            println!("Opening in $EDITOR… (save and close to finish)");

            let validated_content = edit_toml_in_temp(&template, |content| {
                muninn_core::config::RepoConfig::from_toml_str(content)?.validate()
            })
            .map_err(|e| {
                anyhow::anyhow!("{} — {} not registered.", e, repo_path.display())
            })?;

            std::fs::write(&toml_path, &validated_content)?;
            println!("Created: {}", toml_path.display());

            let repo_cfg = muninn_core::config::RepoConfig::from_toml_str(&validated_content)?;
            let eff = muninn_core::config::EffectiveConfig::merge(&cfg, &repo_cfg, &dir_name);
            let repo_dim = muninn_core::embeddings::expected_dimension(&eff.embeddings);

            store::register_repo(
                &pool,
                &repo_path.to_string_lossy(),
                &eff.repo_name,
                repo_dim,
            )
            .await?;

            run_foreground_index(&pool, &cfg, &repo_path).await?;
        }

        Commands::Configure { path } => {
            let repo_path = muninn_core::repo_resolver::resolve_path(&path)?;
            let toml_path = repo_path.join(muninn_core::config::RepoConfig::FILE_NAME);

            if !toml_path.exists() {
                anyhow::bail!(
                    "no {} found at {} — run `muninn add {}` first",
                    muninn_core::config::RepoConfig::FILE_NAME,
                    repo_path.display(),
                    path
                );
            }

            let repo = store::get_repo_by_path(&pool, &repo_path.to_string_lossy())
                .await?
                .ok_or_else(|| {
                    anyhow::anyhow!(
                        "repo not found in database — run `muninn add {}` first",
                        repo_path.display()
                    )
                })?;

            let dir_name = repo_path
                .file_name()
                .unwrap_or_default()
                .to_string_lossy()
                .to_string();
            let existing_content = std::fs::read_to_string(&toml_path)?;

            println!("Opening in $EDITOR… (save and close to finish)");

            let validated_content = edit_toml_in_temp(&existing_content, |content| {
                let rc = muninn_core::config::RepoConfig::from_toml_str(content)?;
                rc.validate()?;
                let eff = muninn_core::config::EffectiveConfig::merge(&cfg, &rc, &dir_name);
                let new_dim = muninn_core::embeddings::expected_dimension(&eff.embeddings);
                if new_dim != repo.embedding_dim as usize {
                    anyhow::bail!(
                        "DimFrozen: this repo uses embedding_dim {} but the edited config \
                         yields {}.\nRemove the [embeddings] section to inherit the global \
                         backend, or:\n  muninn remove {path}\n  muninn add    {path}",
                        repo.embedding_dim,
                        new_dim
                    );
                }
                Ok(())
            })?;

            if validated_content == existing_content {
                println!("No changes.");
                return Ok(());
            }

            std::fs::write(&toml_path, &validated_content)?;

            let repo_cfg = muninn_core::config::RepoConfig::from_toml_str(&validated_content)?;
            let eff = muninn_core::config::EffectiveConfig::merge(&cfg, &repo_cfg, &dir_name);

            if eff.repo_name != repo.name {
                sqlx::query("UPDATE repos SET name = $1 WHERE id = $2")
                    .bind(&eff.repo_name)
                    .bind(repo.id)
                    .execute(&pool)
                    .await?;
                println!("Renamed: {} → {}", repo.name, eff.repo_name);
            }

            println!("Saved. Reindexing…");
            run_foreground_index(&pool, &cfg, &repo_path).await?;
        }

        Commands::Remove { path } => {
            let repo_path = muninn_core::repo_resolver::resolve_path(&path)?;
            let toml_path = repo_path.join(muninn_core::config::RepoConfig::FILE_NAME);
            let repo =
                store::get_repo_by_path(&pool, &repo_path.to_string_lossy()).await?;

            if !toml_path.exists() && repo.is_none() {
                println!(
                    "No {} or registered repo found at: {}",
                    muninn_core::config::RepoConfig::FILE_NAME,
                    repo_path.display()
                );
                return Ok(());
            }

            // UnregisterSafe: refuse if an indexer process is actively holding the lock.
            if let Some(ref r) = repo {
                if r.is_lock_live() {
                    anyhow::bail!(
                        "repo '{}' is currently being indexed (live lock held). \
                         Wait for indexing to complete or stop the indexer before removing.",
                        repo_path.display()
                    );
                }
            }

            let prompt = if toml_path.exists() {
                format!(
                    "Delete {} and remove index data? [y/N] ",
                    toml_path.display()
                )
            } else {
                format!(
                    "{} not found at {}. Remove index data anyway? [y/N] ",
                    muninn_core::config::RepoConfig::FILE_NAME,
                    repo_path.display()
                )
            };
            print!("{prompt}");
            use std::io::Write;
            std::io::stdout().flush()?;
            let mut line = String::new();
            std::io::stdin().read_line(&mut line)?;

            if line.trim().eq_ignore_ascii_case("y") {
                if toml_path.exists() {
                    std::fs::remove_file(&toml_path)?;
                }
                if let Some(repo) = repo {
                    store::delete_repo(&pool, repo.id).await?;
                    println!("Removed index data for: {}", repo_path.display());
                }
                println!("Removed: {}", repo_path.display());
                store::notify_repos_changed(&pool).await?;
            } else {
                println!("Aborted.");
            }
        }

        Commands::List => {
            let repos = store::list_repos(&pool).await?;
            if repos.is_empty() {
                println!("No repositories registered.");
            } else {
                for repo in repos {
                    let status = repo
                        .indexed_at
                        .map(|t| format!("indexed {}", t.format("%Y-%m-%d %H:%M UTC")))
                        .unwrap_or_else(|| "not indexed".to_string());
                    println!("{:24}  {}  [{}]", repo.name, repo.path, status);
                }
            }
        }

        Commands::Reindex { path, all } => {
            if all {
                sqlx::query("UPDATE repos SET indexed_at = NULL")
                    .execute(&pool)
                    .await?;
                store::notify_repos_changed(&pool).await?;
                println!("Marked all repos for reindex. The daemon will pick them up shortly.");
            } else if let Some(p) = path {
                let resolved = muninn_core::repo_resolver::resolve_path(&p)?;
                let result =
                    sqlx::query("UPDATE repos SET indexed_at = NULL WHERE path = $1")
                        .bind(resolved.to_string_lossy().as_ref())
                        .execute(&pool)
                        .await?;
                if result.rows_affected() == 0 {
                    anyhow::bail!(
                        "no registered repo found at '{}' — run `muninn list` to see registered repos",
                        resolved.display()
                    );
                }
                store::notify_repos_changed(&pool).await?;
                println!(
                    "Marked {} for reindex. The daemon will pick it up shortly.",
                    resolved.display()
                );
            } else {
                eprintln!("Specify a path or --all");
                std::process::exit(1);
            }
        }

        Commands::Status => {
            let repos = store::list_repos(&pool).await?;
            println!("Registered repos: {}", repos.len());
            for r in &repos {
                let status = r
                    .indexed_at
                    .map(|t| t.to_string())
                    .unwrap_or_else(|| "unindexed".to_string());
                println!("  {} — {} — {}", r.name, r.path, status);
            }
        }

        Commands::Stats { days } => {
            if days < 0 {
                anyhow::bail!("days must be non-negative");
            }
            let total = sqlx::query_scalar::<_, i64>(
                "SELECT COUNT(*) FROM mcp_usage
                 WHERE ts >= now() - ($1::int * interval '1 day')",
            )
            .bind(days)
            .fetch_one(&pool)
            .await?;

            println!("MCP usage (last {days} days): {total}");

            let rows = sqlx::query(
                "SELECT tool, COUNT(*) AS count
                 FROM mcp_usage
                 WHERE ts >= now() - ($1::int * interval '1 day')
                 GROUP BY tool
                 ORDER BY count DESC",
            )
            .bind(days)
            .fetch_all(&pool)
            .await?;

            for row in rows {
                let tool: String = row.try_get("tool")?;
                let count: i64 = row.try_get("count")?;
                println!("  {:18} {}", tool, count);
            }
        }

        Commands::Config => unreachable!("handled before loading config"),
    }

    Ok(())
}
