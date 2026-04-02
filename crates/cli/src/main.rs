use clap::{Parser, Subcommand};
use muninn_core::{config::GlobalConfig, db, store};
use sqlx::Row;

#[derive(Parser)]
#[command(name = "muninn", about = "muninn repository index manager")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum ConfigCommands {
    /// Create ~/.config/muninn/config.toml and open it for editing
    Init,
}

#[derive(Subcommand)]
enum Commands {
    /// Manage global configuration
    Config {
        #[command(subcommand)]
        cmd: ConfigCommands,
    },
    /// Create muninn.toml in a repository and open it for editing
    Register {
        path: String,
        #[arg(long)]
        name: Option<String>,
    },
    /// Run the initial index of a repository (foreground, with progress)
    Index { path: String },
    /// Unregister a repository and delete its index data
    Unregister { path: String },
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

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let cli = Cli::parse();

    // Config subcommand runs before loading global config (it's the bootstrap command).
    if let Commands::Config { cmd } = &cli.command {
        match cmd {
            ConfigCommands::Init => {
                let path = muninn_core::config::GlobalConfig::create_template()?;
                println!("Created: {}", path.display());
                println!("Opening in $EDITOR… (save and close to finish)");
                let editor = std::env::var("EDITOR").unwrap_or_else(|_| "vi".to_string());
                std::process::Command::new(&editor).arg(&path).status()?;
                println!("Done. Run `muninn register <repo-path>` to add a repository.");
                return Ok(());
            }
        }
    }

    let cfg = GlobalConfig::load()?;
    let pool = db::connect(&cfg.database).await?;

    match cli.command {
        Commands::Register { path, name } => {
            let repo_path = muninn_core::repo_resolver::resolve_path(&path)?;
            if !repo_path.exists() {
                anyhow::bail!("path does not exist: {}", repo_path.display());
            }
            if !repo_path.is_dir() {
                anyhow::bail!("path is not a directory: {}", repo_path.display());
            }
            let dir_name = name.unwrap_or_else(|| {
                repo_path
                    .file_name()
                    .unwrap_or_default()
                    .to_string_lossy()
                    .to_string()
            });
            let toml_path = muninn_core::config::RepoConfig::create_template(&repo_path, &dir_name)?;
            println!("Created: {}", toml_path.display());
            println!("Opening in $EDITOR… (save and close to finish)");
            let editor = std::env::var("EDITOR").unwrap_or_else(|_| "vi".to_string());
            std::process::Command::new(&editor)
                .arg(&toml_path)
                .status()?;
            println!("Done. Run `muninn index {}` when ready to index.", path);
        }

        Commands::Index { path } => {
            let repo_path = muninn_core::repo_resolver::resolve_path(&path)?;
            if !repo_path.exists() {
                anyhow::bail!("path does not exist: {}", repo_path.display());
            }
            if !repo_path.is_dir() {
                anyhow::bail!("path is not a directory: {}", repo_path.display());
            }
            let toml_path = repo_path.join(muninn_core::config::RepoConfig::FILE_NAME);
            if !toml_path.exists() {
                anyhow::bail!(
                    "no muninn.toml found at {} — run `muninn register {}` first",
                    repo_path.display(), repo_path.display()
                );
            }

            let dir_name = repo_path
                .file_name()
                .unwrap_or_default()
                .to_string_lossy()
                .to_string();
            let repo_cfg = muninn_core::config::RepoConfig::load(&repo_path)?;
            let eff = muninn_core::config::EffectiveConfig::merge(&cfg, &repo_cfg, &dir_name);

            let embedder: std::sync::Arc<dyn muninn_core::embeddings::EmbeddingBackend> =
                std::sync::Arc::from(muninn_core::embeddings::make_backend(&eff.embeddings));
            let repo_dim = muninn_core::embeddings::expected_dimension(&eff.embeddings);

            // Register in DB (idempotent — safe to call even if already registered)
            let repo = store::register_repo(
                &pool,
                &repo_path.to_string_lossy(),
                &eff.repo_name,
                repo_dim,
            )
            .await?;

            println!("Indexing {} ({} dims, {} backend)…",
                repo_path.display(), repo_dim,
                format!("{:?}", eff.embeddings.backend).to_lowercase()
            );

            let started = std::time::Instant::now();
            const MAX_PROGRESS_PATH_CHARS: usize = 80;

            let repo_path_for_progress = repo_path.clone();
            let outcome = muninn_core::pipeline::index_repo(
                &pool,
                repo.id,
                &repo_path,
                embedder,
                eff.embeddings.batch_size,
                repo_dim,
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
                    let line = format!("{prefix}{path}");
                    print!("\r\x1b[K{line}");
                    use std::io::Write;
                    let _ = std::io::stdout().flush();
                },
            )
            .await?;

            println!();
            let outcome_note = match outcome {
                muninn_core::types::BatchOutcome::AllSucceeded  => "",
                muninn_core::types::BatchOutcome::SomeSucceeded => " (some files skipped — see warnings above)",
            };
            println!("Done in {:.1}s.{}", started.elapsed().as_secs_f64(), outcome_note);
            store::notify_repos_changed(&pool).await?;
        }

        Commands::Unregister { path } => {
            let repo_path = muninn_core::repo_resolver::resolve_path(&path)?;
            let toml_path = repo_path.join(muninn_core::config::RepoConfig::FILE_NAME);
            let repo = muninn_core::store::get_repo_by_path(
                &pool, &repo_path.to_string_lossy()
            ).await?;
            if !toml_path.exists() && repo.is_none() {
                println!("No muninn.toml or registered repo found at: {}", repo_path.display());
                return Ok(());
            }
            let prompt = if toml_path.exists() {
                format!("Delete {} and remove index data? [y/N] ", toml_path.display())
            } else {
                format!("muninn.toml not found at {}. Remove index data anyway? [y/N] ", repo_path.display())
            };
            print!("{}", prompt);
            use std::io::Write;
            std::io::stdout().flush()?;
            let mut line = String::new();
            std::io::stdin().read_line(&mut line)?;
            if line.trim().eq_ignore_ascii_case("y") {
                if toml_path.exists() {
                    std::fs::remove_file(&toml_path)?;
                }
                if let Some(repo) = repo {
                    muninn_core::store::delete_repo(&pool, repo.id).await?;
                    println!("Removed index data for: {}", repo_path.display());
                }
                println!("Unregistered: {}", repo_path.display());
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
                    let status = repo.indexed_at
                        .map(|t| format!("indexed {}", t.format("%Y-%m-%d %H:%M UTC")))
                        .unwrap_or_else(|| "not indexed".to_string());
                    println!("{:24}  {}  [{}]", repo.name, repo.path, status);
                }
            }
        }

        Commands::Reindex { path, all } => {
            if all {
                sqlx::query("UPDATE repos SET indexed_at = NULL")
                    .execute(&pool).await?;
                store::notify_repos_changed(&pool).await?;
                println!("Marked all repos for reindex. The daemon will pick them up shortly.");
            } else if let Some(p) = path {
                let resolved = muninn_core::repo_resolver::resolve_path(&p)?;
                sqlx::query("UPDATE repos SET indexed_at = NULL WHERE path = $1")
                    .bind(resolved.to_string_lossy().as_ref())
                    .execute(&pool).await?;
                store::notify_repos_changed(&pool).await?;
                println!("Marked {} for reindex. The daemon will pick it up shortly.", resolved.display());
            } else {
                eprintln!("Specify a path or --all");
                std::process::exit(1);
            }
        }

        Commands::Status => {
            let repos = store::list_repos(&pool).await?;
            println!("Registered repos: {}", repos.len());
            for r in &repos {
                let status = r.indexed_at
                    .map(|t| t.to_string())
                    .unwrap_or_else(|| "unindexed".to_string());
                println!("  {} — {}", r.name, status);
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

            println!("MCP usage (last {} days): {}", days, total);

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

        Commands::Config { .. } => unreachable!("handled before loading config"),
    }

    Ok(())
}
