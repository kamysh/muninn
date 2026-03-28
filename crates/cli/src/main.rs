use clap::{Parser, Subcommand};
use muninn_core::{config::GlobalConfig, db, store};

#[derive(Parser)]
#[command(name = "muninn", about = "muninn repository index manager")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
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
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let cli = Cli::parse();
    let cfg = GlobalConfig::load()?;
    let pool = db::connect(&cfg.database.dsn()).await?;

    match cli.command {
        Commands::Register { path, name } => {
            let repo_path = std::path::Path::new(&path);
            if !repo_path.exists() {
                anyhow::bail!("path does not exist: {}", path);
            }
            let dir_name = name.unwrap_or_else(|| {
                repo_path
                    .file_name()
                    .unwrap_or_default()
                    .to_string_lossy()
                    .to_string()
            });
            let toml_path = muninn_core::config::RepoConfig::create_template(repo_path, &dir_name)?;
            println!("Created: {}", toml_path.display());
            println!("Opening in $EDITOR… (save and close to finish)");
            let editor = std::env::var("EDITOR").unwrap_or_else(|_| "vi".to_string());
            std::process::Command::new(&editor)
                .arg(&toml_path)
                .status()?;
            println!("Done. Run `muninn index {}` when ready to index.", path);
        }

        Commands::Index { path } => {
            let repo_path = std::path::Path::new(&path);
            if !repo_path.exists() {
                anyhow::bail!("path does not exist: {}", path);
            }
            let toml_path = repo_path.join(muninn_core::config::RepoConfig::FILE_NAME);
            if !toml_path.exists() {
                anyhow::bail!(
                    "no muninn.toml found at {}  — run `muninn register {}` first",
                    path, path
                );
            }

            let dir_name = repo_path
                .file_name()
                .unwrap_or_default()
                .to_string_lossy()
                .to_string();
            let repo_cfg = muninn_core::config::RepoConfig::load(repo_path)?;
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

            muninn_core::pipeline::index_repo(
                &pool,
                repo.id,
                repo_path,
                embedder,
                eff.embeddings.batch_size,
                repo_dim,
                |done, total, file| {
                    let rel = file.strip_prefix(repo_path).unwrap_or(file);
                    print!("\r  [{:>width$}/{}] {}",
                        done, total, rel.display(),
                        width = total.to_string().len()
                    );
                    use std::io::Write;
                    let _ = std::io::stdout().flush();
                },
            )
            .await?;

            println!();
            println!("Done in {:.1}s.", started.elapsed().as_secs_f64());
            println!("Start or restart muninn-index to begin watching for changes.");
        }

        Commands::Unregister { path } => {
            let toml_path = std::path::Path::new(&path).join(muninn_core::config::RepoConfig::FILE_NAME);
            if !toml_path.exists() {
                println!("No muninn.toml found at: {}", path);
            } else {
                print!("Delete {} and remove index data? [y/N] ", toml_path.display());
                use std::io::Write;
                std::io::stdout().flush()?;
                let mut line = String::new();
                std::io::stdin().read_line(&mut line)?;
                if line.trim().eq_ignore_ascii_case("y") {
                    std::fs::remove_file(&toml_path)?;
                    if let Some(repo) = muninn_core::store::get_repo_by_path(&pool, &path).await? {
                        muninn_core::store::delete_repo(&pool, repo.id).await?;
                        println!("Removed index data for: {}", path);
                    }
                    println!("Unregistered: {}", path);
                    println!("Restart muninn-index to stop watching this repo.");
                } else {
                    println!("Aborted.");
                }
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
                println!("Marked all repos for reindex. Restart muninn-index to apply.");
            } else if let Some(p) = path {
                sqlx::query("UPDATE repos SET indexed_at = NULL WHERE path = $1")
                    .bind(&p)
                    .execute(&pool).await?;
                println!("Marked {} for reindex. Restart muninn-index to apply.", p);
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
    }

    Ok(())
}