use clap::{Parser, Subcommand};
use ai_mem_core::{config::AppConfig, db, store};

#[derive(Parser)]
#[command(name = "ai-mem", about = "ai-mem repository index manager")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Register a repository and queue it for indexing
    Register {
        path: String,
        #[arg(long)]
        name: Option<String>,
    },
    /// Unregister a repository and delete its index data
    Unregister { path: String },
    /// List registered repositories and their index status
    List,
    /// Force full reindex of a repository (or all repos)
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
    let mut cfg = AppConfig::load()?;
    let pool = db::connect(&cfg.database.dsn).await?;

    match cli.command {
        Commands::Register { path, name } => {
            let name = name.unwrap_or_else(|| {
                std::path::Path::new(&path)
                    .file_name()
                    .unwrap_or_default()
                    .to_string_lossy()
                    .to_string()
            });
            let repo = store::register_repo(&pool, &path, &name).await?;
            cfg.repos.push(ai_mem_core::config::RepoEntry {
                id: repo.id,
                path: path.clone(),
                name: name.clone(),
            });
            cfg.save()?;
            println!("Registered: {} ({})", name, path);
        }

        Commands::Unregister { path } => {
            if let Some(repo) = store::get_repo_by_path(&pool, &path).await? {
                store::delete_repo(&pool, repo.id).await?;
                cfg.repos.retain(|r| r.path != path);
                cfg.save()?;
                println!("Unregistered: {}", path);
            } else {
                println!("Not found: {}", path);
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
                println!("Marked all repos for reindex. Restart ai-mem-index to apply.");
            } else if let Some(p) = path {
                sqlx::query("UPDATE repos SET indexed_at = NULL WHERE path = $1")
                    .bind(&p)
                    .execute(&pool).await?;
                println!("Marked {} for reindex. Restart ai-mem-index to apply.", p);
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