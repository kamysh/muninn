mod tools;

use clap::Parser;

#[derive(Parser)]
#[command(name = "muninn-mcp", about = "muninn MCP server", version)]
struct Cli {}

use muninn_core::{config::GlobalConfig, db, embeddings::{make_backend, expected_dimension}};
use std::{path::{Path, PathBuf}, sync::Arc, time::{Duration, SystemTime}};
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
use tools::SearchContext;
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt, EnvFilter};
use tracing_appender::non_blocking::WorkerGuard;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let _cli = Cli::parse();
    let cfg = GlobalConfig::load()?;
    let _log_guard = init_logging(&cfg)?;
    let pool = db::connect_with_app_name(&cfg.database, "muninn-mcp").await?;
    // Self-apply migrations on startup so the server works against a DB that
    // hasn't been migrated yet (e.g. right after a binary upgrade). Idempotent.
    db::run_migrations(&pool).await?;
    let embedder: Arc<dyn muninn_core::embeddings::EmbeddingBackend> =
        Arc::from(make_backend(&cfg.embeddings));
    let embedding_dim = expected_dimension(&cfg.embeddings);
    let ctx = Arc::new(SearchContext {
        pool,
        embedder,
        embedding_dim,
        record_usage: cfg.mcp.record_usage,
    });

    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();
    let mut reader = BufReader::new(stdin);
    let mut writer = stdout;
    let mut line = String::new();

    loop {
        line.clear();
        let n = reader.read_line(&mut line).await?;
        if n == 0 {
            break;
        }

        let request: serde_json::Value = match serde_json::from_str(line.trim()) {
            Ok(v) => v,
            Err(_) => continue,
        };

        let is_notification = request.get("id").is_none();
        let response = handle_request(&ctx, &request).await;
        if !is_notification {
            let mut out = serde_json::to_string(&response)?;
            out.push('\n');
            writer.write_all(out.as_bytes()).await?;
            writer.flush().await?;
        }
    }

    Ok(())
}

async fn handle_request(ctx: &SearchContext, req: &serde_json::Value) -> serde_json::Value {
    let id = req.get("id").cloned().unwrap_or(serde_json::Value::Null);
    let method = req.get("method").and_then(|v| v.as_str()).unwrap_or("");
    let params = req.get("params").cloned().unwrap_or(serde_json::Value::Null);

    match method {
        "initialize" => serde_json::json!({
            "jsonrpc": "2.0",
            "id": id,
            "result": {
                "protocolVersion": "2024-11-05",
                "capabilities": { "tools": {} },
                "serverInfo": { "name": "muninn", "version": env!("CARGO_PKG_VERSION") }
            }
        }),
        "tools/list" => {
            let fname = muninn_core::config::RepoConfig::FILE_NAME;
            let walk_suffix = format!(
                "Supply 'repo' (absolute path) or 'cwd' (current working directory) \
                 — the nearest ancestor containing {fname} is used when 'repo' is absent."
            );
            let cwd_desc = format!(
                "Current working directory. Used to resolve the repo by walking up \
                 to the nearest {fname} when 'repo' is absent."
            );
            serde_json::json!({
            "jsonrpc": "2.0",
            "id": id,
            "result": {
                "tools": [
                    {
                        "name": "search_hybrid",
                        "description": format!("Semantic + fulltext hybrid search over indexed repos. {walk_suffix}"),
                        "inputSchema": {
                            "type": "object",
                            "properties": {
                                "query": {"type": "string"},
                                "repo": {"type": "string", "description": "Absolute path of the indexed repo. Optional if 'cwd' is provided."},
                                "cwd": {"type": "string", "description": (cwd_desc.clone())},
                                "limit": {"type": "integer"}
                            },
                            "required": ["query"]
                        }
                    },
                    {
                        "name": "search_fulltext",
                        "description": format!("Full-text keyword search. {walk_suffix}"),
                        "inputSchema": {
                            "type": "object",
                            "properties": {
                                "query": {"type": "string"},
                                "repo": {"type": "string", "description": "Absolute path of the indexed repo. Optional if 'cwd' is provided."},
                                "cwd": {"type": "string", "description": (cwd_desc.clone())},
                                "limit": {"type": "integer"}
                            },
                            "required": ["query"]
                        }
                    },
                    {
                        "name": "search_semantic",
                        "description": format!("Vector similarity search. {walk_suffix}"),
                        "inputSchema": {
                            "type": "object",
                            "properties": {
                                "query": {"type": "string"},
                                "repo": {"type": "string", "description": "Absolute path of the indexed repo. Optional if 'cwd' is provided."},
                                "cwd": {"type": "string", "description": (cwd_desc.clone())},
                                "limit": {"type": "integer"}
                            },
                            "required": ["query"]
                        }
                    },
                    {
                        "name": "search_structural",
                        "description": format!("Graph traversal — find related symbols. {walk_suffix}"),
                        "inputSchema": {
                            "type": "object",
                            "properties": {
                                "symbol": {"type": "string"},
                                "relation": {
                                    "type": "string",
                                    "enum": ["callers","callees","imports","defines","inheritors","inherits"]
                                },
                                "repo": {"type": "string", "description": "Absolute path of the indexed repo. Optional if 'cwd' is provided."},
                                "cwd": {"type": "string", "description": (cwd_desc)}
                            },
                            "required": ["symbol", "relation"]
                        }
                    },
                    {
                        "name": "record_knowledge",
                        "description": "Store a curated knowledge item (note, lesson, or subsystem insight) for a repo. Items are embedded and searchable via search_knowledge. Provide 'id' to update an existing item.",
                        "inputSchema": {
                            "type": "object",
                            "properties": {
                                "repo":          {"type": "string", "description": "Absolute path of the repo this knowledge belongs to."},
                                "title":         {"type": "string", "description": "Short title."},
                                "body":          {"type": "string", "description": "Full content of the note or lesson."},
                                "tags":          {"type": "array", "items": {"type": "string"}, "description": "Optional tags for categorisation."},
                                "related_files": {"type": "array", "items": {"type": "string"}, "description": "Repo-relative file paths that this item describes."},
                                "id":            {"type": "string", "description": "UUID of existing item to update. Omit to insert."}
                            },
                            "required": ["repo", "title", "body"]
                        }
                    },
                    {
                        "name": "search_knowledge",
                        "description": "Hybrid semantic + fulltext search over knowledge items stored for a repo.",
                        "inputSchema": {
                            "type": "object",
                            "properties": {
                                "query": {"type": "string"},
                                "repo":  {"type": "string", "description": "Absolute path of the repo."},
                                "limit": {"type": "integer"}
                            },
                            "required": ["query", "repo"]
                        }
                    },
                    {
                        "name": "delete_knowledge",
                        "description": "Delete a knowledge item by its UUID.",
                        "inputSchema": {
                            "type": "object",
                            "properties": {
                                "id": {"type": "string", "description": "UUID of the knowledge item to delete."}
                            },
                            "required": ["id"]
                        }
                    },
                    {
                        "name": "list_knowledge",
                        "description": "List all knowledge items stored for a repo, ordered by most recently updated.",
                        "inputSchema": {
                            "type": "object",
                            "properties": {
                                "repo": {"type": "string", "description": "Absolute path of the repo."}
                            },
                            "required": ["repo"]
                        }
                    }
                ]
            }
        })
        },
        "tools/call" => {
            let tool_name = params.get("name").and_then(|v| v.as_str()).unwrap_or("");
            let args = params
                .get("arguments")
                .cloned()
                .unwrap_or(serde_json::Value::Object(Default::default()));

            let repo_hint = extract_repo_hint(&args);
            let query_hint = extract_query_hint(&args);
            let started = std::time::Instant::now();
            let result = dispatch_tool(ctx, tool_name, args).await;
            match result {
                Ok(content) => {
                    let duration_ms = started.elapsed().as_millis() as i64;
                    let result_count = count_results(&content);
                    tracing::info!(
                        tool = tool_name,
                        repo = repo_hint.as_deref().unwrap_or(""),
                        query = query_hint.as_deref().unwrap_or(""),
                        duration_ms,
                        result_count = result_count.unwrap_or(-1)
                    );
                    if ctx.record_usage {
                        if let Err(e) = record_usage(
                            &ctx.pool,
                            tool_name,
                            repo_hint.as_deref(),
                            duration_ms,
                            result_count,
                        )
                        .await
                        {
                            tracing::warn!(error = %e, "failed to record mcp usage");
                        }
                    }
                    serde_json::json!({
                        "jsonrpc": "2.0",
                        "id": id,
                        "result": { "content": [{ "type": "text", "text": content.to_string() }] }
                    })
                }
                Err(e) => {
                    tracing::warn!(tool = tool_name, error = %e, "tool call failed");
                    serde_json::json!({
                        "jsonrpc": "2.0",
                        "id": id,
                        "error": { "code": -32603, "message": e.to_string() }
                    })
                }
            }
        }
        _ => serde_json::json!({
            "jsonrpc": "2.0",
            "id": id,
            "error": { "code": -32601, "message": "method not found" }
        }),
    }
}

fn init_logging(cfg: &GlobalConfig) -> anyhow::Result<Option<WorkerGuard>> {
    let env_filter =
        EnvFilter::try_from_default_env().unwrap_or_else(|_| EnvFilter::new("info"));
    let stderr_layer = tracing_subscriber::fmt::layer().with_writer(std::io::stderr);

    if !cfg.mcp.logging.enabled {
        tracing_subscriber::registry()
            .with(env_filter)
            .with(stderr_layer)
            .init();
        return Ok(None);
    }

    let log_dir = expand_tilde(&cfg.mcp.logging.dir);
    std::fs::create_dir_all(&log_dir)?;

    if cfg.mcp.logging.retention_days > 0 {
        let _ = prune_log_dir(&log_dir, cfg.mcp.logging.retention_days);
        if cfg.mcp.logging.prune_interval_hours > 0 {
            let log_dir = log_dir.clone();
            let retention = cfg.mcp.logging.retention_days;
            let interval = Duration::from_secs(cfg.mcp.logging.prune_interval_hours * 3600);
            tokio::spawn(async move {
                let mut ticker = tokio::time::interval(interval);
                loop {
                    ticker.tick().await;
                    let _ = prune_log_dir(&log_dir, retention);
                }
            });
        }
    }

    let file_appender = tracing_appender::rolling::daily(&log_dir, "muninn-mcp.log");
    let (file_writer, guard) = tracing_appender::non_blocking(file_appender);
    let file_layer = tracing_subscriber::fmt::layer()
        .with_writer(file_writer)
        .with_ansi(false);

    tracing_subscriber::registry()
        .with(env_filter)
        .with(stderr_layer)
        .with(file_layer)
        .init();

    Ok(Some(guard))
}

fn expand_tilde(path: &str) -> PathBuf {
    if path == "~" {
        return std::env::var("HOME")
            .map(PathBuf::from)
            .unwrap_or_else(|_| PathBuf::from(path));
    }
    if let Some(rest) = path.strip_prefix("~/") {
        if let Ok(home) = std::env::var("HOME") {
            return PathBuf::from(home).join(rest);
        }
    }
    PathBuf::from(path)
}

fn prune_log_dir(dir: &Path, retention_days: u64) -> std::io::Result<()> {
    let cutoff = match SystemTime::now()
        .checked_sub(Duration::from_secs(retention_days.saturating_mul(86_400)))
    {
        Some(t) => t,
        None => return Ok(()),
    };

    for entry in std::fs::read_dir(dir)? {
        let entry = match entry {
            Ok(e) => e,
            Err(_) => continue,
        };
        let path = entry.path();
        let meta = match entry.metadata() {
            Ok(m) => m,
            Err(_) => continue,
        };
        if !meta.is_file() {
            continue;
        }
        let modified = match meta.modified() {
            Ok(m) => m,
            Err(_) => continue,
        };
        if modified < cutoff {
            let _ = std::fs::remove_file(path);
        }
    }
    Ok(())
}

fn extract_repo_hint(args: &serde_json::Value) -> Option<String> {
    if let Some(repo) = args.get("repo").and_then(|v| v.as_str()) {
        return Some(repo.to_string());
    }
    if let Some(cwd) = args.get("cwd").and_then(|v| v.as_str()) {
        let cwd_path = Path::new(cwd);
        if let Some(root) = muninn_core::repo_resolver::find_repo_root(cwd_path) {
            return Some(root.to_string_lossy().to_string());
        }
        return Some(cwd.to_string());
    }
    None
}

fn extract_query_hint(args: &serde_json::Value) -> Option<String> {
    if let Some(query) = args.get("query").and_then(|v| v.as_str()) {
        return Some(query.to_string());
    }
    if let Some(symbol) = args.get("symbol").and_then(|v| v.as_str()) {
        return Some(symbol.to_string());
    }
    None
}

fn count_results(content: &serde_json::Value) -> Option<i64> {
    if let Some(results) = content.get("results").and_then(|v| v.as_array()) {
        return Some(results.len() as i64);
    }
    if let Some(symbols) = content.get("symbols").and_then(|v| v.as_array()) {
        return Some(symbols.len() as i64);
    }
    None
}

async fn record_usage(
    pool: &sqlx::PgPool,
    tool: &str,
    repo_path: Option<&str>,
    duration_ms: i64,
    result_count: Option<i64>,
) -> anyhow::Result<()> {
    sqlx::query(
        "INSERT INTO mcp_usage (tool, repo_path, duration_ms, result_count)
         VALUES ($1, $2, $3, $4)",
    )
    .bind(tool)
    .bind(repo_path)
    .bind(duration_ms)
    .bind(result_count)
    .execute(pool)
    .await?;
    Ok(())
}

async fn dispatch_tool(
    ctx: &SearchContext,
    name: &str,
    args: serde_json::Value,
) -> anyhow::Result<serde_json::Value> {
    match name {
        "search_hybrid" => {
            let params: tools::SearchParams = serde_json::from_value(args)?;
            let resp = tools::search_hybrid(ctx, params).await?;
            Ok(serde_json::to_value(resp)?)
        }
        "search_fulltext" => {
            let params: tools::SearchParams = serde_json::from_value(args)?;
            let resp = tools::search_fulltext(ctx, params).await?;
            Ok(serde_json::to_value(resp)?)
        }
        "search_semantic" => {
            let params: tools::SearchParams = serde_json::from_value(args)?;
            let resp = tools::search_semantic(ctx, params).await?;
            Ok(serde_json::to_value(resp)?)
        }
        "search_structural" => {
            let params: tools::StructuralParams = serde_json::from_value(args)?;
            let resp = tools::search_structural(ctx, params).await?;
            Ok(resp)
        }
        "record_knowledge" => {
            let params: tools::RecordKnowledgeParams = serde_json::from_value(args)?;
            let resp = tools::record_knowledge(ctx, params).await?;
            Ok(serde_json::to_value(resp)?)
        }
        "search_knowledge" => {
            let params: tools::SearchKnowledgeParams = serde_json::from_value(args)?;
            let resp = tools::search_knowledge(ctx, params).await?;
            Ok(serde_json::to_value(resp)?)
        }
        "delete_knowledge" => {
            let params: tools::DeleteKnowledgeParams = serde_json::from_value(args)?;
            let resp = tools::delete_knowledge(ctx, params).await?;
            Ok(resp)
        }
        "list_knowledge" => {
            let repo = args["repo"].as_str()
                .ok_or_else(|| anyhow::anyhow!("missing 'repo'"))?
                .to_string();
            let resp = tools::list_knowledge(ctx, &repo).await?;
            Ok(resp)
        }
        other => Err(anyhow::anyhow!("unknown tool: {}", other)),
    }
}
