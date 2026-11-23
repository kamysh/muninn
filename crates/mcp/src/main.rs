mod admin;
mod tools;

use clap::Parser;

#[derive(Parser)]
#[command(name = "muninn-mcp", about = "muninn MCP server", version)]
struct Cli {}

use muninn_core::{
    config::GlobalConfig,
    db,
    embeddings::{expected_dimension, make_backend},
};
use std::{
    path::{Path, PathBuf},
    sync::Arc,
    time::{Duration, SystemTime},
};
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
use tools::SearchContext;
use tracing_appender::non_blocking::WorkerGuard;
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt, EnvFilter};

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    db::exit_on_migration_failure();
    let _cli = Cli::parse();
    let cfg = GlobalConfig::load()?;
    let _log_guard = init_logging(&cfg)?;
    let embedder: Arc<dyn muninn_core::embeddings::EmbeddingBackend> =
        Arc::from(make_backend(&cfg.embeddings));
    let embedding_dim = expected_dimension(&cfg.embeddings);
    let mut ctx = match connect_context(&cfg, Arc::clone(&embedder), embedding_dim).await {
        Ok(connected) => Some(Arc::new(connected)),
        Err(error) => {
            tracing::warn!("database connection unavailable: {error:#}");
            None
        }
    };

    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();
    let mut lines = BufReader::new(stdin).lines();
    let mut writer = stdout;
    let mut reconnect_timer = tokio::time::interval(Duration::from_secs(1));
    let mut requests = tokio::task::JoinSet::new();
    let mut input_closed = false;

    while !input_closed || !requests.is_empty() {
        let line = tokio::select! {
            result = lines.next_line(), if !input_closed => result?,
            result = requests.join_next(), if !requests.is_empty() => {
                if let Some(result) = result {
                    let response: Option<serde_json::Value> = result?;
                    if let Some(response) = response {
                        let mut out = serde_json::to_string(&response)?;
                        out.push('\n');
                        writer.write_all(out.as_bytes()).await?;
                        writer.flush().await?;
                    }
                }
                continue;
            }
            _ = reconnect_timer.tick(), if !input_closed => {
                if ctx.as_ref().is_none_or(|c| c.client.is_closed()) {
                    if let Ok(connected) = connect_context(&cfg, Arc::clone(&embedder), embedding_dim).await {
                        ctx = Some(Arc::new(connected));
                        tracing::info!("database connection restored");
                    }
                }
                continue;
            }
        };
        let Some(line) = line else {
            input_closed = true;
            continue;
        };

        let request: serde_json::Value = match serde_json::from_str(line.trim()) {
            Ok(v) => v,
            Err(_) => continue,
        };

        let is_notification = request.get("id").is_none();
        let method = request.get("method").and_then(|v| v.as_str()).unwrap_or("");
        if method == "tools/call" && ctx.as_ref().is_none_or(|c| c.client.is_closed()) {
            match connect_context(&cfg, Arc::clone(&embedder), embedding_dim).await {
                Ok(connected) => ctx = Some(Arc::new(connected)),
                Err(error) => {
                    tracing::warn!("database connection unavailable: {error:#}");
                    ctx = None;
                }
            }
        }
        let request_context = ctx.clone();
        requests.spawn(async move {
            let response = handle_request(request_context.as_deref(), &request).await;
            (!is_notification).then_some(response)
        });
    }

    Ok(())
}

async fn connect_context(
    cfg: &GlobalConfig,
    embedder: Arc<dyn muninn_core::embeddings::EmbeddingBackend>,
    embedding_dim: usize,
) -> anyhow::Result<SearchContext> {
    let client = tokio::time::timeout(
        Duration::from_secs(3),
        db::connect_with_app_name(&cfg.database, "muninn-mcp"),
    )
    .await??;
    let mut migrate_client = tokio::time::timeout(
        Duration::from_secs(3),
        db::connect_with_app_name(&cfg.database, "muninn-mcp-migrate"),
    )
    .await??;
    db::run_migrations(&mut migrate_client).await?;
    Ok(SearchContext {
        config: cfg.clone(),
        family_embedders: Default::default(),
        client: Arc::new(client),
        embedder,
        embedding_dim,
        record_usage: cfg.mcp.record_usage,
    })
}

async fn handle_request(ctx: Option<&SearchContext>, req: &serde_json::Value) -> serde_json::Value {
    let id = req.get("id").cloned().unwrap_or(serde_json::Value::Null);
    let method = req.get("method").and_then(|v| v.as_str()).unwrap_or("");
    let params = req
        .get("params")
        .cloned()
        .unwrap_or(serde_json::Value::Null);

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
            let walk_suffix = "Supply 'repo' (absolute checkout/directory path) or 'cwd' (a directory inside it); 'repo' takes precedence. Git worktrees resolve through Git and registered families; directory roots through database registration. A first search can register and index a new linked worktree when its family already permits indexing. Subsequent searches use that checkout's last completed index; incomplete Git operations retain it.";
            let cwd_desc = "Directory inside the target checkout or registered directory. Used when 'repo' is absent; no configuration marker is needed.";
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
                                    "repo": {"type": "string", "description": "Absolute path of the target checkout/worktree or indexed directory. Optional if 'cwd' is provided."},
                                    "cwd": {"type": "string", "description": cwd_desc},
                                    "limit": {"type": "integer"}
                                },
                                "required": ["query"]
                            }
                        },
                        {
                            "name": "search_fulltext",
                            "description": format!("Tokenized full-text keyword search, not literal substring or regex matching. {walk_suffix}"),
                            "inputSchema": {
                                "type": "object",
                                "properties": {
                                    "query": {"type": "string"},
                                    "repo": {"type": "string", "description": "Absolute path of the target checkout/worktree or indexed directory. Optional if 'cwd' is provided."},
                                    "cwd": {"type": "string", "description": cwd_desc},
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
                                    "repo": {"type": "string", "description": "Absolute path of the target checkout/worktree or indexed directory. Optional if 'cwd' is provided."},
                                    "cwd": {"type": "string", "description": cwd_desc},
                                    "limit": {"type": "integer"}
                                },
                                "required": ["query"]
                            }
                        },
                        {
                            "name": "search_structural",
                            "description": format!("Find name-based related-symbol candidates, not compiler-verified bindings. For Git checkouts, call resolution prefers matches in the caller file, keeping ties; otherwise it keeps checkout-wide matches. Verify paths and source. {walk_suffix}"),
                            "inputSchema": {
                                "type": "object",
                                "properties": {
                                    "symbol": {"type": "string"},
                                    "relation": {
                                        "type": "string",
                                        "enum": ["callers","callees","imports","defines","inheritors","inherits"]
                                    },
                                    "repo": {"type": "string", "description": "Absolute path of the target checkout/worktree or indexed directory. Optional if 'cwd' is provided."},
                                    "cwd": {"type": "string", "description": cwd_desc}
                                },
                                "required": ["symbol", "relation"]
                            }
                        },
                        {
                            "name": "record_knowledge",
                            "description": "Store a curated knowledge item under an exact repository-path key (no worktree/family resolution). Items are embedded and searchable via search_knowledge. Provide 'id' to update an existing item.",
                            "inputSchema": {
                                "type": "object",
                                "properties": {
                                    "repo":          {"type": "string", "description": "Exact repository-path key for curated knowledge. Worktree paths are not resolved to a shared family; use the established main-checkout key for shared notes."},
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
                            "description": "Hybrid semantic + fulltext search over curated notes under an exact repository-path key; no worktree/family resolution. Use the established main-checkout key for shared notes.",
                            "inputSchema": {
                                "type": "object",
                                "properties": {
                                    "query": {"type": "string"},
                                    "repo":  {"type": "string", "description": "Exact repository-path key, usually the main checkout path for shared notes; no worktree/family resolution."},
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
                            "description": "List knowledge for an exact repository-path key, ordered by most recently updated. Worktrees do not automatically share this key.",
                            "inputSchema": {
                                "type": "object",
                                "properties": {
                                    "repo": {"type": "string", "description": "Exact repository-path key, usually the main checkout path for shared notes; no worktree/family resolution."}
                                },
                                "required": ["repo"]
                            }
                        },
                        {
                            "name": "inspect_policy",
                            "description": "Inspect the current stored policy and effective configuration for a registered family.",
                            "inputSchema": {
                                "type": "object",
                                "properties": {
                                    "repo": {"type": "string", "description": "Absolute path of the target checkout or indexed directory."}
                                },
                                "required": ["repo"]
                            }
                        },
                        {
                            "name": "check_policy",
                            "description": "Validate a policy draft without writing anything.",
                            "inputSchema": {
                                "type": "object",
                                "properties": {
                                    "repo": {"type": "string", "description": "Absolute path of the target checkout or indexed directory."}, "draft": {"type": "object"}
                                },
                                "required": ["repo", "draft"]
                            }
                        },
                        {
                            "name": "apply_policy",
                            "description": "Apply a validated policy draft atomically.",
                            "inputSchema": {
                                "type": "object",
                                "properties": {
                                    "repo": {"type": "string", "description": "Absolute path of the target checkout or indexed directory."}, "draft": {"type": "object"}
                                },
                                "required": ["repo", "draft"]
                            }
                        },
                        {
                            "name": "preflight_family",
                            "description": "Creation defaults and advice for an unregistered directory.",
                            "inputSchema": {
                                "type": "object",
                                "properties": {
                                    "repo": {"type": "string", "description": "Absolute path of the target checkout or indexed directory."}
                                },
                                "required": ["repo"]
                            }
                        },
                        {
                            "name": "register_family",
                            "description": "Register a directory with a frozen creation policy.",
                            "inputSchema": {
                                "type": "object",
                                "properties": {
                                    "repo": {"type": "string", "description": "Absolute path of the target checkout or indexed directory."}, "draft": {"type": "object"}
                                },
                                "required": ["repo", "draft"]
                            }
                        },
                        {
                            "name": "start_family",
                            "description": "Authorize indexing for a registered family.",
                            "inputSchema": {
                                "type": "object",
                                "properties": {
                                    "repo": {"type": "string", "description": "Absolute path of the target checkout or indexed directory."}, "draft": {"type": "object"}
                                },
                                "required": ["repo", "draft"]
                            }
                        },
                        {
                            "name": "reindex_family",
                            "description": "Run the foreground index for a registered family.",
                            "inputSchema": {
                                "type": "object",
                                "properties": {
                                    "repo": {"type": "string", "description": "Absolute path of the target checkout or indexed directory."}
                                },
                                "required": ["repo"]
                            }
                        },
                        {
                            "name": "pause_family",
                            "description": "Pause indexing while preserving accepted work.",
                            "inputSchema": {
                                "type": "object",
                                "properties": {
                                    "repo": {"type": "string", "description": "Absolute path of the target checkout or indexed directory."}
                                },
                                "required": ["repo"]
                            }
                        },
                        {
                            "name": "resume_family",
                            "description": "Resume paused indexing.",
                            "inputSchema": {
                                "type": "object",
                                "properties": {
                                    "repo": {"type": "string", "description": "Absolute path of the target checkout or indexed directory."}
                                },
                                "required": ["repo"]
                            }
                        },
                        {
                            "name": "cancel_work",
                            "description": "Cancel accepted work for one operation; committed results stay.",
                            "inputSchema": {
                                "type": "object",
                                "properties": {
                                    "repo": {"type": "string", "description": "Absolute path of the target checkout or indexed directory."}, "operation_id": {"type": "string"}
                                },
                                "required": ["repo", "operation_id"]
                            }
                        },
                        {
                            "name": "inspect_status",
                            "description": "The family's registration, indexing and usage snapshot.",
                            "inputSchema": {
                                "type": "object",
                                "properties": {
                                    "repo": {"type": "string", "description": "Absolute path of the target checkout or indexed directory."}
                                },
                                "required": ["repo"]
                            }
                        },
                        {
                            "name": "unregister_family",
                            "description": "Retire a registered family without deleting index data.",
                            "inputSchema": {
                                "type": "object",
                                "properties": {
                                    "repo": {"type": "string", "description": "Absolute path of the target checkout or indexed directory."}
                                },
                                "required": ["repo"]
                            }
                        },
                        {
                            "name": "forget_repository",
                            "description": "Unregister and delete all owned index data.",
                            "inputSchema": {
                                "type": "object",
                                "properties": {
                                    "repo": {"type": "string", "description": "Absolute path of the target checkout or indexed directory."}
                                },
                                "required": ["repo"]
                            }
                        },
                        {
                            "name": "recreate_index",
                            "description": "Recreate derived index data for an embedding profile change.",
                            "inputSchema": {
                                "type": "object",
                                "properties": {
                                    "repo": {"type": "string", "description": "Absolute path of the target checkout or indexed directory."}, "draft": {"type": "object"}
                                },
                                "required": ["repo", "draft"]
                            }
                        },
                        {
                            "name": "convert_directory",
                            "description": "Keep a registered directory usable after it becomes a Git repository.",
                            "inputSchema": {
                                "type": "object",
                                "properties": {
                                    "repo": {"type": "string", "description": "Absolute path of the target checkout or indexed directory."}, "draft": {"type": "object"}
                                },
                                "required": ["repo", "draft"]
                            }
                        },
                        {
                            "name": "continue_request",
                            "description": "Resume saved work or return the saved result for an operation ID.",
                            "inputSchema": {
                                "type": "object",
                                "properties": {
                                    "repo": {"type": "string", "description": "Absolute path of the target checkout or indexed directory."}, "operation_id": {"type": "string"}, "message": {"type": "string"}
                                },
                                "required": ["operation_id", "message"]
                            }
                        },
                    ]
                }
            })
        }
        "tools/call" => {
            let Some(ctx) = ctx else {
                return serde_json::json!({"jsonrpc":"2.0", "id":id, "error": {"code":-32603, "message":"Cannot reach the database. Muninn will reconnect automatically; continue with the same request ID when access returns."}});
            };
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
                            &ctx.client,
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
                    if ctx.client.is_closed() {
                        return serde_json::json!({"jsonrpc":"2.0", "id":id, "error": {"code":-32603, "message":"Database connection lost. Muninn will reconnect automatically; continue with the same request ID when access returns."}});
                    }
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
    let env_filter = EnvFilter::try_from_default_env().unwrap_or_else(|_| EnvFilter::new("info"));
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
    client: &tokio_postgres::Client,
    tool: &str,
    repo_path: Option<&str>,
    duration_ms: i64,
    result_count: Option<i64>,
) -> anyhow::Result<()> {
    // These columns are PostgreSQL INT (int4), so their wire values must be i32.
    // Checked conversions keep unusually large measurements from wrapping.
    let duration_ms = i32::try_from(duration_ms)?;
    let result_count = result_count.map(i32::try_from).transpose()?;
    client
        .execute(
            "INSERT INTO mcp_usage (tool, repo_path, duration_ms, result_count) \
             VALUES ($1, $2, $3, $4)",
            &[&tool, &repo_path, &duration_ms, &result_count],
        )
        .await?;
    Ok(())
}

#[cfg(test)]
#[path = "usage_tests.rs"]
mod usage_tests;

#[cfg(test)]
mod worktree_tests;

fn repo_arg(args: &serde_json::Value) -> anyhow::Result<&str> {
    args["repo"]
        .as_str()
        .ok_or_else(|| anyhow::anyhow!("missing 'repo'"))
}

fn draft_arg(args: &serde_json::Value) -> anyhow::Result<&serde_json::Value> {
    args.get("draft")
        .ok_or_else(|| anyhow::anyhow!("missing 'draft'"))
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
            let repo = args["repo"]
                .as_str()
                .ok_or_else(|| anyhow::anyhow!("missing 'repo'"))?
                .to_string();
            let resp = tools::list_knowledge(ctx, &repo).await?;
            Ok(resp)
        }
        "inspect_policy" => Ok(admin::inspect_policy(ctx, repo_arg(&args)?).await?),
        "check_policy" => Ok(admin::check_policy(ctx, repo_arg(&args)?, draft_arg(&args)?).await?),
        "apply_policy" => Ok(admin::apply_policy(ctx, repo_arg(&args)?, draft_arg(&args)?).await?),
        "preflight_family" => Ok(admin::preflight_family(ctx, repo_arg(&args)?).await?),
        "register_family" => {
            Ok(admin::register_family(ctx, repo_arg(&args)?, draft_arg(&args)?).await?)
        }
        "start_family" => Ok(admin::start_family(ctx, repo_arg(&args)?, draft_arg(&args)?).await?),
        "reindex_family" => Ok(admin::reindex_family(ctx, repo_arg(&args)?).await?),
        "pause_family" => Ok(admin::pause_family(ctx, repo_arg(&args)?).await?),
        "resume_family" => Ok(admin::resume_family(ctx, repo_arg(&args)?).await?),
        "cancel_work" => Ok(admin::cancel_work(
            ctx,
            repo_arg(&args)?,
            args["operation_id"]
                .as_str()
                .ok_or_else(|| anyhow::anyhow!("missing 'operation_id'"))?,
        )
        .await?),
        "inspect_status" => Ok(admin::inspect_status(ctx, repo_arg(&args)?).await?),
        "unregister_family" => Ok(admin::unregister_family(ctx, repo_arg(&args)?).await?),
        "forget_repository" => Ok(admin::forget_repository(ctx, repo_arg(&args)?).await?),
        "recreate_index" => {
            Ok(admin::recreate_index(ctx, repo_arg(&args)?, draft_arg(&args)?).await?)
        }
        "convert_directory" => {
            Ok(admin::convert_directory(ctx, repo_arg(&args)?, draft_arg(&args)?).await?)
        }
        "continue_request" => Ok(admin::continue_request(
            ctx,
            args["operation_id"]
                .as_str()
                .ok_or_else(|| anyhow::anyhow!("missing 'operation_id'"))?,
            args["message"].as_str().map(str::to_string),
        )
        .await?),
        other => Err(anyhow::anyhow!("unknown tool: {}", other)),
    }
}
