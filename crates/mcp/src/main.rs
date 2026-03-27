mod tools;

use muninn_core::{config::AppConfig, db, embeddings::make_backend};
use std::sync::Arc;
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
use tools::SearchContext;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    tracing_subscriber::fmt().with_writer(std::io::stderr).init();

    let cfg = AppConfig::load()?;
    let pool = db::connect(&cfg.database.dsn).await?;
    let embedder: Arc<dyn muninn_core::embeddings::EmbeddingBackend> =
        Arc::from(make_backend(&cfg.embeddings));
    let ctx = Arc::new(SearchContext { pool, embedder });

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

        let response = handle_request(&ctx, &request).await;
        let mut out = serde_json::to_string(&response)?;
        out.push('\n');
        writer.write_all(out.as_bytes()).await?;
        writer.flush().await?;
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
        "tools/list" => serde_json::json!({
            "jsonrpc": "2.0",
            "id": id,
            "result": {
                "tools": [
                    {
                        "name": "search_hybrid",
                        "description": "Semantic + fulltext hybrid search over indexed repos",
                        "inputSchema": {
                            "type": "object",
                            "properties": {
                                "query": {"type": "string"},
                                "repo": {"type": "string"},
                                "limit": {"type": "integer"}
                            },
                            "required": ["query"]
                        }
                    },
                    {
                        "name": "search_fulltext",
                        "description": "Full-text keyword search",
                        "inputSchema": {
                            "type": "object",
                            "properties": {
                                "query": {"type": "string"},
                                "repo": {"type": "string"},
                                "limit": {"type": "integer"}
                            },
                            "required": ["query"]
                        }
                    },
                    {
                        "name": "search_semantic",
                        "description": "Vector similarity search",
                        "inputSchema": {
                            "type": "object",
                            "properties": {
                                "query": {"type": "string"},
                                "repo": {"type": "string"},
                                "limit": {"type": "integer"}
                            },
                            "required": ["query"]
                        }
                    },
                    {
                        "name": "search_structural",
                        "description": "Graph traversal — find related symbols",
                        "inputSchema": {
                            "type": "object",
                            "properties": {
                                "symbol": {"type": "string"},
                                "relation": {
                                    "type": "string",
                                    "enum": ["callers","callees","imports","defines","inheritors","inherits"]
                                },
                                "repo": {"type": "string"}
                            },
                            "required": ["symbol", "relation"]
                        }
                    }
                ]
            }
        }),
        "tools/call" => {
            let tool_name = params.get("name").and_then(|v| v.as_str()).unwrap_or("");
            let args = params
                .get("arguments")
                .cloned()
                .unwrap_or(serde_json::Value::Object(Default::default()));

            let result = dispatch_tool(ctx, tool_name, args).await;
            match result {
                Ok(content) => serde_json::json!({
                    "jsonrpc": "2.0",
                    "id": id,
                    "result": { "content": [{ "type": "text", "text": content.to_string() }] }
                }),
                Err(e) => serde_json::json!({
                    "jsonrpc": "2.0",
                    "id": id,
                    "error": { "code": -32603, "message": e.to_string() }
                }),
            }
        }
        _ => serde_json::json!({
            "jsonrpc": "2.0",
            "id": id,
            "error": { "code": -32601, "message": "method not found" }
        }),
    }
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
        other => Err(anyhow::anyhow!("unknown tool: {}", other)),
    }
}