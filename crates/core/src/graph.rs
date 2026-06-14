use tokio_postgres::Client;
use uuid::Uuid;
use anyhow::Result;
use crate::types::{Symbol, SymbolKind, LineRange, StructuralRelation, StructuralEdge};
use crate::store::graph_name;

// ─── Per-statement graph-write timeout (Tier 2 safety net) ───────────────────
//
// Each `muninn_cypher` write runs inside a transaction with `SET LOCAL
// statement_timeout`, so any single AGE operation that gets pathologically slow
// (see issue #5) aborts after `GRAPH_STATEMENT_TIMEOUT_SECS`. On timeout the
// helper logs a structured warning and returns `Ok(())` — the file's chunks
// remain indexed (full-text + semantic search work); only the symbol-graph
// portion for that op is partial or missing.
// Spec: Muninn.Storage (IsolatedGraph + timeout addendum).
const GRAPH_STATEMENT_TIMEOUT_SECS: u64 = 60;

fn is_statement_timeout(err: &tokio_postgres::Error) -> bool {
    // SQLSTATE 57014 = query_canceled (covers statement_timeout and lock_timeout)
    err.code() == Some(&tokio_postgres::error::SqlState::QUERY_CANCELED)
}

async fn exec_cypher_with_timeout(
    client: &Client,
    gname: &str,
    cypher: &str,
    params: &str,
    op: &'static str,
    context: &str,
) -> Result<()> {
    // Set a session-level statement timeout, execute, then reset.
    // Using SET (not SET LOCAL) so it works outside a transaction.
    client
        .execute(
            &format!("SET statement_timeout = '{GRAPH_STATEMENT_TIMEOUT_SECS}s'"),
            &[],
        )
        .await?;
    let result = client
        .execute(
            "SELECT * FROM muninn_cypher($1, $2, $3)",
            &[&gname, &cypher, &params],
        )
        .await;
    // Reset to default regardless of outcome.
    let _ = client.execute("SET statement_timeout = 0", &[]).await;
    match result {
        Ok(_) => Ok(()),
        Err(e) if is_statement_timeout(&e) => {
            tracing::warn!(
                op = op,
                context = context,
                timeout_secs = GRAPH_STATEMENT_TIMEOUT_SECS,
                "graph write timed out — chunks remain indexed; symbol graph for this op is partial or missing. Consider tightening `[index].exclude` for very large or symbol-dense files."
            );
            Ok(())
        }
        Err(e) => Err(e.into()),
    }
}

/// Input for one symbol node in a batch upsert.
pub struct SymbolNodeInput {
    pub chunk_id: Uuid,
    pub name: String,
    pub kind: SymbolKind,
    pub file_path: String,
    pub start_line: u32,
    pub end_line: u32,
}

fn kind_label(kind: &SymbolKind) -> &'static str {
    match kind {
        SymbolKind::Function => "Function",
        SymbolKind::Class    => "Class",
        SymbolKind::Module   => "Module",
        SymbolKind::Import   => "Import",
    }
}

fn relation_label(rel: &StructuralRelation) -> &'static str {
    match rel {
        StructuralRelation::Calls        => "CALLS",
        StructuralRelation::Imports      => "IMPORTS",
        StructuralRelation::Defines      => "DEFINES",
        StructuralRelation::InheritsFrom => "INHERITS_FROM",
    }
}

/// Batch-upsert symbol nodes into the per-repo AGE graph using one
/// `UNWIND … MERGE` per distinct node label (≤4 round-trips total).
pub async fn upsert_symbol_nodes(
    client: &Client,
    repo_id: Uuid,
    nodes: &[SymbolNodeInput],
) -> Result<()> {
    if nodes.is_empty() {
        return Ok(());
    }
    let gname = graph_name(repo_id);

    let mut by_label: std::collections::HashMap<&'static str, Vec<serde_json::Value>> =
        std::collections::HashMap::new();
    for n in nodes {
        by_label.entry(kind_label(&n.kind)).or_default().push(serde_json::json!({
            "chunk_id": n.chunk_id.to_string(),
            "name": n.name,
            "file_path": n.file_path,
            "start_line": n.start_line,
            "end_line": n.end_line,
        }));
    }

    for (label, rows) in by_label {
        let params = serde_json::json!({ "rows": rows });
        let cypher = format!(
            r#"UNWIND $rows AS r
               MERGE (n:{label} {{chunk_id: r.chunk_id}})
               SET n.name = r.name,
                   n.kind = '{label}',
                   n.file_path = r.file_path,
                   n.start_line = r.start_line,
                   n.end_line = r.end_line"#,
            label = label,
        );
        exec_cypher_with_timeout(
            client,
            &gname,
            &cypher,
            &params.to_string(),
            "upsert_symbol_nodes",
            label,
        )
        .await?;
    }
    Ok(())
}

/// Batch-upsert directed edges into the per-repo graph using one
/// `UNWIND … MATCH … MERGE` per distinct relation type (≤4 round-trips).
pub async fn upsert_edges(client: &Client, repo_id: Uuid, edges: &[StructuralEdge]) -> Result<()> {
    if edges.is_empty() {
        return Ok(());
    }
    let gname = graph_name(repo_id);

    let mut by_rel: std::collections::HashMap<&'static str, Vec<serde_json::Value>> =
        std::collections::HashMap::new();
    for e in edges {
        by_rel.entry(relation_label(&e.relation)).or_default().push(serde_json::json!({
            "from": e.from.to_string(),
            "to": e.to.to_string(),
        }));
    }

    for (rel, rows) in by_rel {
        let params = serde_json::json!({ "rows": rows });
        let cypher = format!(
            r#"UNWIND $rows AS r
               MATCH (a {{chunk_id: r.from}}), (b {{chunk_id: r.to}})
               MERGE (a)-[:{rel}]->(b)"#,
            rel = rel,
        );
        exec_cypher_with_timeout(
            client,
            &gname,
            &cypher,
            &params.to_string(),
            "upsert_edges",
            rel,
        )
        .await?;
    }
    Ok(())
}

/// Delete all symbol nodes (and their incident edges) for a file from the
/// per-repo graph.
pub async fn delete_file_symbols(client: &Client, repo_id: Uuid, file_path: &str) -> Result<()> {
    let gname = graph_name(repo_id);
    let params = serde_json::json!({ "sym_file_path": file_path });
    let cypher = r#"MATCH (n {file_path: $sym_file_path}) DETACH DELETE n"#;
    exec_cypher_with_timeout(
        client,
        &gname,
        cypher,
        &params.to_string(),
        "delete_file_symbols",
        file_path,
    )
    .await?;
    Ok(())
}

/// Query symbols related to a given symbol name by relation type and direction.
pub async fn query_related(
    client: &Client,
    repo_id: Uuid,
    symbol_name: &str,
    relation: StructuralRelation,
    incoming: bool,
) -> Result<Vec<Symbol>> {
    let gname = graph_name(repo_id);

    let edge_type = match relation {
        StructuralRelation::Calls => "CALLS",
        StructuralRelation::Imports => "IMPORTS",
        StructuralRelation::Defines => "DEFINES",
        StructuralRelation::InheritsFrom => "INHERITS_FROM",
    };

    let params = serde_json::json!({ "sym_name": symbol_name });

    let cypher = if incoming {
        format!(
            r#"MATCH (a)-[:{edge}]->(b {{name: $sym_name}})
               RETURN {{chunk_id: a.chunk_id, name: a.name, file_path: a.file_path,
                        kind: a.kind, start_line: a.start_line, end_line: a.end_line}}"#,
            edge = edge_type,
        )
    } else {
        format!(
            r#"MATCH (a {{name: $sym_name}})-[:{edge}]->(b)
               RETURN {{chunk_id: b.chunk_id, name: b.name, file_path: b.file_path,
                        kind: b.kind, start_line: b.start_line, end_line: b.end_line}}"#,
            edge = edge_type,
        )
    };

    let rows = client
        .query(
            "SELECT r::text FROM muninn_cypher($1, $2, $3) AS r",
            &[&gname, &cypher, &params.to_string()],
        )
        .await?;

    let mut symbols = vec![];
    for row in rows {
        let raw: String = row.try_get(0).unwrap_or_default();
        let map: serde_json::Value =
            serde_json::from_str(&raw).unwrap_or(serde_json::Value::Null);

        let name = map.get("name")
            .and_then(|v| v.as_str())
            .map(|s| s.trim_matches('"').to_string())
            .unwrap_or_default();
        let file_path = map.get("file_path")
            .and_then(|v| v.as_str())
            .map(|s| s.trim_matches('"').to_string())
            .unwrap_or_default();
        let kind_str = map.get("kind")
            .and_then(|v| v.as_str())
            .map(|s| s.trim_matches('"').to_string())
            .unwrap_or_default();
        let start_line = map.get("start_line")
            .and_then(|v| v.as_u64())
            .unwrap_or(0) as u32;
        let end_line = map.get("end_line")
            .and_then(|v| v.as_u64())
            .unwrap_or(0) as u32;
        let chunk_id: Uuid = map.get("chunk_id")
            .and_then(|v| v.as_str())
            .and_then(|s| s.trim_matches('"').parse().ok())
            .unwrap_or_else(Uuid::nil);

        symbols.push(Symbol {
            name,
            kind: parse_symbol_kind(&kind_str),
            file_path,
            range: LineRange {
                start: start_line,
                end: end_line,
            },
            chunk_id,
        });
    }
    Ok(symbols)
}

fn parse_symbol_kind(s: &str) -> SymbolKind {
    match s {
        "Function" => SymbolKind::Function,
        "Class" => SymbolKind::Class,
        "Module" => SymbolKind::Module,
        "Import" => SymbolKind::Import,
        _ => SymbolKind::Function,
    }
}

#[cfg(test)]
mod tests {
    #[allow(unused_imports)]
    use super::*;
    use crate::{config::GlobalConfig, db};

    async fn test_client() -> tokio_postgres::Client {
        let manifest = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let config_path = manifest.join("../../config.toml");
        let cfg = GlobalConfig::load_from(&config_path).expect("load local config.toml");
        db::connect(&cfg.database).await.expect("connect to muninn db")
    }

    #[tokio::test]
    #[ignore = "requires live muninn database at localhost:5450"]
    async fn test_write_via_execute() {
        let client = test_client().await;
        let gname = "code_graph_63ca78b63feb4129841eb8c3842f8aec";
        let params = serde_json::json!({"sym_name": "write_test", "sym_file": "/test.rs"});

        client
            .execute(
                "SELECT * FROM muninn_cypher($1, $2, $3)",
                &[
                    &gname,
                    &"MERGE (n:Function {chunk_id: 'write-test-uuid'}) SET n.name = $sym_name, n.kind = 'Function', n.file_path = $sym_file, n.start_line = 1, n.end_line = 5",
                    &params.to_string(),
                ],
            )
            .await
            .expect("MERGE via muninn_cypher should succeed");

        let rows = client
            .query(
                "SELECT r::text FROM muninn_cypher($1, $2, $3) AS r",
                &[
                    &gname,
                    &"MATCH (n {chunk_id: 'write-test-uuid'}) RETURN {name: n.name, kind: n.kind}",
                    &"{}",
                ],
            )
            .await
            .expect("read back should succeed");

        assert_eq!(rows.len(), 1, "node should have been written");
        let raw: String = rows[0].try_get(0).unwrap();
        let map: serde_json::Value = serde_json::from_str(&raw).unwrap();
        assert_eq!(map.get("name").and_then(|v| v.as_str()).unwrap_or(""), "write_test");
    }

    #[tokio::test]
    #[ignore = "requires live muninn database at localhost:5450"]
    async fn test_agtype_map_column_readable() {
        let client = test_client().await;
        let gname = "code_graph_63ca78b63feb4129841eb8c3842f8aec";
        let params = serde_json::json!({"sym_name": "test_func"});

        let rows = client
            .query(
                "SELECT r::text FROM muninn_cypher($1, $2, $3) AS r",
                &[
                    &gname,
                    &"MATCH (n {name: $sym_name}) RETURN {chunk_id: n.chunk_id, name: n.name, file_path: n.file_path, kind: n.kind, start_line: n.start_line, end_line: n.end_line}",
                    &params.to_string(),
                ],
            )
            .await
            .expect("query should succeed");

        assert_eq!(rows.len(), 1, "should find the test_func node");
        let raw: String = rows[0].try_get(0).expect("r column should be text");
        let map: serde_json::Value = serde_json::from_str(&raw).expect("should parse as JSON");
        let name = map.get("name")
            .and_then(|v| v.as_str())
            .map(|s| s.trim_matches('"').to_string())
            .unwrap_or_default();
        assert_eq!(name, "test_func");
        let start_line = map.get("start_line").and_then(|v| v.as_u64()).unwrap_or(0);
        assert_eq!(start_line, 1);
    }
}
