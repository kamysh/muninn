use tokio_postgres::Client;
use uuid::Uuid;
use anyhow::Result;
use crate::types::{Symbol, SymbolKind, LineRange, StructuralRelation, StructuralEdge};
use crate::store::graph_name;

// ─── Per-statement graph-write timeout (Tier 2 safety net) ───────────────────
//
// Each AGE Cypher write uses PREPARE/EXECUTE/DEALLOCATE via simple_query
// (plain-text protocol). The Cypher query string is a SQL literal in the
// PREPARE statement; user data (file paths, symbol names) goes into the EXECUTE
// call as a typed agtype parameter ($1). This enforces the query/data boundary
// at the protocol level — the Cypher query structure can never be altered by
// user input.
//
// Each write is bracketed by SET/RESET statement_timeout so that any single AGE
// operation that gets pathologically slow aborts after GRAPH_STATEMENT_TIMEOUT_SECS.
// On timeout the helper logs a structured warning and returns Ok(()) — the file's
// chunks remain indexed (full-text + semantic search work); only the symbol-graph
// portion for that op is partial or missing.
// Spec: Muninn.Storage (IsolatedGraph + timeout addendum).
const GRAPH_STATEMENT_TIMEOUT_SECS: u64 = 60;

fn is_statement_timeout(err: &tokio_postgres::Error) -> bool {
    // SQLSTATE 57014 = query_canceled (covers statement_timeout and lock_timeout)
    err.code() == Some(&tokio_postgres::error::SqlState::QUERY_CANCELED)
}

/// Run PREPARE / EXECUTE / DEALLOCATE for a Cypher write that takes one
/// agtype parameter, using simple_query (plain-text protocol).
/// `stmt_name` must be unique per call (use a UUID-derived name).
/// `prepare_sql` is the full PREPARE statement.
/// `agtype_json` is the raw JSON object (user data); sql_esc is applied here.
async fn age_execute(
    client: &Client,
    stmt_name: &str,
    prepare_sql: &str,
    agtype_json: &str,
) -> Result<()> {
    client.simple_query(prepare_sql).await?;
    let exec = format!("EXECUTE {}('{}')", stmt_name, sql_esc(agtype_json));
    let result = client.simple_query(&exec).await;
    let _ = client.simple_query(&format!("DEALLOCATE {}", stmt_name)).await;
    result?;
    Ok(())
}

/// Escape an agtype JSON literal for embedding inside a SQL string literal.
/// Single-quote doubling only — the JSON layer is handled by serde_json serialization.
fn sql_esc(s: &str) -> String {
    s.replace('\'', "''")
}

async fn exec_cypher_write_with_timeout(
    client: &Client,
    gname: &str,
    stmt_name: &str,
    prepare_sql: &str,
    agtype_json: &str,
    op: &'static str,
    context: &str,
) -> Result<()> {
    client
        .execute(
            &format!("SET statement_timeout = '{GRAPH_STATEMENT_TIMEOUT_SECS}s'"),
            &[],
        )
        .await?;
    let result = age_execute(client, stmt_name, prepare_sql, agtype_json).await;
    let _ = client.execute("SET statement_timeout = 0", &[]).await;
    match result {
        Ok(_) => Ok(()),
        Err(e) => {
            // Check if the underlying cause is a statement timeout.
            let is_timeout = e.downcast_ref::<tokio_postgres::Error>()
                .map(is_statement_timeout)
                .unwrap_or(false);
            if is_timeout {
                tracing::warn!(
                    op = op,
                    context = context,
                    graph = gname,
                    timeout_secs = GRAPH_STATEMENT_TIMEOUT_SECS,
                    "graph write timed out — chunks remain indexed; symbol graph for this op is partial or missing."
                );
                Ok(())
            } else {
                Err(e)
            }
        }
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
/// PREPARE/EXECUTE per distinct node label (≤4 round-trips total).
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
        let agtype_json = params.to_string();
        let stmt = format!("muninn_upsert_{}_{}", label.to_lowercase(), Uuid::new_v4().simple());
        // label and relation_label are &'static str from closed match arms — never user input.
        let cypher = format!(
            r#"UNWIND $rows AS r
               MERGE (n:{label} {{chunk_id: r.chunk_id}})
               SET n.name = r.name,
                   n.kind = '{label}',
                   n.file_path = r.file_path,
                   n.start_line = r.start_line,
                   n.end_line = r.end_line"#,
        );
        let prepare = format!(
            "PREPARE {stmt}(agtype) AS SELECT * FROM ag_catalog.cypher('{gname}', $$ {cypher} $$, $1) AS (v ag_catalog.agtype)"
        );
        exec_cypher_write_with_timeout(
            client,
            &gname,
            &stmt,
            &prepare,
            &agtype_json,
            "upsert_symbol_nodes",
            label,
        )
        .await?;
    }
    Ok(())
}

/// Batch-upsert directed edges into the per-repo graph using one
/// PREPARE/EXECUTE per distinct relation type (≤4 round-trips).
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
        let agtype_json = params.to_string();
        let stmt = format!("muninn_upsert_edge_{}_{}", rel.to_lowercase(), Uuid::new_v4().simple());
        let cypher = format!(
            r#"UNWIND $rows AS r
               MATCH (a {{chunk_id: r.from}}), (b {{chunk_id: r.to}})
               MERGE (a)-[:{rel}]->(b)"#,
        );
        let prepare = format!(
            "PREPARE {stmt}(agtype) AS SELECT * FROM ag_catalog.cypher('{gname}', $$ {cypher} $$, $1) AS (v ag_catalog.agtype)"
        );
        exec_cypher_write_with_timeout(
            client,
            &gname,
            &stmt,
            &prepare,
            &agtype_json,
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
    let agtype_json = params.to_string();
    let stmt = format!("muninn_del_file_{}", Uuid::new_v4().simple());
    let prepare = format!(
        "PREPARE {stmt}(agtype) AS SELECT * FROM ag_catalog.cypher('{gname}', \
         $$ MATCH (n {{file_path: $sym_file_path}}) DETACH DELETE n $$, \
         $1) AS (v ag_catalog.agtype)"
    );
    exec_cypher_write_with_timeout(
        client,
        &gname,
        &stmt,
        &prepare,
        &agtype_json,
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
    let agtype_json = params.to_string();

    // edge_type is a &'static str from a closed match — never user input.
    let cypher = if incoming {
        format!(
            r#"MATCH (a)-[:{edge_type}]->(b {{name: $sym_name}})
               RETURN {{chunk_id: a.chunk_id, name: a.name, file_path: a.file_path,
                        kind: a.kind, start_line: a.start_line, end_line: a.end_line}}"#,
        )
    } else {
        format!(
            r#"MATCH (a {{name: $sym_name}})-[:{edge_type}]->(b)
               RETURN {{chunk_id: b.chunk_id, name: b.name, file_path: b.file_path,
                        kind: b.kind, start_line: b.start_line, end_line: b.end_line}}"#,
        )
    };

    let stmt = format!("muninn_qrel_{}", Uuid::new_v4().simple());
    let prepare = format!(
        "PREPARE {stmt}(agtype) AS SELECT r::text \
         FROM ag_catalog.cypher('{gname}', $$ {cypher} $$, $1) AS (r ag_catalog.agtype)"
    );

    client.simple_query(&prepare).await?;
    let exec = format!("EXECUTE {}('{}')", stmt, sql_esc(&agtype_json));
    let msgs = client.simple_query(&exec).await;
    let _ = client.simple_query(&format!("DEALLOCATE {}", stmt)).await;
    let msgs = msgs?;

    let mut symbols = vec![];
    for msg in msgs {
        if let tokio_postgres::SimpleQueryMessage::Row(row) = msg {
            let raw = row.get(0).unwrap_or_default();
            let map: serde_json::Value =
                serde_json::from_str(raw).unwrap_or(serde_json::Value::Null);

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
        let params = serde_json::json!({"rows": [{"chunk_id": "write-test-uuid", "name": "write_test", "file_path": "/test.rs", "start_line": 1, "end_line": 5}]});
        let agtype_json = params.to_string();
        let stmt = format!("test_write_{}", Uuid::new_v4().simple());
        let prepare = format!(
            "PREPARE {stmt}(agtype) AS SELECT * FROM ag_catalog.cypher('{gname}', \
             $$ UNWIND $rows AS r MERGE (n:Function {{chunk_id: r.chunk_id}}) \
             SET n.name = r.name, n.kind = 'Function', n.file_path = r.file_path, \
             n.start_line = r.start_line, n.end_line = r.end_line $$, \
             $1) AS (v ag_catalog.agtype)"
        );
        age_execute(&client, &stmt, &prepare, &agtype_json)
            .await
            .expect("MERGE via PREPARE/EXECUTE should succeed");

        let read_params = serde_json::json!({"chunk_id": "write-test-uuid"});
        let read_stmt = format!("test_read_{}", Uuid::new_v4().simple());
        let read_prepare = format!(
            "PREPARE {read_stmt}(agtype) AS SELECT r::text \
             FROM ag_catalog.cypher('{gname}', \
             $$ MATCH (n {{chunk_id: $chunk_id}}) RETURN {{name: n.name, kind: n.kind}} $$, \
             $1) AS r"
        );
        client.simple_query(&read_prepare).await.expect("prepare read");
        let exec = format!("EXECUTE {}('{}')", read_stmt, sql_esc(&read_params.to_string()));
        let msgs = client.simple_query(&exec).await.expect("execute read");
        let _ = client.simple_query(&format!("DEALLOCATE {read_stmt}")).await;

        let rows: Vec<_> = msgs.iter().filter_map(|m| {
            if let tokio_postgres::SimpleQueryMessage::Row(r) = m { Some(r) } else { None }
        }).collect();
        assert_eq!(rows.len(), 1, "node should have been written");
        let raw = rows[0].get(0).unwrap();
        let map: serde_json::Value = serde_json::from_str(raw).unwrap();
        assert_eq!(map.get("name").and_then(|v| v.as_str()).unwrap_or(""), "write_test");
    }
}
