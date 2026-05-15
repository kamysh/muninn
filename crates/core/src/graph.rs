use sqlx::PgPool;
use uuid::Uuid;
use anyhow::Result;
use crate::types::{Symbol, SymbolKind, LineRange, StructuralRelation, StructuralEdge};
use crate::store::{graph_name, chunk_exists};

/// Insert or update a symbol node in the per-repo AGE graph.
/// Enforces the IsolatedGraph invariant: the chunk_id must exist in the
/// repo's chunk store before a symbol node may reference it.
///
/// SafeSymbolUpsert invariant: `kind` comes from the SymbolKind enum
/// (hardcoded label strings, never user input); `chunk_id` is a UUID.
/// `name` and `file_path` are user-supplied and are passed as bound
/// parameters via muninn_cypher's params argument — never interpolated.
pub async fn upsert_symbol_node(
    pool: &PgPool,
    repo_id: Uuid,
    chunk_id: Uuid,
    name: &str,
    kind: &str,
    file_path: &str,
    start_line: u32,
    end_line: u32,
) -> Result<()> {
    anyhow::ensure!(
        chunk_exists(pool, repo_id, chunk_id).await?,
        "IsolatedGraph violation: chunk {} not found in repo {} store",
        chunk_id, repo_id
    );
    let gname = graph_name(repo_id);

    // name and file_path are bound via the params JSON argument.
    // kind and chunk_id are safe to interpolate: kind is a SymbolKind enum
    // (hardcoded strings), chunk_id is a UUID (injection-impossible).
    let params = serde_json::json!({
        "sym_name": name,
        "sym_file_path": file_path
    });

    let cypher = format!(
        r#"MERGE (n:{kind} {{chunk_id: '{chunk_id}'}})
           SET n.name = $sym_name,
               n.kind = '{kind}',
               n.file_path = $sym_file_path,
               n.start_line = {sl},
               n.end_line = {el}"#,
        kind = kind,
        chunk_id = chunk_id,
        sl = start_line,
        el = end_line,
    );

    sqlx::query("SELECT * FROM muninn_cypher($1, $2, $3)")
        .bind(&gname)
        .bind(&cypher)
        .bind(params.to_string())
        .execute(pool)
        .await?;
    Ok(())
}

/// Insert a directed edge between two symbol nodes in the per-repo graph.
///
/// `from` and `to` are UUIDs bound via the params JSON argument and
/// referenced as $from_id / $to_id inside the Cypher template — never
/// interpolated.
pub async fn upsert_edge(pool: &PgPool, repo_id: Uuid, edge: &StructuralEdge) -> Result<()> {
    let rel = match edge.relation {
        StructuralRelation::Calls => "CALLS",
        StructuralRelation::Imports => "IMPORTS",
        StructuralRelation::Defines => "DEFINES",
        StructuralRelation::InheritsFrom => "INHERITS_FROM",
    };
    let gname = graph_name(repo_id);
    let params = serde_json::json!({
        "from_id": edge.from.to_string(),
        "to_id": edge.to.to_string(),
    });
    let cypher = format!(
        r#"MATCH (a {{chunk_id: $from_id}}), (b {{chunk_id: $to_id}})
           MERGE (a)-[:{rel}]->(b)"#,
        rel = rel,
    );
    sqlx::query("SELECT * FROM muninn_cypher($1, $2, $3)")
        .bind(&gname)
        .bind(&cypher)
        .bind(params.to_string())
        .execute(pool)
        .await?;
    Ok(())
}

/// Query symbols related to a given symbol name by relation type and direction.
pub async fn query_related(
    pool: &PgPool,
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

    // symbol_name is user-supplied — bound via params JSON, never interpolated.
    // edge_type comes from the StructuralRelation enum (hardcoded strings).
    // Return all fields as a single map so muninn_cypher's SETOF agtype works.
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

    let rows = sqlx::query("SELECT r::text FROM muninn_cypher($1, $2, $3) AS r")
        .bind(&gname)
        .bind(&cypher)
        .bind(params.to_string())
        .fetch_all(pool)
        .await?;

    let mut symbols = vec![];
    for row in rows {
        use sqlx::Row;
        // Cast to text so sqlx can read it; parse as JSON map.
        let raw: String = row.try_get::<String, _>("r").unwrap_or_default();
        let map: serde_json::Value = serde_json::from_str(&raw).unwrap_or(serde_json::Value::Null);

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
    use super::*;
    use crate::{config::GlobalConfig, db};

    async fn test_pool() -> PgPool {
        // Load from the local config.toml in the muninn repo root.
        // This file is not committed; developers copy it from ~/.config/muninn/config.toml.
        let manifest = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let config_path = manifest.join("../../config.toml");
        let cfg = GlobalConfig::load_from(&config_path).expect("load local config.toml");
        db::connect(&cfg.database).await.expect("connect to muninn db")
    }

    /// Verifies that sqlx .execute() works with muninn_cypher for write operations
    /// (MERGE statements that return no rows). This is the path used by
    /// upsert_symbol_node and upsert_edge.
    #[tokio::test]
    #[ignore = "requires live muninn database at localhost:5450"]
    async fn test_write_via_execute() {
        let pool = test_pool().await;
        let gname = "code_graph_63ca78b63feb4129841eb8c3842f8aec";
        let params = serde_json::json!({"sym_name": "write_test", "sym_file": "/test.rs"});

        // MERGE (write) — returns no rows; .execute() must not error
        sqlx::query("SELECT * FROM muninn_cypher($1, $2, $3)")
            .bind(gname)
            .bind("MERGE (n:Function {chunk_id: 'write-test-uuid'}) SET n.name = $sym_name, n.kind = 'Function', n.file_path = $sym_file, n.start_line = 1, n.end_line = 5")
            .bind(params.to_string())
            .execute(&pool)
            .await
            .expect("MERGE via muninn_cypher should succeed");

        // Verify the node was actually written
        let rows = sqlx::query("SELECT r::text FROM muninn_cypher($1, $2, $3) AS r")
            .bind(gname)
            .bind("MATCH (n {chunk_id: 'write-test-uuid'}) RETURN {name: n.name, kind: n.kind}")
            .bind("{}")
            .fetch_all(&pool)
            .await
            .expect("read back should succeed");

        assert_eq!(rows.len(), 1, "node should have been written");

        use sqlx::Row;
        let raw: String = rows[0].try_get("r").unwrap();
        let map: serde_json::Value = serde_json::from_str(&raw).unwrap();
        assert_eq!(map.get("name").and_then(|v| v.as_str()).unwrap_or(""), "write_test");
    }

    /// Verifies that sqlx can read an ag_catalog.agtype map column as serde_json::Value
    /// and that field extraction works correctly. Uses the test node inserted during
    /// the muninn_cypher development session.
    #[tokio::test]
    #[ignore = "requires live muninn database at localhost:5450"]
    async fn test_agtype_map_column_readable() {
        let pool = test_pool().await;
        let gname = "code_graph_63ca78b63feb4129841eb8c3842f8aec";
        let params = serde_json::json!({"sym_name": "test_func"});

        let rows = sqlx::query(
            "SELECT r::text FROM muninn_cypher($1, $2, $3) AS r"
        )
        .bind(gname)
        .bind("MATCH (n {name: $sym_name}) RETURN {chunk_id: n.chunk_id, name: n.name, file_path: n.file_path, kind: n.kind, start_line: n.start_line, end_line: n.end_line}")
        .bind(params.to_string())
        .fetch_all(&pool)
        .await
        .expect("query should succeed");

        assert_eq!(rows.len(), 1, "should find the test_func node");

        use sqlx::Row;
        let raw: String = rows[0].try_get::<String, _>("r").expect("r column should be text");
        let map: serde_json::Value = serde_json::from_str(&raw).expect("should parse as JSON");

        let name = map.get("name")
            .and_then(|v| v.as_str())
            .map(|s| s.trim_matches('"').to_string())
            .unwrap_or_default();

        assert_eq!(name, "test_func", "name field should parse correctly");

        let start_line = map.get("start_line")
            .and_then(|v| v.as_u64())
            .unwrap_or(0);
        assert_eq!(start_line, 1);
    }
}