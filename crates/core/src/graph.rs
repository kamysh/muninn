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
/// parameters via the AGE jsonb params argument — never interpolated.
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

    // name and file_path are bound via the AGE jsonb params argument ($1::jsonb).
    // They are referenced as $name / $file_path inside the Cypher template,
    // never interpolated into the string — this closes the Cypher injection surface.
    let params = serde_json::json!({
        "sym_name": name,
        "sym_file_path": file_path
    });

    let sql = format!(
        r#"SELECT * FROM ag_catalog.cypher('{gname}', $$
            MERGE (n:{kind} {{chunk_id: '{chunk_id}'}})
            SET n.name = $sym_name,
                n.kind = '{kind}',
                n.file_path = $sym_file_path,
                n.start_line = {sl},
                n.end_line = {el}
        $$, $1::jsonb) AS (result ag_catalog.agtype)"#,
        gname = gname,
        kind = kind,
        chunk_id = chunk_id,
        sl = start_line,
        el = end_line,
    );

    sqlx::query(&sql)
        .bind(params.to_string())
        .execute(pool)
        .await?;
    Ok(())
}

/// Insert a directed edge between two symbol nodes in the per-repo graph.
///
/// `from` and `to` are UUIDs bound via the AGE jsonb params argument ($1::jsonb)
/// and referenced as $from_id / $to_id inside the Cypher template — consistent
/// with the SafeSymbolQuery binding pattern used in query_related.
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
    let sql = format!(
        r#"SELECT * FROM ag_catalog.cypher('{gname}', $$
            MATCH (a {{chunk_id: $from_id}}), (b {{chunk_id: $to_id}})
            MERGE (a)-[:{rel}]->(b)
        $$, $1::jsonb) AS (result ag_catalog.agtype)"#,
        gname = gname,
        rel = rel,
    );
    sqlx::query(&sql)
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

    // symbol_name is user-supplied — bound via AGE jsonb params, never interpolated.
    // edge_type comes from the StructuralRelation enum (hardcoded strings).
    let params = serde_json::json!({ "sym_name": symbol_name });

    let cypher = if incoming {
        format!(
            r#"MATCH (a)-[:{edge}]->(b {{name: $sym_name}})
               RETURN a.chunk_id AS chunk_id, a.name AS name,
                      a.file_path AS file_path, a.kind AS kind,
                      a.start_line AS start_line, a.end_line AS end_line"#,
            edge = edge_type,
        )
    } else {
        format!(
            r#"MATCH (a {{name: $sym_name}})-[:{edge}]->(b)
               RETURN b.chunk_id AS chunk_id, b.name AS name,
                      b.file_path AS file_path, b.kind AS kind,
                      b.start_line AS start_line, b.end_line AS end_line"#,
            edge = edge_type
        )
    };

    let sql = format!(
        r#"SELECT * FROM ag_catalog.cypher('{gname}', $$ {cypher} $$, $1::jsonb)
           AS (chunk_id ag_catalog.agtype, name ag_catalog.agtype,
               file_path ag_catalog.agtype, kind ag_catalog.agtype,
               start_line ag_catalog.agtype, end_line ag_catalog.agtype)"#,
        gname = gname,
        cypher = cypher
    );

    let rows = sqlx::query(&sql)
        .bind(params.to_string())
        .fetch_all(pool)
        .await?;

    let mut symbols = vec![];
    for row in rows {
        use sqlx::Row;
        let name: String = parse_agtype_string(row.try_get::<serde_json::Value, _>("name").ok(), "name");
        let file_path: String =
            parse_agtype_string(row.try_get::<serde_json::Value, _>("file_path").ok(), "file_path");
        let kind_str: String =
            parse_agtype_string(row.try_get::<serde_json::Value, _>("kind").ok(), "kind");
        let start_line: u32 =
            parse_agtype_u32(row.try_get::<serde_json::Value, _>("start_line").ok(), "start_line");
        let end_line: u32 =
            parse_agtype_u32(row.try_get::<serde_json::Value, _>("end_line").ok(), "end_line");
        let chunk_id: Uuid = row
            .try_get::<serde_json::Value, _>("chunk_id")
            .ok()
            .and_then(|v| v.as_str().and_then(|s| s.trim_matches('"').parse().ok()))
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

fn parse_agtype_string(v: Option<serde_json::Value>, field: &str) -> String {
    match v.and_then(|v| v.as_str().map(|s| s.trim_matches('"').to_string())) {
        Some(s) => s,
        None => {
            tracing::warn!("AGE response: failed to parse string field '{}'", field);
            String::new()
        }
    }
}

fn parse_agtype_u32(v: Option<serde_json::Value>, field: &str) -> u32 {
    match v.and_then(|v| v.as_u64()) {
        Some(n) => n as u32,
        None => {
            tracing::warn!("AGE response: failed to parse u32 field '{}'", field);
            0
        }
    }
}