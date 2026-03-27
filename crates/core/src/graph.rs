use sqlx::PgPool;
use uuid::Uuid;
use anyhow::Result;
use crate::types::{Symbol, SymbolKind, LineRange, StructuralRelation, StructuralEdge};

/// Insert or update a symbol node in the AGE code_graph.
/// Uses Cypher via ag_catalog.cypher().
pub async fn upsert_symbol_node(
    pool: &PgPool,
    chunk_id: Uuid,
    name: &str,
    kind: &str,
    file_path: &str,
    start_line: u32,
    end_line: u32,
) -> Result<()> {
    // AGE Cypher is executed via the cypher() function in ag_catalog
    // Parameters cannot be bound directly in Cypher — values are interpolated
    // into the query string (safe here because inputs come from parsed source code)
    let name_escaped = name.replace('\'', "\\'");
    let file_path_escaped = file_path.replace('\'', "\\'");

    let sql = format!(
        r#"SELECT * FROM ag_catalog.cypher('code_graph', $$
            MERGE (n:{kind} {{chunk_id: '{chunk_id}'}})
            SET n.name = '{name}',
                n.kind = '{kind}',
                n.file_path = '{fp}',
                n.start_line = {sl},
                n.end_line = {el}
        $$) AS (result ag_catalog.agtype)"#,
        kind = kind,
        chunk_id = chunk_id,
        name = name_escaped,
        fp = file_path_escaped,
        sl = start_line,
        el = end_line,
    );

    sqlx::query(&sql).execute(pool).await?;
    Ok(())
}

/// Insert a directed edge between two symbol nodes.
pub async fn upsert_edge(
    pool: &PgPool,
    edge: &StructuralEdge,
) -> Result<()> {
    let rel = match edge.relation {
        StructuralRelation::Calls => "CALLS",
        StructuralRelation::Imports => "IMPORTS",
        StructuralRelation::Defines => "DEFINES",
        StructuralRelation::InheritsFrom => "INHERITS_FROM",
    };
    upsert_edge_raw(pool, edge.from, edge.to, rel).await
}

/// Private helper: insert an edge by raw UUIDs and relation string.
async fn upsert_edge_raw(
    pool: &PgPool,
    from_chunk_id: Uuid,
    to_chunk_id: Uuid,
    relation: &str,
) -> Result<()> {
    let sql = format!(
        r#"SELECT * FROM ag_catalog.cypher('code_graph', $$
            MATCH (a {{chunk_id: '{from}'}}), (b {{chunk_id: '{to}'}})
            MERGE (a)-[:{rel}]->(b)
        $$) AS (result ag_catalog.agtype)"#,
        from = from_chunk_id,
        to = to_chunk_id,
        rel = relation,
    );

    sqlx::query(&sql).execute(pool).await?;
    Ok(())
}

/// Query symbols related to a given symbol name by relation type and direction.
pub async fn query_related(
    pool: &PgPool,
    symbol_name: &str,
    relation: StructuralRelation,
    incoming: bool,
) -> Result<Vec<Symbol>> {
    let name_escaped = symbol_name.replace('\'', "\\'");

    let edge_type = match relation {
        StructuralRelation::Calls => "CALLS",
        StructuralRelation::Imports => "IMPORTS",
        StructuralRelation::Defines => "DEFINES",
        StructuralRelation::InheritsFrom => "INHERITS_FROM",
    };

    let cypher = if incoming {
        format!(
            r#"MATCH (a)-[:{edge}]->(b {{name: '{name}'}})
               RETURN a.chunk_id AS chunk_id, a.name AS name,
                      a.file_path AS file_path, a.kind AS kind,
                      a.start_line AS start_line, a.end_line AS end_line"#,
            edge = edge_type, name = name_escaped
        )
    } else {
        format!(
            r#"MATCH (a {{name: '{name}'}})-[:{edge}]->(b)
               RETURN b.chunk_id AS chunk_id, b.name AS name,
                      b.file_path AS file_path, b.kind AS kind,
                      b.start_line AS start_line, b.end_line AS end_line"#,
            name = name_escaped, edge = edge_type
        )
    };

    let sql = format!(
        r#"SELECT * FROM ag_catalog.cypher('code_graph', $$ {cypher} $$)
           AS (chunk_id ag_catalog.agtype, name ag_catalog.agtype,
               file_path ag_catalog.agtype, kind ag_catalog.agtype,
               start_line ag_catalog.agtype, end_line ag_catalog.agtype)"#,
        cypher = cypher
    );

    let rows = sqlx::query(&sql).fetch_all(pool).await?;

    let mut symbols = vec![];
    for row in rows {
        use sqlx::Row;
        // AGE returns agtype values as JSON-encoded strings
        let name: String = parse_agtype_string(row.try_get::<serde_json::Value, _>("name").ok());
        let file_path: String = parse_agtype_string(row.try_get::<serde_json::Value, _>("file_path").ok());
        let kind_str: String = parse_agtype_string(row.try_get::<serde_json::Value, _>("kind").ok());
        let start_line: u32 = parse_agtype_u32(row.try_get::<serde_json::Value, _>("start_line").ok());
        let end_line: u32 = parse_agtype_u32(row.try_get::<serde_json::Value, _>("end_line").ok());
        let chunk_id: Uuid = row.try_get::<serde_json::Value, _>("chunk_id")
            .ok()
            .and_then(|v| v.as_str().and_then(|s| s.trim_matches('"').parse().ok()))
            .unwrap_or_else(Uuid::nil);

        let kind = parse_symbol_kind(&kind_str);

        symbols.push(Symbol {
            name,
            kind,
            file_path,
            range: LineRange { start: start_line, end: end_line },
            chunk_id,
        });
    }
    Ok(symbols)
}

fn parse_symbol_kind(s: &str) -> SymbolKind {
    match s {
        "Function" => SymbolKind::Function,
        "Class"    => SymbolKind::Class,
        "Module"   => SymbolKind::Module,
        "Import"   => SymbolKind::Import,
        _          => SymbolKind::Function, // fallback
    }
}

fn parse_agtype_string(v: Option<serde_json::Value>) -> String {
    v.and_then(|v| v.as_str().map(|s| s.trim_matches('"').to_string()))
     .unwrap_or_default()
}

fn parse_agtype_u32(v: Option<serde_json::Value>) -> u32 {
    v.and_then(|v| v.as_u64()).unwrap_or(0) as u32
}