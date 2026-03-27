use sqlx::PgPool;
use uuid::Uuid;
use anyhow::Result;
use crate::types::{Symbol, SymbolKind, LineRange, StructuralRelation, StructuralEdge};
use crate::store::{graph_name, chunk_exists};

/// Insert or update a symbol node in the per-repo AGE graph.
/// Enforces the IsolatedGraph invariant: the chunk_id must exist in the
/// repo's chunk store before a symbol node may reference it.
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
    let name_escaped = name.replace('\'', "\\'");
    let file_path_escaped = file_path.replace('\'', "\\'");

    let sql = format!(
        r#"SELECT * FROM ag_catalog.cypher('{gname}', $$
            MERGE (n:{kind} {{chunk_id: '{chunk_id}'}})
            SET n.name = '{name}',
                n.kind = '{kind}',
                n.file_path = '{fp}',
                n.start_line = {sl},
                n.end_line = {el}
        $$) AS (result ag_catalog.agtype)"#,
        gname = gname,
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

/// Insert a directed edge between two symbol nodes in the per-repo graph.
pub async fn upsert_edge(pool: &PgPool, repo_id: Uuid, edge: &StructuralEdge) -> Result<()> {
    let rel = match edge.relation {
        StructuralRelation::Calls => "CALLS",
        StructuralRelation::Imports => "IMPORTS",
        StructuralRelation::Defines => "DEFINES",
        StructuralRelation::InheritsFrom => "INHERITS_FROM",
    };
    let gname = graph_name(repo_id);
    let sql = format!(
        r#"SELECT * FROM ag_catalog.cypher('{gname}', $$
            MATCH (a {{chunk_id: '{from}'}}), (b {{chunk_id: '{to}'}})
            MERGE (a)-[:{rel}]->(b)
        $$) AS (result ag_catalog.agtype)"#,
        gname = gname,
        from = edge.from,
        to = edge.to,
        rel = rel,
    );
    sqlx::query(&sql).execute(pool).await?;
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
            edge = edge_type,
            name = name_escaped
        )
    } else {
        format!(
            r#"MATCH (a {{name: '{name}'}})-[:{edge}]->(b)
               RETURN b.chunk_id AS chunk_id, b.name AS name,
                      b.file_path AS file_path, b.kind AS kind,
                      b.start_line AS start_line, b.end_line AS end_line"#,
            name = name_escaped,
            edge = edge_type
        )
    };

    let sql = format!(
        r#"SELECT * FROM ag_catalog.cypher('{gname}', $$ {cypher} $$)
           AS (chunk_id ag_catalog.agtype, name ag_catalog.agtype,
               file_path ag_catalog.agtype, kind ag_catalog.agtype,
               start_line ag_catalog.agtype, end_line ag_catalog.agtype)"#,
        gname = gname,
        cypher = cypher
    );

    let rows = sqlx::query(&sql).fetch_all(pool).await?;

    let mut symbols = vec![];
    for row in rows {
        use sqlx::Row;
        let name: String = parse_agtype_string(row.try_get::<serde_json::Value, _>("name").ok());
        let file_path: String =
            parse_agtype_string(row.try_get::<serde_json::Value, _>("file_path").ok());
        let kind_str: String =
            parse_agtype_string(row.try_get::<serde_json::Value, _>("kind").ok());
        let start_line: u32 =
            parse_agtype_u32(row.try_get::<serde_json::Value, _>("start_line").ok());
        let end_line: u32 =
            parse_agtype_u32(row.try_get::<serde_json::Value, _>("end_line").ok());
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

fn parse_agtype_string(v: Option<serde_json::Value>) -> String {
    v.and_then(|v| v.as_str().map(|s| s.trim_matches('"').to_string()))
        .unwrap_or_default()
}

fn parse_agtype_u32(v: Option<serde_json::Value>) -> u32 {
    v.and_then(|v| v.as_u64()).unwrap_or(0) as u32
}