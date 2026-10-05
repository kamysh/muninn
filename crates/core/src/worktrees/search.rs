use super::{schema, Target};
use crate::{search::MAX_LIMIT, types::*};
use anyhow::{ensure, Result};
use pgvector::Vector;
use tokio_postgres::{Client, Row};

fn common(s: &str) -> String {
    format!("selected AS MATERIALIZED (SELECT id FROM {s}.checkouts WHERE id=$1 AND registration_state='active' AND indexed_at IS NOT NULL), excluded AS MATERIALIZED (SELECT COALESCE(array_agg(path),ARRAY[]::text[]) AS paths FROM {s}.file_deltas WHERE checkout=$1), delta AS MATERIALIZED (SELECT c.* FROM {s}.chunks c JOIN {s}.file_deltas d ON c.file_version=d.version WHERE d.checkout=$1 AND EXISTS(SELECT 1 FROM selected))")
}
fn branches(s: &str, semantic: bool, param: &str, limit: &str, prefix: &str) -> String {
    let (score, order, filter) = if semantic {
        (
            format!("embedding <=> {param}"),
            "ASC",
            "embedding IS NOT NULL".to_owned(),
        )
    } else {
        (
            format!("ts_rank(ts_vector,plainto_tsquery('english',{param}))"),
            "DESC",
            format!("ts_vector @@ plainto_tsquery('english',{param})"),
        )
    };
    format!("{prefix}_base AS MATERIALIZED (SELECT c.id,{score} AS score FROM {s}.chunks c WHERE in_base AND file_version IS NOT NULL AND EXISTS(SELECT 1 FROM selected) AND file_path <> ALL((SELECT paths FROM excluded)::text[]) AND {filter} ORDER BY {score} {order} LIMIT {limit}),
        {prefix}_delta AS MATERIALIZED (SELECT id,{score} AS score FROM delta WHERE {filter} ORDER BY {score} {order} LIMIT {limit}),
        {prefix} AS MATERIALIZED (SELECT * FROM (SELECT * FROM {prefix}_base UNION ALL SELECT * FROM {prefix}_delta) combined ORDER BY score {order},id LIMIT {limit})")
}
fn rows(target: &Target, rows: Vec<Row>) -> Result<Vec<SearchResult>> {
    rows.into_iter()
        .map(|row| {
            Ok(SearchResult {
                score: row.try_get("score")?,
                chunk: Chunk {
                    id: row.try_get("id")?,
                    repo_id: target.family,
                    file_path: target
                        .root
                        .join(row.try_get::<_, String>("file_path")?)
                        .to_string_lossy()
                        .into_owned(),
                    range: LineRange {
                        start: row.try_get::<_, i32>("start_line")? as u32,
                        end: row.try_get::<_, i32>("end_line")? as u32,
                    },
                    content: row.try_get("content")?,
                    embedding: None,
                    tier: if row.try_get::<_, i16>("tier")? == 2 {
                        Tier::Tier2
                    } else {
                        Tier::Tier1
                    },
                    embedding_state: EmbeddingState::Embedded,
                    content_hash: None,
                },
            })
        })
        .collect()
}
fn validate(limit: i64) -> Result<()> {
    ensure!((1..=MAX_LIMIT).contains(&limit), "invalid search limit");
    Ok(())
}

pub async fn semantic_search(
    client: &Client,
    target: &Target,
    query: &[f32],
    limit: i64,
) -> Result<Vec<SearchResult>> {
    validate(limit)?;
    client
        .batch_execute("SET hnsw.iterative_scan = strict_order")
        .await?;
    let s = schema(target.family);
    let v = Vector::from(query.to_vec());
    let sql=format!("WITH {},{} SELECT c.*, (1-r.score)::real AS score FROM sem r JOIN {s}.chunks c ON c.id=r.id WHERE r.score<1 ORDER BY r.score,c.id",common(&s),branches(&s,true,"$2","$3","sem"));
    rows(
        target,
        client.query(&sql, &[&target.checkout, &v, &limit]).await?,
    )
}
pub async fn fulltext_search(
    client: &Client,
    target: &Target,
    query: &str,
    limit: i64,
) -> Result<Vec<SearchResult>> {
    validate(limit)?;
    let s = schema(target.family);
    let sql=format!("WITH {},{} SELECT c.*,r.score::real AS score FROM txt r JOIN {s}.chunks c ON c.id=r.id ORDER BY r.score DESC,c.id",common(&s),branches(&s,false,"$2","$3","txt"));
    rows(
        target,
        client
            .query(&sql, &[&target.checkout, &query, &limit])
            .await?,
    )
}
/// One statement gives both modalities the same MVCC snapshot during base moves.
pub async fn hybrid_search(
    client: &Client,
    target: &Target,
    vector: &[f32],
    query: &str,
    limit: i64,
) -> Result<Vec<SearchResult>> {
    validate(limit)?;
    client
        .batch_execute("SET hnsw.iterative_scan = strict_order")
        .await?;
    let s = schema(target.family);
    let v = Vector::from(vector.to_vec());
    let candidates = (limit * 10).min(MAX_LIMIT);
    let sql=format!("WITH {},{}, {}, ranks AS (
        SELECT id,1.0/(59+row_number() OVER(ORDER BY score,id)) AS contribution FROM sem WHERE score<1
        UNION ALL SELECT id,1.0/(59+row_number() OVER(ORDER BY score DESC,id)) FROM txt),
        ranked AS (SELECT id,sum(contribution)::real AS score FROM ranks GROUP BY id ORDER BY score DESC,id LIMIT $5)
        SELECT c.*,r.score FROM ranked r JOIN {s}.chunks c ON c.id=r.id ORDER BY r.score DESC,c.id",
        common(&s),branches(&s,true,"$2","$4","sem"),branches(&s,false,"$3","$4","txt"));
    rows(
        target,
        client
            .query(&sql, &[&target.checkout, &v, &query, &candidates, &limit])
            .await?,
    )
}
