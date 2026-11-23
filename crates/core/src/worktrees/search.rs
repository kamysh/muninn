use super::{schema, Target};
use crate::{search::MAX_LIMIT, types::*};
use anyhow::{ensure, Result};
use pgvector::Vector;
use std::{collections::BTreeMap, path::PathBuf};
use tokio_postgres::{Client, GenericClient, Row, Transaction};
use uuid::Uuid;

fn common(s: &str, hidden: &str) -> String {
    format!(
        "eligible AS MATERIALIZED (
      SELECT COALESCE(array_agg(m.version),ARRAY[]::uuid[]) AS versions
      FROM {s}.checkout_file_versions m JOIN {s}.checkouts c ON c.id=m.checkout
      WHERE c.id=$1 AND c.registration_state='active' AND c.indexed_at IS NOT NULL
        AND m.version <> ALL({hidden}::uuid[]))"
    )
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
    format!(
        "{prefix} AS MATERIALIZED (SELECT c.id,{score} AS score FROM {s}.chunks c
      WHERE c.file_version=ANY((SELECT versions FROM eligible)::uuid[]) AND {filter}
      ORDER BY {score} {order} LIMIT {limit})"
    )
}

pub(super) async fn hidden_paths(
    tx: &Transaction<'_>,
    target: &Target,
) -> Result<BTreeMap<String, Uuid>> {
    let direct = crate::maintenance::generation(tx, target.family, target.checkout).await?;
    let family = crate::maintenance::generation(tx, target.family, target.family).await?;
    if direct.is_none() && family.is_none() {
        return Ok(BTreeMap::new());
    }
    let s = schema(target.family);
    let manifest = super::manifest(tx, &s, target.checkout).await?;
    let policy = crate::family_policy::runtime::policy(tx, target.family).await?;
    let selection =
        crate::family_policy::runtime::Selection::new(&target.root, policy.as_ref(), &[], &[])?;
    let paths: Vec<PathBuf> = manifest.keys().map(PathBuf::from).collect();
    let ignored = crate::git_ignore::check(&target.root, &paths).await?;
    Ok(manifest
        .into_iter()
        .zip(paths)
        .zip(ignored)
        .filter_map(|(((name, version), path), ignored)| {
            use crate::pipeline::Decision::Drop;
            let excluded = selection.classify_with_git(&path, false, ignored) == Drop
                || path
                    .ancestors()
                    .skip(1)
                    .filter(|p| !p.as_os_str().is_empty())
                    .any(|parent| selection.classify(parent, true) == Drop);
            excluded.then_some((name, version))
        })
        .collect())
}

pub(super) async fn visibility_epoch(
    client: &impl GenericClient,
    target: &Target,
) -> Result<(Option<i64>, Option<i64>, Option<i64>)> {
    let s = schema(target.family);
    let row = client
        .query_one(
            &format!(
                "SELECT (SELECT current_revision FROM {s}.family_policy WHERE singleton),
          (SELECT requested FROM {s}.selection_maintenance WHERE target=$1),
          (SELECT requested FROM {s}.selection_maintenance WHERE target=$2)"
            ),
            &[&target.checkout, &target.family],
        )
        .await?;
    Ok((row.get(0), row.get(1), row.get(2)))
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
                    embedding_state: match row.try_get::<_, &str>("embedding_state")? {
                        "pending" => EmbeddingState::Pending,
                        "embedded" => EmbeddingState::Embedded,
                        _ => EmbeddingState::Absent,
                    },
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
    client: &mut Client,
    target: &Target,
    query: &[f32],
    limit: i64,
) -> Result<Vec<SearchResult>> {
    validate(limit)?;
    super::ensure_checkout_schema(client, target.family).await?;
    let s = schema(target.family);
    let v = Vector::from(query.to_vec());
    let sql=format!("WITH {},{} SELECT c.*, (1-r.score)::real AS score FROM sem r JOIN {s}.chunks c ON c.id=r.id WHERE r.score<1 ORDER BY r.score,c.id",common(&s,"$4"),branches(&s,true,"$2","$3","sem"));
    query_snapshot(client, target, &sql, &[&target.checkout, &v, &limit]).await
}
pub async fn fulltext_search(
    client: &mut Client,
    target: &Target,
    query: &str,
    limit: i64,
) -> Result<Vec<SearchResult>> {
    validate(limit)?;
    super::ensure_checkout_schema(client, target.family).await?;
    let s = schema(target.family);
    let sql=format!("WITH {},{} SELECT c.*,r.score::real AS score FROM txt r JOIN {s}.chunks c ON c.id=r.id ORDER BY r.score DESC,c.id",common(&s,"$4"),branches(&s,false,"$2","$3","txt"));
    query_snapshot(client, target, &sql, &[&target.checkout, &query, &limit]).await
}
/// One statement ranks both modalities against the same selected view.
pub async fn hybrid_search(
    client: &mut Client,
    target: &Target,
    vector: &[f32],
    query: &str,
    limit: i64,
) -> Result<Vec<SearchResult>> {
    validate(limit)?;
    super::ensure_checkout_schema(client, target.family).await?;
    let s = schema(target.family);
    let v = Vector::from(vector.to_vec());
    let candidates = (limit * 10).min(MAX_LIMIT);
    let sql=format!("WITH {},{}, {}, ranks AS (
        SELECT id,1.0/(59+row_number() OVER(ORDER BY score,id)) AS contribution FROM sem WHERE score<1
        UNION ALL SELECT id,1.0/(59+row_number() OVER(ORDER BY score DESC,id)) FROM txt),
        ranked AS (SELECT id,sum(contribution)::real AS score FROM ranks GROUP BY id ORDER BY score DESC,id LIMIT $5)
        SELECT c.*,r.score FROM ranked r JOIN {s}.chunks c ON c.id=r.id ORDER BY r.score DESC,c.id",
        common(&s,"$6"),branches(&s,true,"$2","$4","sem"),branches(&s,false,"$3","$4","txt"));
    query_snapshot(
        client,
        target,
        &sql,
        &[&target.checkout, &v, &query, &candidates, &limit],
    )
    .await
}

async fn query_snapshot(
    client: &mut Client,
    target: &Target,
    sql: &str,
    args: &[&(dyn tokio_postgres::types::ToSql + Sync)],
) -> Result<Vec<SearchResult>> {
    client
        .batch_execute("SET hnsw.iterative_scan = strict_order")
        .await?;
    loop {
        let tx = crate::maintenance::read(client, target.family).await?;
        let expected = visibility_epoch(&tx, target).await?;
        let hidden: Vec<_> = hidden_paths(&tx, target).await?.into_values().collect();
        let mut params = args.to_vec();
        params.push(&hidden);
        let found = tx.query(sql, &params).await?;
        tx.commit().await?;
        // The read pins its checkout snapshot. A changed policy or Git
        // selection request must be applied before releasing those results.
        if visibility_epoch(client, target).await? == expected {
            return rows(target, found);
        }
    }
}
