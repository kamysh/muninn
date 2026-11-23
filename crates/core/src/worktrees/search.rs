use super::{schema, CheckoutCoverage, Target};
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
      ORDER BY {score} {order},c.id LIMIT {limit})"
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
    Ok(
        query_snapshot(client, target, &sql, &[&target.checkout, &v, &limit])
            .await?
            .0,
    )
}

#[derive(serde::Serialize)]
pub struct SemanticCoverage {
    pub total: i64,
    pub usable: i64,
    pub pending: i64,
    pub waiting: i64,
    pub complete: bool,
    pub exact: bool,
    pub candidate_count: i64,
}

/// Read the eligible inventory and results from the same checkout snapshot.
/// HNSW provides candidates only. Both modes rank with binary64 cosine.
pub async fn semantic_search_report(
    client: &mut Client,
    target: &Target,
    query: &[f32],
    limit: i64,
    exact: bool,
) -> Result<(Vec<(SearchResult, f64)>, SemanticCoverage, CheckoutCoverage)> {
    validate(limit)?;
    ensure!(
        crate::embeddings::usable_vector(query),
        "query embedding must be finite and nonzero"
    );
    super::ensure_checkout_schema(client, target.family).await?;
    client
        .batch_execute("SET hnsw.iterative_scan = strict_order")
        .await?;
    loop {
        let tx = crate::maintenance::read(client, target.family).await?;
        let expected = visibility_epoch(&tx, target).await?;
        let view = super::checkout_coverage(&tx, target).await?;
        let hidden: Vec<_> = hidden_paths(&tx, target).await?.into_values().collect();
        let (results, coverage) = semantic_snapshot(
            &tx,
            target,
            query,
            limit,
            exact,
            SemanticScope::Checkout(&hidden),
        )
        .await?;
        tx.commit().await?;
        if visibility_epoch(client, target).await? == expected {
            return Ok((results, coverage, view));
        }
    }
}

pub async fn directory_semantic_search_report(
    client: &mut Client,
    family: Uuid,
    query: &[f32],
    limit: i64,
    exact: bool,
) -> Result<(Vec<(SearchResult, f64)>, SemanticCoverage)> {
    validate(limit)?;
    ensure!(
        crate::embeddings::usable_vector(query),
        "query embedding must be finite and nonzero"
    );
    client
        .batch_execute("SET hnsw.iterative_scan = strict_order")
        .await?;
    let tx = crate::maintenance::read(client, family).await?;
    let hidden: Vec<_> = crate::maintenance::legacy_hidden_paths(&tx, family)
        .await?
        .into_iter()
        .collect();
    let target = Target {
        family,
        checkout: family,
        graph: family,
        root: PathBuf::new(),
    };
    let result = semantic_snapshot(
        &tx,
        &target,
        query,
        limit,
        exact,
        SemanticScope::Directory(&hidden),
    )
    .await?;
    tx.commit().await?;
    Ok(result)
}

enum SemanticScope<'a> {
    Checkout(&'a Vec<Uuid>),
    Directory(&'a Vec<String>),
}

impl SemanticScope<'_> {
    fn inventory(&self, schema: &str, hidden: &str) -> String {
        match self {
            Self::Checkout(_) => common(schema, hidden),
            Self::Directory(_) => {
                format!("eligible AS (SELECT $1::uuid AS family, {hidden}::text[] AS hidden)")
            }
        }
    }

    fn predicate(&self) -> &'static str {
        match self {
            Self::Checkout(_) => "file_version=ANY((SELECT versions FROM eligible)::uuid[])",
            Self::Directory(_) => {
                "repo_id=(SELECT family FROM eligible) AND file_version IS NULL
                                  AND file_path <> ALL((SELECT hidden FROM eligible)::text[])"
            }
        }
    }

    fn hidden(&self) -> &(dyn tokio_postgres::types::ToSql + Sync) {
        match self {
            Self::Checkout(paths) => *paths,
            Self::Directory(paths) => *paths,
        }
    }
}

async fn semantic_snapshot(
    tx: &Transaction<'_>,
    target: &Target,
    query: &[f32],
    limit: i64,
    exact: bool,
    scope: SemanticScope<'_>,
) -> Result<(Vec<(SearchResult, f64)>, SemanticCoverage)> {
    let s = schema(target.family);
    let v = Vector::from(query.to_vec());
    let budget = (limit * 10).min(MAX_LIMIT);
    let eligible = scope.predicate();
    let usable =
        "embedding_state='embedded' AND embedding IS NOT NULL AND vector_norm(embedding)>0";
    let pool_bound = if exact {
        ""
    } else {
        "ORDER BY embedding <=> $2 LIMIT $4"
    };
    let sql = format!(
        "WITH {}, pool AS MATERIALIZED (
            SELECT id,embedding FROM {s}.chunks WHERE {eligible} AND {usable} {pool_bound}
        ), scored AS MATERIALIZED (
            SELECT p.id, LEAST(1::float8, a.dot/(sqrt(a.left_norm)*sqrt(a.right_norm))) AS cosine
            FROM pool p CROSS JOIN LATERAL (
                SELECT sum(x::float8*y::float8 ORDER BY n DESC) AS dot,
                       sum(x::float8*x::float8 ORDER BY n DESC) AS left_norm,
                       sum(y::float8*y::float8 ORDER BY n DESC) AS right_norm
                FROM unnest(p.embedding::real[], $2::public.vector::real[]) WITH ORDINALITY AS w(x,y,n)
            ) a
        )
        SELECT c.*,r.cosine,r.cosine::real AS score, pool_size.examined
        FROM (SELECT count(*) AS examined FROM pool) pool_size
        LEFT JOIN (SELECT id,cosine FROM scored WHERE cosine>0 ORDER BY cosine DESC,id LIMIT $3) r ON true
        LEFT JOIN {s}.chunks c ON c.id=r.id ORDER BY r.cosine DESC,r.id",
        scope.inventory(&s, if exact { "$4" } else { "$5" })
    );
    let count_sql = format!(
        "WITH {} SELECT count(*) AS total, count(*) FILTER (WHERE {usable}) AS usable,
          count(*) FILTER (WHERE embedding_state='pending') AS pending
          FROM {s}.chunks WHERE {eligible}",
        scope.inventory(&s, "$2")
    );
    let hidden = scope.hidden();
    let count = tx
        .query_one(&count_sql, &[&target.checkout, hidden])
        .await?;
    let total: i64 = count.get("total");
    let usable: i64 = count.get("usable");
    let pending: i64 = count.get("pending");
    let mut found = if exact {
        tx.query(&sql, &[&target.checkout, &v, &limit, hidden])
            .await?
    } else {
        tx.query(&sql, &[&target.checkout, &v, &limit, &budget, hidden])
            .await?
    };
    let candidate_count = found[0].get("examined");
    found.retain(|row| row.get::<_, Option<f64>>("cosine").is_some());
    let scores: Vec<f64> = found.iter().map(|row| row.get("cosine")).collect();
    let coverage = SemanticCoverage {
        total,
        usable,
        pending,
        waiting: total - usable - pending,
        complete: total == usable,
        exact,
        candidate_count,
    };
    Ok((
        rows(target, found)?.into_iter().zip(scores).collect(),
        coverage,
    ))
}
pub async fn fulltext_search(
    client: &mut Client,
    target: &Target,
    query: &str,
    limit: i64,
) -> Result<Vec<SearchResult>> {
    Ok(fulltext_search_report(client, target, query, limit)
        .await?
        .0)
}

pub async fn fulltext_search_report(
    client: &mut Client,
    target: &Target,
    query: &str,
    limit: i64,
) -> Result<(Vec<SearchResult>, CheckoutCoverage)> {
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
    Ok(hybrid_search_report(client, target, vector, query, limit)
        .await?
        .0)
}

pub async fn hybrid_search_report(
    client: &mut Client,
    target: &Target,
    vector: &[f32],
    query: &str,
    limit: i64,
) -> Result<(Vec<SearchResult>, CheckoutCoverage)> {
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
) -> Result<(Vec<SearchResult>, CheckoutCoverage)> {
    client
        .batch_execute("SET hnsw.iterative_scan = strict_order")
        .await?;
    loop {
        let tx = crate::maintenance::read(client, target.family).await?;
        let expected = visibility_epoch(&tx, target).await?;
        let view = super::checkout_coverage(&tx, target).await?;
        let hidden: Vec<_> = hidden_paths(&tx, target).await?.into_values().collect();
        let mut params = args.to_vec();
        params.push(&hidden);
        let found = tx.query(sql, &params).await?;
        tx.commit().await?;
        // The read pins its checkout snapshot. A changed policy or Git
        // selection request must be applied before releasing those results.
        if visibility_epoch(client, target).await? == expected {
            return Ok((rows(target, found)?, view));
        }
    }
}
