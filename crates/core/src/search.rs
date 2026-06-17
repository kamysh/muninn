use crate::store::chunks_table;
use crate::types::{Chunk, LineRange, SearchResult};
use anyhow::Result;
use pgvector::Vector;
use std::collections::HashMap;
use tokio_postgres::Client;
use uuid::Uuid;

/// Server-enforced ceiling on query limits (spec: Muninn.Search.MAX_LIMIT).
/// Without this, a caller supplying limit=10⁹ would attempt a billion-row fetch.
pub const MAX_LIMIT: i64 = 1000;

/// Validate a search limit against the spec's ValidLimit invariant: 1 ≤ limit ≤ MAX_LIMIT.
fn validate_limit(limit: i64) -> Result<()> {
    anyhow::ensure!(limit >= 1, "limit must be at least 1");
    anyhow::ensure!(limit <= MAX_LIMIT, "limit must not exceed {}", MAX_LIMIT);
    Ok(())
}

pub async fn fulltext_search(
    client: &Client,
    query: &str,
    repo_id: Uuid,
    limit: i64,
) -> Result<Vec<SearchResult>> {
    validate_limit(limit)?;
    let table = chunks_table(repo_id);
    let rows = client
        .query(
            &format!(
                r#"
        SELECT id, repo_id, file_path, start_line, end_line, content,
               ts_rank(ts_vector, plainto_tsquery('english', $1)) AS score
        FROM "{table}"
        WHERE ts_vector @@ plainto_tsquery('english', $1)
        ORDER BY score DESC
        LIMIT $2
        "#
            ),
            &[&query, &limit],
        )
        .await?;

    rows.into_iter()
        .map(|row| {
            Ok(SearchResult {
                score: row.try_get::<_, f32>("score")?,
                chunk: Chunk {
                    id: row.try_get("id")?,
                    repo_id: row.try_get("repo_id")?,
                    file_path: row.try_get("file_path")?,
                    range: LineRange {
                        start: row.try_get::<_, i32>("start_line")? as u32,
                        end: row.try_get::<_, i32>("end_line")? as u32,
                    },
                    content: row.try_get("content")?,
                    embedding: None,
                },
            })
        })
        .collect()
}

pub async fn semantic_search(
    client: &Client,
    query_embedding: &[f32],
    repo_id: Uuid,
    limit: i64,
) -> Result<Vec<SearchResult>> {
    validate_limit(limit)?;
    let table = chunks_table(repo_id);
    let vec = Vector::from(query_embedding.to_vec());

    let rows = client
        .query(
            &format!(
                r#"
        SELECT id, repo_id, file_path, start_line, end_line, content,
               (1 - (embedding <=> $1))::float4 AS score
        FROM "{table}"
        WHERE embedding IS NOT NULL
          AND (1 - (embedding <=> $1)) > 0.0
        ORDER BY embedding <=> $1
        LIMIT $2
        "#
            ),
            &[&vec, &limit],
        )
        .await?;

    rows.into_iter()
        .map(|row| {
            Ok(SearchResult {
                score: row.try_get::<_, f32>("score")?,
                chunk: Chunk {
                    id: row.try_get("id")?,
                    repo_id: row.try_get("repo_id")?,
                    file_path: row.try_get("file_path")?,
                    range: LineRange {
                        start: row.try_get::<_, i32>("start_line")? as u32,
                        end: row.try_get::<_, i32>("end_line")? as u32,
                    },
                    content: row.try_get("content")?,
                    embedding: None,
                },
            })
        })
        .collect()
}

/// Reciprocal Rank Fusion merge of two ranked result lists.
/// k=60 is the standard RRF constant.
pub fn rrf_merge(
    list_a: Vec<SearchResult>,
    list_b: Vec<SearchResult>,
    limit: usize,
) -> Vec<SearchResult> {
    const K: f32 = 60.0;
    let mut scores: HashMap<Uuid, (f32, SearchResult)> = HashMap::new();

    for (rank, result) in list_a.into_iter().enumerate() {
        let rrf = 1.0 / (K + rank as f32);
        let id = result.chunk.id;
        scores
            .entry(id)
            .and_modify(|e| e.0 += rrf)
            .or_insert((rrf, result));
    }
    for (rank, result) in list_b.into_iter().enumerate() {
        let rrf = 1.0 / (K + rank as f32);
        let id = result.chunk.id;
        scores
            .entry(id)
            .and_modify(|e| e.0 += rrf)
            .or_insert((rrf, result));
    }

    let mut results: Vec<(f32, SearchResult)> = scores.into_values().collect();
    results.sort_by(|a, b| b.0.partial_cmp(&a.0).unwrap_or(std::cmp::Ordering::Equal));
    results.truncate(limit);
    results
        .into_iter()
        .map(|(score, mut r)| {
            r.score = score;
            r
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{Chunk, LineRange};
    use uuid::Uuid;

    fn make_result(id: Uuid, score: f32) -> SearchResult {
        SearchResult {
            score,
            chunk: Chunk {
                id,
                repo_id: Uuid::nil(),
                file_path: "test.rs".to_string(),
                range: LineRange { start: 1, end: 1 },
                content: "fn foo() {}".to_string(),
                embedding: None,
            },
        }
    }

    #[test]
    fn rrf_merge_deduplicates_and_boosts_shared() {
        let id_a = Uuid::new_v4();
        let id_b = Uuid::new_v4();
        let id_c = Uuid::new_v4();

        let list1 = vec![make_result(id_a, 0.9), make_result(id_b, 0.8)];
        let list2 = vec![make_result(id_a, 0.7), make_result(id_c, 0.6)];

        let merged = rrf_merge(list1, list2, 3);

        assert_eq!(merged.len(), 3);
        assert_eq!(merged[0].chunk.id, id_a);
    }

    #[test]
    fn rrf_merge_respects_limit() {
        let results_a: Vec<_> = (0..5).map(|_| make_result(Uuid::new_v4(), 0.5)).collect();
        let results_b: Vec<_> = (0..5).map(|_| make_result(Uuid::new_v4(), 0.5)).collect();
        let merged = rrf_merge(results_a, results_b, 4);
        assert_eq!(merged.len(), 4);
    }

    #[test]
    fn rrf_merge_empty_lists() {
        let merged = rrf_merge(vec![], vec![], 10);
        assert!(merged.is_empty());
    }

    #[test]
    fn rrf_merge_single_list_preserves_order() {
        let ids: Vec<_> = (0..5).map(|_| uuid::Uuid::new_v4()).collect();
        let list: Vec<_> = ids.iter().map(|&id| make_result(id, 0.9)).collect();
        let merged = rrf_merge(list, vec![], 5);
        assert_eq!(merged.len(), 5);
    }

    #[test]
    fn rrf_merge_item_in_both_lists_outranks_item_in_one() {
        let shared = uuid::Uuid::new_v4();
        let only_a = uuid::Uuid::new_v4();
        let only_b = uuid::Uuid::new_v4();

        let list_a = vec![make_result(shared, 0.9), make_result(only_a, 0.8)];
        let list_b = vec![make_result(shared, 0.7), make_result(only_b, 0.6)];
        let merged = rrf_merge(list_a, list_b, 3);

        assert_eq!(merged[0].chunk.id, shared, "shared item should rank first");
    }

    #[test]
    fn rrf_merge_scores_are_positive() {
        let ids: Vec<_> = (0..3).map(|_| uuid::Uuid::new_v4()).collect();
        let list: Vec<_> = ids.iter().map(|&id| make_result(id, 0.5)).collect();
        let merged = rrf_merge(list.clone(), list, 3);
        assert!(merged.iter().all(|r| r.score > 0.0));
    }

    #[test]
    fn rrf_first_rank_uses_zero_based_index() {
        let id = uuid::Uuid::new_v4();
        let merged = rrf_merge(vec![make_result(id, 1.0)], vec![], 1);
        let expected = 1.0_f32 / 60.0;
        assert!(
            (merged[0].score - expected).abs() < 1e-6,
            "score {} != expected {}",
            merged[0].score,
            expected
        );
    }

    use quickcheck::quickcheck;

    fn arb_result(id: Uuid) -> SearchResult {
        SearchResult {
            score: 0.5,
            chunk: Chunk {
                id,
                repo_id: Uuid::nil(),
                file_path: "f.rs".into(),
                range: LineRange { start: 1, end: 1 },
                content: "x".into(),
                embedding: None,
            },
        }
    }

    quickcheck! {
        fn prop_rrf_merge_length_le_limit(n: u8, limit: u8) -> bool {
            let limit = (limit as usize).max(1);
            let n = n as usize;
            let list_a: Vec<_> = (0..n).map(|_| arb_result(Uuid::new_v4())).collect();
            let list_b: Vec<_> = (0..n).map(|_| arb_result(Uuid::new_v4())).collect();
            let merged = rrf_merge(list_a, list_b, limit);
            merged.len() <= limit
        }

        fn prop_rrf_merge_no_duplicates(n: u8) -> bool {
            let n = (n as usize).min(20);
            let ids: Vec<Uuid> = (0..n).map(|_| Uuid::new_v4()).collect();
            let list_a: Vec<_> = ids.iter().map(|&id| arb_result(id)).collect();
            let list_b: Vec<_> = ids.iter().map(|&id| arb_result(id)).collect();
            let merged = rrf_merge(list_a, list_b, n + 1);
            let mut seen = std::collections::HashSet::new();
            merged.iter().all(|r| seen.insert(r.chunk.id))
        }

        fn prop_rrf_merge_scores_positive(n: u8) -> bool {
            let n = n as usize;
            let list_a: Vec<_> = (0..n).map(|_| arb_result(Uuid::new_v4())).collect();
            let merged = rrf_merge(list_a, vec![], n + 1);
            merged.iter().all(|r| r.score > 0.0)
        }

        fn prop_rrf_merge_sorted_descending(n: u8) -> bool {
            let n = (n as usize).min(20);
            let list_a: Vec<_> = (0..n).map(|_| arb_result(Uuid::new_v4())).collect();
            let list_b: Vec<_> = (0..n).map(|_| arb_result(Uuid::new_v4())).collect();
            let merged = rrf_merge(list_a, list_b, n * 2 + 1);
            merged.windows(2).all(|w| w[0].score >= w[1].score)
        }
    }
}
