use crate::types::{Chunk, SearchResult, LineRange};
use sqlx::PgPool;
use uuid::Uuid;
use anyhow::Result;
use std::collections::HashMap;

pub async fn fulltext_search(
    pool: &PgPool,
    query: &str,
    repo_id: Option<Uuid>,
    limit: i64,
) -> Result<Vec<SearchResult>> {
    use sqlx::Row;
    let rows = sqlx::query(
        r#"
        SELECT id, repo_id, file_path, start_line, end_line, content,
               ts_rank(ts_vector, plainto_tsquery('english', $1)) AS score
        FROM chunks
        WHERE ts_vector @@ plainto_tsquery('english', $1)
          AND ($2::uuid IS NULL OR repo_id = $2)
        ORDER BY score DESC
        LIMIT $3
        "#,
    )
    .bind(query)
    .bind(repo_id)
    .bind(limit)
    .fetch_all(pool)
    .await?;

    rows.into_iter().map(|row| {
        Ok(SearchResult {
            score: row.try_get::<f32, _>("score")?,
            chunk: Chunk {
                id: row.try_get("id")?,
                repo_id: row.try_get("repo_id")?,
                file_path: row.try_get("file_path")?,
                range: LineRange {
                    start: row.try_get::<i32, _>("start_line")? as u32,
                    end: row.try_get::<i32, _>("end_line")? as u32,
                },
                content: row.try_get("content")?,
                embedding: None,
            },
        })
    }).collect()
}

pub async fn semantic_search(
    pool: &PgPool,
    query_embedding: &[f32],
    repo_id: Option<Uuid>,
    limit: i64,
) -> Result<Vec<SearchResult>> {
    use sqlx::Row;
    // Format embedding as pgvector literal: '[f1,f2,...]'
    let vec_literal = format!(
        "[{}]",
        query_embedding.iter().map(|f| f.to_string()).collect::<Vec<_>>().join(",")
    );

    let rows = sqlx::query(
        r#"
        SELECT id, repo_id, file_path, start_line, end_line, content,
               (1 - (embedding <=> $1::vector))::float4 AS score
        FROM chunks
        WHERE embedding IS NOT NULL
          AND ($2::uuid IS NULL OR repo_id = $2)
        ORDER BY embedding <=> $1::vector
        LIMIT $3
        "#,
    )
    .bind(vec_literal)
    .bind(repo_id)
    .bind(limit)
    .fetch_all(pool)
    .await?;

    rows.into_iter().map(|row| {
        Ok(SearchResult {
            score: row.try_get::<f32, _>("score")?,
            chunk: Chunk {
                id: row.try_get("id")?,
                repo_id: row.try_get("repo_id")?,
                file_path: row.try_get("file_path")?,
                range: LineRange {
                    start: row.try_get::<i32, _>("start_line")? as u32,
                    end: row.try_get::<i32, _>("end_line")? as u32,
                },
                content: row.try_get("content")?,
                embedding: None,
            },
        })
    }).collect()
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
        scores.entry(id).and_modify(|e| e.0 += rrf).or_insert((rrf, result));
    }
    for (rank, result) in list_b.into_iter().enumerate() {
        let rrf = 1.0 / (K + rank as f32);
        let id = result.chunk.id;
        scores.entry(id).and_modify(|e| e.0 += rrf).or_insert((rrf, result));
    }

    let mut results: Vec<(f32, SearchResult)> = scores.into_values().collect();
    results.sort_by(|a, b| b.0.partial_cmp(&a.0).unwrap_or(std::cmp::Ordering::Equal));
    results.truncate(limit);
    results.into_iter().map(|(score, mut r)| { r.score = score; r }).collect()
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

        // id_a appears in both lists → higher combined RRF score
        let list1 = vec![make_result(id_a, 0.9), make_result(id_b, 0.8)];
        let list2 = vec![make_result(id_a, 0.7), make_result(id_c, 0.6)];

        let merged = rrf_merge(list1, list2, 3);

        assert_eq!(merged.len(), 3);
        // id_a should rank first (appears in both lists)
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
}