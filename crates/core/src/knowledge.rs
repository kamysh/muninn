use anyhow::{Context, Result};
use chrono::{DateTime, Utc};
use pgvector::Vector;
use std::path::Path;
use tokio_postgres::{Client, GenericClient, Row};
use uuid::Uuid;

use crate::search::rrf_merge;
use crate::types::{Chunk, EmbeddingState, LineRange, SearchResult, Tier};

pub struct NoteLocation {
    path: String,
    family_path: String,
    pub family_id: Option<Uuid>,
    pub embedding_dim: Option<usize>,
    checkout_key: Option<Vec<u8>>,
    legacy_keys: Vec<String>,
}

impl NoteLocation {
    fn legacy(path: &str) -> Self {
        Self {
            path: path.into(),
            family_path: path.into(),
            family_id: None,
            embedding_dim: None,
            checkout_key: None,
            legacy_keys: vec![path.into()],
        }
    }

    pub async fn resolve(client: &Client, path: &str) -> Result<Self> {
        use crate::family_store::{self, CheckoutIdentity};
        let root = Path::new(path);
        if !root.is_absolute() || !root.try_exists()? {
            return Ok(Self::legacy(path));
        }
        let identity = CheckoutIdentity::discover(root).await?;
        let Some(family) = family_store::lookup_family(client, &identity.family).await? else {
            return Ok(Self::legacy(path));
        };
        let selected = identity.root.to_path_buf()?;
        let primary =
            crate::family_policy::runtime::root(client, family.id, Path::new(&family.legacy_path))
                .await?;
        let checkout = if family.schema_state != family_store::SchemaState::Ready {
            None
        } else if let Some(git_dir) = &identity.git_dir {
            family_store::lookup_checkout_by_git_dir(client, &family, git_dir).await?
        } else {
            family_store::lookup_checkout(client, family.id, &identity.root)
                .await?
                .map(|resolved| resolved.checkout)
        };
        // Existing text is still reachable through its original literal key.
        // The primary checkout's historical key represents the shared notes.
        Ok(Self {
            path: selected.to_string_lossy().into_owned(),
            family_path: primary.to_string_lossy().into_owned(),
            family_id: Some(family.id),
            embedding_dim: Some(family.embedding_dim as usize),
            checkout_key: checkout.map(|checkout| checkout.token.id.as_bytes().to_vec()),
            legacy_keys: vec![
                path.into(),
                selected.to_string_lossy().into_owned(),
                primary.to_string_lossy().into_owned(),
            ],
        })
    }

    pub async fn resolve_for_checkout_note(client: &mut Client, path: &str) -> Result<Self> {
        let mut location = Self::resolve(client, path).await?;
        if location.checkout_key.is_none() {
            let family = location
                .family_id
                .context("checkout scope requires a registered family")?;
            let identity = crate::family_store::CheckoutIdentity::discover(Path::new(path)).await?;
            let checkout =
                crate::family_store::register_checkout(client, family, &identity).await?;
            location.checkout_key = Some(checkout.token.id.as_bytes().to_vec());
        }
        Ok(location)
    }
}

// $1 selects the family and $2 its optional checkout. Existing notes that
// predate explicit scope continue to be visible through their original keys.
const VISIBLE: &str = "((family_id = $1 AND (checkout_key IS NULL OR checkout_key = $2))
                         OR (family_id IS NULL AND repo_path = ANY($3)))";

// ─── Domain type ─────────────────────────────────────────────────────────────

#[derive(Debug, Clone)]
pub struct KnowledgeItem {
    pub id: Uuid,
    pub repo_path: String,
    pub title: String,
    pub body: String,
    pub tags: Vec<String>,
    pub related_files: Vec<String>,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

#[derive(Debug, Clone)]
pub struct KnowledgeResult {
    pub item: KnowledgeItem,
    pub score: f32,
}

// ─── Write ────────────────────────────────────────────────────────────────────

/// Insert or update a knowledge item for the given repo.
/// If `id` is Some, only that note within the same repository scope can be updated.
/// If `id` is None, always inserts.
/// `expected_dim` is the dimension of the active embedding backend; if `embedding` is
/// present its length must match to prevent dimension-mismatch errors at query time.
/// Returns the persisted item (with embedding cleared — caller must re-embed if needed).
// Cohesive set of knowledge-item fields; bundling them into a struct would just
// move the argument list elsewhere without improving clarity.
#[allow(clippy::too_many_arguments)]
pub async fn upsert(
    client: &Client,
    id: Option<Uuid>,
    repo_path: &str,
    title: &str,
    body: &str,
    tags: &[String],
    related_files: &[String],
    embedding: Option<&[f32]>,
    expected_dim: usize,
) -> Result<KnowledgeItem> {
    upsert_scoped(
        client,
        &NoteLocation::legacy(repo_path),
        false,
        id,
        title,
        body,
        tags,
        related_files,
        embedding,
        expected_dim,
    )
    .await
}

#[allow(clippy::too_many_arguments)]
pub async fn upsert_scoped(
    client: &impl GenericClient,
    location: &NoteLocation,
    checkout_only: bool,
    id: Option<Uuid>,
    title: &str,
    body: &str,
    tags: &[String],
    related_files: &[String],
    embedding: Option<&[f32]>,
    expected_dim: usize,
) -> Result<KnowledgeItem> {
    anyhow::ensure!(!title.is_empty(), "knowledge title must not be empty");
    anyhow::ensure!(!body.is_empty(), "knowledge body must not be empty");
    if let Some(emb) = embedding {
        anyhow::ensure!(
            emb.len() == expected_dim,
            "knowledge embedding dimension {} does not match configured backend dimension {}; \
             switching backends requires re-embedding all existing knowledge items",
            emb.len(),
            expected_dim
        );
        anyhow::ensure!(
            crate::embeddings::usable_vector(emb),
            "knowledge embedding must be finite and nonzero"
        );
    }

    let emb: Option<Vector> = embedding.map(|v| Vector::from(v.to_vec()));
    let dimension = i32::try_from(expected_dim)?;
    let columns = "id, repo_path, title, body, tags, related_files, created_at, updated_at";
    let row = if let Some(id) = id {
        client.query_opt(
            &format!("UPDATE knowledge SET title=$5, body=$6, tags=$7, related_files=$8, embedding=$9, updated_at=now()
                     WHERE id=$4 AND {VISIBLE} AND ($1::uuid IS NULL OR EXISTS (
                        SELECT FROM public.repos WHERE id=$1 AND embedding_dim=$10
                        AND retired_at IS NULL FOR KEY SHARE
                     )) RETURNING {columns}"),
            &[&location.family_id, &location.checkout_key, &location.legacy_keys, &id,
              &title, &body, &tags, &related_files, &emb, &dimension],
        ).await?.context("knowledge note does not exist in the specified repository scope")?
    } else {
        let checkout_key = if checkout_only {
            Some(
                location
                    .checkout_key
                    .as_ref()
                    .context("checkout-local notes require a registered checkout")?,
            )
        } else {
            None
        };
        let stored_path = if checkout_only {
            &location.path
        } else {
            &location.family_path
        };
        client.query_opt(
            &format!("INSERT INTO knowledge (repo_path, title, body, tags, related_files, embedding, family_id, checkout_key)
                      SELECT $1, $2, $3, $4, $5, $6, $7, $8
                      WHERE $7::uuid IS NULL OR EXISTS (
                        SELECT FROM public.repos WHERE id=$7 AND embedding_dim=$9
                        AND retired_at IS NULL FOR KEY SHARE
                      ) RETURNING {columns}"),
            &[stored_path, &title, &body, &tags, &related_files, &emb,
              &location.family_id, &checkout_key, &dimension],
        ).await?.context("knowledge note family is no longer registered")?
    };
    row_to_item(row)
}

/// Delete a knowledge item by id. Returns true if found and deleted.
pub async fn delete(client: &Client, id: Uuid) -> Result<bool> {
    let n = client
        .execute(
            "DELETE FROM knowledge WHERE id = $1 AND family_id IS NULL",
            &[&id],
        )
        .await?;
    Ok(n > 0)
}

pub async fn delete_scoped(
    client: &impl GenericClient,
    location: &NoteLocation,
    id: Uuid,
) -> Result<bool> {
    let n = client
        .execute(
            &format!("DELETE FROM knowledge WHERE id=$4 AND {VISIBLE}"),
            &[
                &location.family_id,
                &location.checkout_key,
                &location.legacy_keys,
                &id,
            ],
        )
        .await?;
    Ok(n > 0)
}

// ─── Read ─────────────────────────────────────────────────────────────────────

/// List all knowledge items for a repo, ordered by updated_at descending.
pub async fn list(client: &Client, repo_path: &str) -> Result<Vec<KnowledgeItem>> {
    list_scoped(client, &NoteLocation::legacy(repo_path)).await
}

pub async fn list_scoped(client: &Client, location: &NoteLocation) -> Result<Vec<KnowledgeItem>> {
    let rows = client
        .query(
            &format!(
                "
        SELECT id, repo_path, title, body, tags, related_files, created_at, updated_at
        FROM knowledge
        WHERE {VISIBLE}
        ORDER BY updated_at DESC, id
        "
            ),
            &[
                &location.family_id,
                &location.checkout_key,
                &location.legacy_keys,
            ],
        )
        .await?;

    rows.into_iter().map(row_to_item).collect()
}

// ─── Search ───────────────────────────────────────────────────────────────────

pub async fn search_fulltext(
    client: &Client,
    location: &NoteLocation,
    query: &str,
    limit: i64,
) -> Result<Vec<KnowledgeResult>> {
    let rows = client
        .query(
            &format!(
                "
        SELECT id, repo_path, title, body, tags, related_files, created_at, updated_at,
               ts_rank(ts_vector, plainto_tsquery('english', $4)) AS score
        FROM knowledge
        WHERE {VISIBLE}
          AND ts_vector @@ plainto_tsquery('english', $4)
        ORDER BY score DESC, id
        LIMIT $5
        "
            ),
            &[
                &location.family_id,
                &location.checkout_key,
                &location.legacy_keys,
                &query,
                &limit,
            ],
        )
        .await?;

    rows.into_iter()
        .map(|row| {
            let score: f32 = row.try_get("score")?;
            let item = row_to_item(row)?;
            Ok(KnowledgeResult { score, item })
        })
        .collect()
}

pub async fn has_vectors(
    client: &Client,
    location: &NoteLocation,
    dimension: usize,
) -> Result<bool> {
    let dimension = i32::try_from(dimension)?;
    let row = client
        .query_one(
            &format!(
                "SELECT EXISTS(SELECT FROM knowledge WHERE {VISIBLE}
            AND vector_dims(embedding)=$4 AND vector_norm(embedding)>0)"
            ),
            &[
                &location.family_id,
                &location.checkout_key,
                &location.legacy_keys,
                &dimension,
            ],
        )
        .await?;
    Ok(row.get(0))
}

async fn search_semantic(
    client: &Client,
    location: &NoteLocation,
    query_embedding: &[f32],
    limit: i64,
) -> Result<Vec<KnowledgeResult>> {
    let vec = Vector::from(query_embedding.to_vec());

    let rows = client
        .query(
            &format!(
                "
        SELECT id, repo_path, title, body, tags, related_files, created_at, updated_at,
               (1 - (embedding <=> $4))::float4 AS score
        FROM knowledge
        WHERE {VISIBLE}
          AND embedding IS NOT NULL
          AND vector_dims(embedding) = vector_dims($4)
          AND vector_norm(embedding)>0 AND (embedding <=> $4)<1
        ORDER BY embedding <=> $4, id
        LIMIT $5
        "
            ),
            &[
                &location.family_id,
                &location.checkout_key,
                &location.legacy_keys,
                &vec,
                &limit,
            ],
        )
        .await?;

    rows.into_iter()
        .map(|row| {
            let score: f32 = row.try_get("score")?;
            let item = row_to_item(row)?;
            Ok(KnowledgeResult { score, item })
        })
        .collect()
}

/// Hybrid search: RRF merge of semantic + fulltext results.
pub async fn search_hybrid(
    client: &Client,
    location: &NoteLocation,
    query: &str,
    query_embedding: &[f32],
    limit: i64,
) -> Result<Vec<KnowledgeResult>> {
    let sem = search_semantic(client, location, query_embedding, limit * 2).await?;
    let ft = search_fulltext(client, location, query, limit * 2).await?;

    let sem_sr: Vec<SearchResult> = sem.iter().map(knowledge_to_search_result).collect();
    let ft_sr: Vec<SearchResult> = ft.iter().map(knowledge_to_search_result).collect();

    let merged_sr = rrf_merge(sem_sr, ft_sr, limit as usize);

    let all_items: std::collections::HashMap<Uuid, &KnowledgeResult> = sem
        .iter()
        .chain(ft.iter())
        .map(|r| (r.item.id, r))
        .collect();

    Ok(merged_sr
        .into_iter()
        .filter_map(|sr| {
            all_items.get(&sr.chunk.id).map(|r| KnowledgeResult {
                item: r.item.clone(),
                score: sr.score,
            })
        })
        .collect())
}

// ─── Helpers ──────────────────────────────────────────────────────────────────

fn row_to_item(row: Row) -> Result<KnowledgeItem> {
    Ok(KnowledgeItem {
        id: row.try_get("id")?,
        repo_path: row.try_get("repo_path")?,
        title: row.try_get("title")?,
        body: row.try_get("body")?,
        tags: row.try_get("tags")?,
        related_files: row.try_get("related_files")?,
        created_at: row.try_get("created_at")?,
        updated_at: row.try_get("updated_at")?,
    })
}

/// Wrap a KnowledgeResult in a SearchResult so we can reuse rrf_merge.
/// Uses the knowledge item id as the chunk id (unique per item).
fn knowledge_to_search_result(r: &KnowledgeResult) -> SearchResult {
    SearchResult {
        score: r.score,
        chunk: Chunk {
            id: r.item.id,
            repo_id: Uuid::nil(),
            file_path: r.item.title.clone(),
            range: LineRange { start: 0, end: 0 },
            content: r.item.body.clone(),
            embedding: None,
            tier: Tier::Tier1,
            embedding_state: EmbeddingState::Embedded,
            content_hash: None,
        },
    }
}
