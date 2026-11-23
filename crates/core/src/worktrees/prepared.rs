use super::{schema, SourceFile, Target};
use crate::{
    pipeline,
    types::{Chunk, EmbeddingState},
};
use anyhow::{Context, Result};
use pgvector::Vector;
use std::{
    collections::{BTreeMap, HashMap},
    path::Path,
};
use tokio_postgres::{Client, Transaction};
use uuid::Uuid;

type Candidates = HashMap<(String, Vec<u8>, i16), Vec<(Uuid, String)>>;
const FILES_PER_COMMIT: usize = 32;

pub(super) async fn prepare(
    client: &mut Client,
    target: &Target,
    files: &[SourceFile],
    previous: &BTreeMap<String, Uuid>,
    progress: &impl Fn(usize, usize, &Path),
) -> Result<BTreeMap<String, Uuid>> {
    let s = schema(target.family);
    let paths: Vec<_> = files
        .iter()
        .filter(|file| file.source.is_some())
        .map(|file| &file.path)
        .collect();
    let tx = client.transaction().await?;
    let mut candidates = Candidates::new();
    for row in tx.query(
        &format!("SELECT v.id,v.path,v.content_hash,v.tier,c.source FROM {s}.file_versions v
          JOIN {s}.file_content_cache c ON c.file_version=v.id WHERE v.path=ANY($1) FOR KEY SHARE OF v"),
        &[&paths],
    ).await? {
        candidates.entry((row.get(1), row.get(2), row.get(3)))
            .or_default().push((row.get(0), row.get(4)));
    }
    let mut desired = BTreeMap::new();
    for file in files {
        let reuse = match &file.source {
            None => Some(
                *previous
                    .get(&file.path)
                    .context("missing inherited version")?,
            ),
            Some(source) => candidates
                .get(&(file.path.clone(), file.hash.clone(), file.tier.as_i16()))
                .and_then(|matches| matches.iter().find(|(_, saved)| saved == source))
                .map(|(version, _)| *version),
        };
        if let Some(version) = reuse {
            desired.insert(file.path.clone(), version);
        }
    }
    let (new_paths, new_versions): (Vec<&String>, Vec<&Uuid>) = desired
        .iter()
        .filter(|(path, version)| previous.get(*path) != Some(*version))
        .unzip();
    if !new_paths.is_empty() {
        tx.execute(
            &format!(
                "INSERT INTO {s}.checkout_prepared_files(checkout,path,version)
              SELECT $1,path,version FROM unnest($2::text[],$3::uuid[]) AS p(path,version)
              ON CONFLICT DO NOTHING"
            ),
            &[&target.checkout, &new_paths, &new_versions],
        )
        .await?;
    }
    tx.commit().await?;
    let mut processed = 0;
    for batch in files.chunks(FILES_PER_COMMIT) {
        let missing: Vec<_> = batch
            .iter()
            .filter(|file| !desired.contains_key(&file.path))
            .collect();
        if !missing.is_empty() {
            let mut inputs = Vec::with_capacity(missing.len());
            for file in missing {
                let source = file.source.as_deref().context("missing file input")?;
                let (chunks, _) = pipeline::prepare_text_chunks(
                    target.family,
                    &file.path,
                    source,
                    1500,
                    file.tier,
                );
                inputs.push((file, chunks));
            }
            let tx = client.transaction().await?;
            lock_versions(&tx, target, &inputs).await?;
            for (file, chunks) in inputs {
                let version = prepare_file(&tx, target, &s, file, &chunks).await?;
                desired.insert(file.path.clone(), version);
            }
            tx.commit().await?;
        }
        for file in batch {
            processed += 1;
            progress(processed, files.len(), &target.root.join(&file.path));
        }
    }
    Ok(desired)
}

async fn lock_versions(
    tx: &Transaction<'_>,
    target: &Target,
    inputs: &[(&SourceFile, Vec<Chunk>)],
) -> Result<()> {
    let paths: Vec<_> = inputs.iter().map(|(file, _)| &file.path).collect();
    let hashes: Vec<_> = inputs.iter().map(|(file, _)| &file.hash).collect();
    let tiers: Vec<_> = inputs.iter().map(|(file, _)| file.tier.as_i16()).collect();
    // Order the actual advisory keys so overlapping batches cannot deadlock.
    // A matching digest only acquires a lock. Exact source still decides reuse.
    tx.query(
        "SELECT pg_advisory_xact_lock(key) FROM (
            SELECT DISTINCT hashtextextended($1 || path || encode(hash,'hex') || tier::text, 802392) key
            FROM unnest($2::text[],$3::bytea[],$4::smallint[]) AS v(path,hash,tier)
         ) keys ORDER BY key",
        &[&target.family.to_string(), &paths, &hashes, &tiers],
    ).await?;
    Ok(())
}

async fn prepare_file(
    tx: &Transaction<'_>,
    target: &Target,
    s: &str,
    file: &SourceFile,
    chunks: &[Chunk],
) -> Result<Uuid> {
    let source = file.source.as_deref().context("missing file input")?;
    let saved = tx.query_opt(
        &format!("SELECT v.id FROM {s}.file_versions v JOIN {s}.file_content_cache c ON c.file_version=v.id
          WHERE v.path=$1 AND v.content_hash=$2 AND v.tier=$3 AND c.source=$4 ORDER BY v.id LIMIT 1 FOR KEY SHARE OF v"),
        &[&file.path, &file.hash, &file.tier.as_i16(), &source],
    ).await?;
    let version = if let Some(saved) = saved {
        saved.get(0)
    } else {
        let paths = [
            &file.path,
            &target.root.join(&file.path).to_string_lossy().into_owned(),
        ];
        let vectors: HashMap<String, Vector> = tx.query(
            &format!("SELECT content,embedding FROM {s}.chunks WHERE file_path=ANY($1) AND embedding IS NOT NULL"),
            &[&&paths[..]],
        ).await?.into_iter().map(|row| (row.get(0), row.get(1))).collect();
        let version = Uuid::new_v4();
        tx.execute(
            &format!(
                "INSERT INTO {s}.file_versions(id,path,content_hash,tier) VALUES($1,$2,$3,$4)"
            ),
            &[&version, &file.path, &file.hash, &file.tier.as_i16()],
        )
        .await?;
        tx.execute(
            &format!("INSERT INTO {s}.file_content_cache(file_version,source) VALUES($1,$2)"),
            &[&version, &source],
        )
        .await?;
        let ids: Vec<_> = chunks.iter().map(|chunk| chunk.id).collect();
        let starts: Vec<_> = chunks
            .iter()
            .map(|chunk| chunk.range.start as i32)
            .collect();
        let ends: Vec<_> = chunks.iter().map(|chunk| chunk.range.end as i32).collect();
        let contents: Vec<_> = chunks.iter().map(|chunk| chunk.content.as_str()).collect();
        let embeddings: Vec<_> = contents.iter().map(|text| vectors.get(*text)).collect();
        let hashes: Vec<_> = chunks
            .iter()
            .map(|chunk| chunk.content_hash.as_deref())
            .collect();
        tx.execute(
            &format!("INSERT INTO {s}.chunks
              (id,repo_id,file_path,start_line,end_line,content,embedding,tier,embedding_state,content_hash,file_version,in_base)
              SELECT id,$1,$2,start_line,end_line,content,embedding,$3,
                  CASE WHEN embedding IS NULL THEN $4::text ELSE $5::text END,hash,$6,false
              FROM unnest($7::uuid[],$8::int[],$9::int[],$10::text[],$11::public.vector[],$12::bytea[])
                  AS c(id,start_line,end_line,content,embedding,hash)"),
            &[
                &target.family, &file.path, &file.tier.as_i16(),
                &EmbeddingState::Pending.as_str(), &EmbeddingState::Embedded.as_str(), &version,
                &ids, &starts, &ends, &contents, &embeddings, &hashes,
            ],
        ).await?;
        version
    };
    pin(tx, s, target, file, version).await?;
    Ok(version)
}

async fn pin(
    tx: &Transaction<'_>,
    s: &str,
    target: &Target,
    file: &SourceFile,
    version: Uuid,
) -> Result<()> {
    tx.execute(
        &format!(
            "INSERT INTO {s}.checkout_prepared_files(checkout,path,version) VALUES($1,$2,$3)
          ON CONFLICT DO NOTHING"
        ),
        &[&target.checkout, &file.path, &version],
    )
    .await?;
    Ok(())
}
