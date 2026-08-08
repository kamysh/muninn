use crate::{
    embeddings::EmbeddingBackend,
    graph,
    parser::{chunk_file, detect_language, extract_edges, parse_file},
    store::{delete_file_chunks, upsert_chunk},
    types::{content_sha256, BatchOutcome, EmbeddingState, StructuralEdge, Tier},
};
use anyhow::Result;
use std::path::Path;
use std::sync::Arc;
use tokio_postgres::Client;
use uuid::Uuid;

/// Files larger than this are skipped during indexing (see `index_file`).
const MAX_FILE_BYTES: u64 = 10 * 1024 * 1024; // 10 MiB

/// Files larger than this still get **text-indexed** (chunked + embedded) but
/// the symbol-extraction + structural-edge passes (`parse_file`,
/// `extract_edges`, the recursive walks in `parser.rs` like
/// `collect_callees_rec`) are skipped. Those passes are O(AST-node-count) and
/// bundled megafiles like TypeScript's `typescript.js` (~9 MB / 190 k lines)
/// blow that up to millions of nodes — minutes per file. Above this threshold
/// the file remains searchable via full-text + semantic vectors; only
/// structural search (callers / callees / imports / defines) is unavailable
/// for that file. See issue #6.
const MAX_PARSER_BYTES: u64 = 1024 * 1024; // 1 MiB

/// Per-file watchdog for `index_repo`'s inner loop. If a single file's full
/// pipeline (parse + edge extract + chunking + embed + DB writes) takes
/// longer than this, the file is skipped with a structured warning and a
/// `SkipRecord`. End-users can therefore never be silently hung by a single
/// file regardless of the failure mode (parser recursion, embedding stall,
/// network flake, etc.) — this is the file-level analogue of the per-cypher
/// `statement_timeout` in `graph.rs` (see issue #6 for the TypeScript .d.ts
/// parser-hang that motivated this). Spec: `Muninn.Storage` — IsolatedGraph
/// holds vacuously when a file is skipped (no chunks written → no symbols
/// referencing them either).
const FILE_INDEX_TIMEOUT_SECS: u64 = 120;

#[allow(clippy::too_many_arguments)]
pub async fn index_file(
    client: &Client,
    repo_id: Uuid,
    path: &Path,
    embedder: &dyn EmbeddingBackend,
    max_chars: usize,
    embed_batch_size: usize,
    expected_dim: usize,
    tier: Tier,
) -> Result<()> {
    let file_path = path.to_string_lossy().to_string();
    if let Ok(meta) = std::fs::metadata(path) {
        if meta.len() > MAX_FILE_BYTES {
            return Ok(());
        }
    }
    let bytes = std::fs::read(path)?;
    if bytes.contains(&0u8) {
        return Ok(());
    }
    let source = match String::from_utf8(bytes) {
        Ok(s) => s,
        Err(_) => return Ok(()),
    };

    let detected_language = detect_language(&file_path);
    let language = if detected_language.is_some() && (source.len() as u64) > MAX_PARSER_BYTES {
        tracing::info!(
            file = %file_path,
            size_bytes = source.len(),
            threshold_bytes = MAX_PARSER_BYTES,
            "file exceeds MAX_PARSER_BYTES — text-indexed only (no symbol graph)"
        );
        None
    } else {
        detected_language
    };
    let symbols = match &language {
        Some(lang) => parse_file(&source, *lang).unwrap_or_default(),
        None => vec![],
    };

    let mut chunks = chunk_file(&source, &symbols, max_chars);
    for c in &mut chunks {
        c.repo_id = repo_id;
        c.file_path = file_path.clone();
        // Tier and content_hash are set for every chunk at index time. The hash
        // lets the daemon dedup identical Tier-2 content during backfill.
        c.tier = tier;
        c.content_hash = Some(content_sha256(&c.content));
    }

    if chunks.is_empty() {
        return Ok(());
    }

    chunks.retain(|c| {
        if c.content.is_empty() {
            tracing::warn!("dropping empty-content chunk in {}", file_path);
            false
        } else {
            true
        }
    });
    if chunks.is_empty() {
        return Ok(());
    }

    match tier {
        // Tier 1 (first-party): embed eagerly. Spec: Muninn.Types.Tier1NeverPending.
        Tier::Tier1 => {
            let batch_size = if embed_batch_size == 0 {
                chunks.len().max(1)
            } else {
                embed_batch_size
            };
            for chunk_batch in chunks.chunks_mut(batch_size) {
                let texts: Vec<String> = chunk_batch.iter().map(|c| c.content.clone()).collect();
                let embeddings = embedder.embed(&texts).await?;
                for (c, emb) in chunk_batch.iter_mut().zip(embeddings) {
                    if emb.is_empty() {
                        tracing::warn!(
                            "embedder returned empty vector for chunk in {}; storing without embedding",
                            file_path
                        );
                        c.embedding_state = EmbeddingState::Absent;
                    } else if emb.len() != expected_dim {
                        return Err(anyhow::anyhow!(
                            "ValidStoredEmbedding violation: embedding dimension {} != expected {} \
                             for chunk in {}; switching backends requires unregister + re-index",
                            emb.len(),
                            expected_dim,
                            file_path
                        ));
                    } else {
                        c.embedding = Some(emb);
                        c.embedding_state = EmbeddingState::Embedded;
                    }
                }
            }
        }
        // Tier 2 (vendored): full-text indexed now, embedded lazily by the daemon.
        // Leave embedding = None and mark Pending; the backfill task fills it in.
        Tier::Tier2 => {
            for c in &mut chunks {
                c.embedding = None;
                c.embedding_state = EmbeddingState::Pending;
            }
        }
    }

    delete_file_chunks(client, repo_id, &file_path).await?;
    if let Err(e) = graph::delete_file_symbols(client, repo_id, &file_path).await {
        tracing::warn!("failed to clear old graph nodes for {}: {}", file_path, e);
    }
    for chunk in &chunks {
        upsert_chunk(client, chunk).await?;
    }

    let mut range_to_chunk: std::collections::HashMap<(u32, u32), uuid::Uuid> =
        std::collections::HashMap::new();
    let mut name_to_chunk: std::collections::HashMap<String, uuid::Uuid> =
        std::collections::HashMap::new();

    let mut node_inputs: Vec<graph::SymbolNodeInput> = Vec::new();
    for chunk in &chunks {
        if let Some(sym) = symbols.iter().find(|s| s.range.start == chunk.range.start) {
            node_inputs.push(graph::SymbolNodeInput {
                chunk_id: chunk.id,
                name: sym.name.clone(),
                kind: sym.kind.clone(),
                file_path: file_path.clone(),
                start_line: sym.range.start,
                end_line: sym.range.end,
            });
            range_to_chunk.insert((sym.range.start, sym.range.end), chunk.id);
            name_to_chunk.entry(sym.name.clone()).or_insert(chunk.id);
        }
    }
    if let Err(e) = graph::upsert_symbol_nodes(client, repo_id, &node_inputs).await {
        tracing::warn!(
            "failed to store {} symbol node(s) for {}: {}",
            node_inputs.len(),
            file_path,
            e
        );
    }

    if let Some(lang) = language {
        let known: std::collections::HashSet<String> =
            symbols.iter().map(|s| s.name.clone()).collect();
        let parsed_edges = extract_edges(&symbols, &source, &lang, &known);
        let mut edges: Vec<StructuralEdge> = Vec::new();
        for pe in parsed_edges {
            let from_id = range_to_chunk.get(&(pe.from_range.start, pe.from_range.end));
            let to_id = name_to_chunk.get(&pe.to_name);
            if let (Some(&from), Some(&to)) = (from_id, to_id) {
                edges.push(StructuralEdge {
                    from,
                    to,
                    relation: pe.relation,
                });
            }
        }
        if let Err(e) = graph::upsert_edges(client, repo_id, &edges).await {
            tracing::warn!(
                "failed to store {} edge(s) for {}: {}",
                edges.len(),
                file_path,
                e
            );
        }
    }

    Ok(())
}

/// One file's worth of work for `backfill_structural_edges`, factored out so
/// it can be wrapped in the same per-file timeout `index_repo`'s main loop
/// uses — without it, a single pathological file (dense minified/generated
/// source; see issue #6) can silently stall the whole backfill pass with no
/// per-file protection, unlike every other parse site in the pipeline.
async fn backfill_one_file(
    client: &Client,
    repo_id: Uuid,
    file: &std::path::Path,
    known_ids: &std::collections::HashMap<String, Uuid>,
    known_names: &std::collections::HashSet<String>,
) -> Result<()> {
    let file_path = file.to_string_lossy().to_string();
    let Some(lang) = detect_language(&file_path) else {
        return Ok(());
    };
    let Ok(bytes) = std::fs::read(file) else {
        return Ok(());
    };
    if bytes.len() as u64 > MAX_PARSER_BYTES || bytes.contains(&0u8) {
        return Ok(());
    }
    let Ok(source) = String::from_utf8(bytes) else {
        return Ok(());
    };
    let symbols = parse_file(&source, lang).unwrap_or_default();
    if symbols.is_empty() {
        return Ok(());
    }

    // Resolve the caller (`from`) side against this file's own nodes only —
    // the repo-wide `known_ids` map is ambiguous whenever two files define a
    // same-named symbol (e.g. every crate's own `main`), and the caller is
    // always defined in this file.
    let local_ids = graph::symbol_chunk_ids_for_file(client, repo_id, &file_path).await?;
    let range_to_name: std::collections::HashMap<(u32, u32), &str> = symbols
        .iter()
        .map(|s| ((s.range.start, s.range.end), s.name.as_str()))
        .collect();

    let parsed_edges = extract_edges(&symbols, &source, &lang, known_names);
    let mut edges: Vec<StructuralEdge> = Vec::new();
    for pe in parsed_edges {
        let from_id = range_to_name
            .get(&(pe.from_range.start, pe.from_range.end))
            .and_then(|n| local_ids.get(*n));
        let to_id = known_ids.get(&pe.to_name);
        if let (Some(&from), Some(&to)) = (from_id, to_id) {
            edges.push(StructuralEdge {
                from,
                to,
                relation: pe.relation,
            });
        }
    }
    if !edges.is_empty() {
        graph::upsert_edges(client, repo_id, &edges).await?;
    }
    Ok(())
}

/// Second pass over `files`, run once per `index_repo` call after every file
/// has had its own chunks and symbol nodes written. `index_file`'s immediate
/// pass can only resolve CALLS edges within the same file — its `known` set
/// is that file's own symbols, so a function in file A calling one in file B
/// is invisible to A's pass, regardless of walk order. This pass re-parses
/// each file with the now-complete repo-wide name -> chunk_id table as
/// `known`, so cross-file calls resolve, and writes any newly-found edges via
/// the same idempotent MERGE `upsert_edges` already uses.
///
/// Read-only w.r.t. chunks: never re-chunks, re-embeds, or rewrites symbol
/// nodes, only adds edges. Only called from `index_repo` (bulk add/reindex);
/// the daemon's incremental single-file watcher path does not call this — a
/// newly-added cross-file call is only picked up by the next full reindex.
///
/// `on_progress` is called after each file, same `(files_done, total_files,
/// path)` shape as `index_repo`'s — this pass does one extra DB round-trip
/// per source file on top of a full re-parse, so on a large repo it can run
/// long after the main loop's progress bar reaches 100%; without its own
/// progress output that looks indistinguishable from a hang.
async fn backfill_structural_edges(
    client: &Client,
    repo_id: Uuid,
    files: &[std::path::PathBuf],
    on_progress: &impl Fn(usize, usize, &Path),
) -> Result<()> {
    let known_ids = graph::all_symbol_chunk_ids(client, repo_id).await?;
    if known_ids.is_empty() {
        return Ok(());
    }
    let known_names: std::collections::HashSet<String> = known_ids.keys().cloned().collect();

    let total = files.len();
    for (i, file) in files.iter().enumerate() {
        let work = backfill_one_file(client, repo_id, file, &known_ids, &known_names);
        match tokio::time::timeout(
            std::time::Duration::from_secs(FILE_INDEX_TIMEOUT_SECS),
            work,
        )
        .await
        {
            Ok(Ok(())) => {}
            Ok(Err(e)) => {
                tracing::warn!("structural backfill failed for {}: {}", file.display(), e)
            }
            Err(_elapsed) => {
                tracing::warn!(
                    file = %file.display(),
                    timeout_secs = FILE_INDEX_TIMEOUT_SECS,
                    "structural backfill timed out for file — skipping"
                );
            }
        }
        on_progress(i + 1, total, file);
    }
    Ok(())
}

/// A file that failed to index, along with the reason. The reason string is
/// the full anyhow-style cause chain rendered once at skip-time so the CLI
/// can print it later without holding the underlying error.
#[derive(Debug, Clone)]
pub struct SkipRecord {
    pub path: std::path::PathBuf,
    pub reason: String,
}

/// Build an `ignore::overrides::Override` from a layered glob list (relative to
/// `repo_path`). A bare pattern `p` adds `p` to the set (an `ignore`-crate
/// negated glob `!p`, which `path_excluded` reads as "in the set"); a
/// `!p`-prefixed pattern REMOVES a prior match (an `ignore`-crate whitelist glob
/// `p`). Patterns are applied in order, last match wins — so a later `!p` can
/// un-set an earlier `p`. With only these entries the `ignore` crate matches
/// everything by default and only the resolved set is "ignored". Shared by the
/// full-repo walk and the file watcher so both apply identical rules.
pub fn build_excludes(repo_path: &Path, exclude: &[String]) -> ignore::overrides::Override {
    use ignore::overrides::OverrideBuilder;
    let mut builder = OverrideBuilder::new(repo_path);
    for pat in exclude {
        let pat = pat.trim();
        if pat.is_empty() {
            continue;
        }
        // A user `!p` (negation) becomes an ignore-crate WHITELIST glob `p`,
        // which last-match-wins un-sets a prior membership. A bare `p` becomes
        // the ignore-crate negated glob `!p` (membership).
        let entry = match pat.strip_prefix('!') {
            Some(rest) => rest.to_string(),
            None => format!("!{pat}"),
        };
        if let Err(e) = builder.add(&entry) {
            tracing::warn!("ignoring invalid exclude glob {:?}: {}", pat, e);
        }
    }
    builder.build().unwrap_or_else(|e| {
        tracing::warn!(
            "failed to build exclude globset for {}: {}",
            repo_path.display(),
            e
        );
        ignore::overrides::Override::empty()
    })
}

/// Whether `rel` (a path relative to the repo root) is excluded by `overrides`.
///
/// The full-repo walk relies on `WalkBuilder` to prune excluded directories as
/// it descends, so a single `Override::matched` per entry suffices there. The
/// file watcher, however, receives deep paths with no traversal context — and
/// `Override::matched` (unlike `Gitignore::matched_path_or_any_parents`) tests
/// only the exact path, not its ancestors. So a change to `target/debug/x.rs`
/// under a `target/` exclude would slip through. This walks the path's
/// ancestors so a directory exclude correctly covers everything beneath it.
pub fn path_excluded(overrides: &ignore::overrides::Override, rel: &Path) -> bool {
    if overrides.is_empty() {
        return false;
    }
    if overrides.matched(rel, false).is_ignore() {
        return true;
    }
    rel.ancestors()
        .skip(1)
        .take_while(|a| !a.as_os_str().is_empty())
        .any(|ancestor| overrides.matched(ancestor, true).is_ignore())
}

/// The classification of a repo-relative path. Spec: Muninn.Config.Decision.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Decision {
    /// Matched `exclude` — never indexed.
    Drop,
    /// First-party source: full weight, eager embed.
    Tier1,
    /// Matched `vendor` — indexed but down-weighted and lazily embedded.
    Tier2,
}

/// Classify a repo-relative path against the two glob axes. `exclude` drops first
/// and wins on overlap; `vendor` then classifies survivors as Tier 2; everything
/// else is Tier 1. Both axes use the same last-match-wins / `!`-negation matcher
/// as `build_excludes`. Spec: Muninn.Config.classify.
pub fn classify(repo_root: &Path, exclude: &[String], vendor: &[String], rel: &Path) -> Decision {
    if path_excluded(&build_excludes(repo_root, exclude), rel) {
        return Decision::Drop;
    }
    if path_excluded(&build_excludes(repo_root, vendor), rel) {
        return Decision::Tier2;
    }
    Decision::Tier1
}

/// Index all files in a repo.
///
/// Returns the overall `BatchOutcome` plus a list of files that were skipped
/// (with reasons). The CLI prints this list after its progress bar finishes,
/// since the progress bar's `\r`-redraw would otherwise overwrite any
/// in-flight `tracing::warn!` output. The daemon ignores the list (it relies
/// on the tracing warning that also fires).
///
/// `on_progress` is called after each file with `(files_done, total_files, path)`.
/// Pass `|_, _, _| {}` for no-op (daemon background use).
// Client, ids, embedder, config knobs and a progress callback — all distinct
// concerns; a param struct would obscure more than it clarifies.
#[allow(clippy::too_many_arguments)]
pub async fn index_repo(
    client: &Client,
    repo_id: Uuid,
    repo_path: &Path,
    embedder: Arc<dyn EmbeddingBackend>,
    embed_batch_size: usize,
    expected_dim: usize,
    exclude: &[String],
    vendor: &[String],
    on_progress: impl Fn(usize, usize, &Path),
) -> Result<(BatchOutcome, Vec<SkipRecord>)> {
    use ignore::WalkBuilder;

    let overrides = build_excludes(repo_path, exclude);
    let walker = WalkBuilder::new(repo_path)
        .standard_filters(false)
        .overrides(overrides)
        .filter_entry(|e| e.file_name() != ".git")
        .build();

    // The walker prunes `exclude` (Drop) during traversal; survivors are then
    // classified Tier 1 vs Tier 2 by the vendor override (hoisted once here).
    let vendor_overrides = build_excludes(repo_path, vendor);

    let mut files: Vec<std::path::PathBuf> = vec![];
    for entry in walker.flatten() {
        if entry.file_type().map(|t| t.is_file()).unwrap_or(false) {
            files.push(entry.path().to_owned());
        }
    }

    let keep: Vec<String> = files
        .iter()
        .map(|p| p.to_string_lossy().to_string())
        .collect();

    let total = files.len();
    let mut done = 0usize;
    let mut any_succeeded = false;
    let mut skips: Vec<SkipRecord> = Vec::new();

    for file in &files {
        // Survivors of the exclude-pruned walk: Tier 2 if the vendor override
        // matches, else Tier 1. Spec: Muninn.Config.classify.
        let rel = file.strip_prefix(repo_path).unwrap_or(file);
        let tier = if path_excluded(&vendor_overrides, rel) {
            Tier::Tier2
        } else {
            Tier::Tier1
        };
        let work = index_file(
            client,
            repo_id,
            file,
            embedder.as_ref(),
            1500,
            embed_batch_size,
            expected_dim,
            tier,
        );
        match tokio::time::timeout(
            std::time::Duration::from_secs(FILE_INDEX_TIMEOUT_SECS),
            work,
        )
        .await
        {
            Ok(Ok(())) => any_succeeded = true,
            Ok(Err(e)) => {
                let reason = format!("{:#}", e);
                tracing::warn!("skipping {}: {}", file.display(), reason);
                skips.push(SkipRecord {
                    path: file.clone(),
                    reason,
                });
            }
            Err(_elapsed) => {
                let reason = format!(
                    "file index timed out after {FILE_INDEX_TIMEOUT_SECS}s — likely \
                     pathological parser recursion (see issue #6). Skipped; chunks \
                     and symbols for this file are absent."
                );
                tracing::warn!(
                    file = %file.display(),
                    timeout_secs = FILE_INDEX_TIMEOUT_SECS,
                    "file index timed out — skipping"
                );
                skips.push(SkipRecord {
                    path: file.clone(),
                    reason,
                });
            }
        }
        done += 1;
        on_progress(done, total, file);
    }

    let any_failed = !skips.is_empty();
    if any_succeeded || files.is_empty() {
        match crate::store::file_paths_not_in(client, repo_id, &keep).await {
            Ok(orphans) => {
                for path in &orphans {
                    if let Err(e) = crate::graph::delete_file_symbols(client, repo_id, path).await {
                        tracing::warn!("graph prune failed for {}: {}", path, e);
                    }
                }
            }
            Err(e) => tracing::warn!("listing orphan files failed for repo {}: {}", repo_id, e),
        }
        match crate::store::prune_chunks_not_in(client, repo_id, &keep).await {
            Ok(n) if n > 0 => {
                tracing::info!("reindex pruned {} orphaned chunk(s) in repo {}", n, repo_id)
            }
            Ok(_) => {}
            Err(e) => tracing::warn!("orphan prune failed for repo {}: {}", repo_id, e),
        }
        if any_succeeded {
            if let Err(e) = backfill_structural_edges(client, repo_id, &files, &on_progress).await {
                tracing::warn!(
                    "cross-file structural edge backfill failed for repo {}: {}",
                    repo_id,
                    e
                );
            }
        }
        crate::store::mark_indexed(client, repo_id).await?;
        let outcome = if any_failed {
            BatchOutcome::SomeSucceeded
        } else {
            BatchOutcome::AllSucceeded
        };
        Ok((outcome, skips))
    } else {
        tracing::error!(
            "repo {}: all {} files failed to index — not marking as indexed",
            repo_id,
            files.len()
        );
        Err(anyhow::anyhow!(
            "BatchOutcome: no files were successfully indexed in repo {}",
            repo_id
        ))
    }
}

/// Max distinct contents embedded per backfill pass — bounds one daemon tick.
const BACKFILL_BATCH: i64 = 128;

/// Drain one batch of the repo's Tier-2 embedding backlog: embed each UNIQUE
/// pending content once (deduped by content_hash) and fan the vector out to all
/// pending chunks sharing that hash. Returns the number of chunk rows updated.
/// The daemon calls this repeatedly until it returns 0. Spec: Muninn.IndexFsm
/// .EmbedStep (Pending → Embedded; only ever advances pending chunks).
pub async fn backfill_once(
    client: &Client,
    repo_id: Uuid,
    embedder: &dyn EmbeddingBackend,
    expected_dim: usize,
) -> Result<usize> {
    let groups = crate::store::pending_content_groups(client, repo_id, BACKFILL_BATCH).await?;
    if groups.is_empty() {
        return Ok(0);
    }
    let texts: Vec<String> = groups.iter().map(|(_, c)| c.clone()).collect();
    let embeddings = embedder.embed(&texts).await?;
    let mut updated = 0usize;
    for ((hash, _), emb) in groups.iter().zip(embeddings) {
        if emb.is_empty() {
            tracing::warn!(
                "backfill: embedder returned empty vector for a Tier-2 content in repo {}; \
                 leaving those chunks pending",
                repo_id
            );
            continue;
        }
        if emb.len() != expected_dim {
            // Dim mismatch is a hard misconfiguration; skip rather than corrupt
            // the VECTOR(n) column. Spec: ValidStoredEmbedding.
            tracing::error!(
                "backfill: embedding dim {} != expected {} in repo {}; skipping",
                emb.len(),
                expected_dim,
                repo_id
            );
            continue;
        }
        updated +=
            crate::store::set_embedding_for_hash(client, repo_id, hash, &emb).await? as usize;
    }
    Ok(updated)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ov(globs: &[&str]) -> ignore::overrides::Override {
        let v: Vec<String> = globs.iter().map(|s| s.to_string()).collect();
        build_excludes(Path::new("/repo"), &v)
    }

    fn cls(exclude: &[&str], vendor: &[&str], rel: &str) -> Decision {
        let ex: Vec<String> = exclude.iter().map(|s| s.to_string()).collect();
        let vn: Vec<String> = vendor.iter().map(|s| s.to_string()).collect();
        classify(Path::new("/repo"), &ex, &vn, Path::new(rel))
    }

    #[test]
    fn classify_exclude_wins_over_vendor() {
        // A path matching both axes is dropped (exclude wins).
        assert_eq!(cls(&["**/x/**"], &["**/x/**"], "x/a.js"), Decision::Drop);
    }

    #[test]
    fn classify_vendor_then_tier1() {
        assert_eq!(
            cls(&[], &["**/node_modules/**"], "node_modules/p/i.js"),
            Decision::Tier2
        );
        assert_eq!(
            cls(&[], &["**/node_modules/**"], "src/main.rs"),
            Decision::Tier1
        );
    }

    #[test]
    fn classify_negation_reclaims_tier1() {
        // vendor matches target/, but a repo `!` negation un-sets it → Tier 1.
        assert_eq!(
            cls(&[], &["**/target/**", "!**/target/**"], "target/x.rs"),
            Decision::Tier1
        );
    }

    #[test]
    fn classify_unmatched_is_tier1() {
        assert_eq!(cls(&[], &[], "src/lib.rs"), Decision::Tier1);
    }

    #[test]
    fn empty_excludes_index_everything() {
        let o = ov(&[]);
        assert!(!path_excluded(&o, Path::new("src/main.rs")));
        assert!(!path_excluded(&o, Path::new("node_modules/pkg/index.js")));
    }

    #[test]
    fn dir_exclude_covers_descendants() {
        let o = ov(&["target/"]);
        assert!(path_excluded(&o, Path::new("target/debug/build/x.rs")));
        assert!(path_excluded(&o, Path::new("target/foo")));
        assert!(!path_excluded(&o, Path::new("src/lib.rs")));
        assert!(!path_excluded(
            &o,
            Path::new("node_modules/left-pad/index.js")
        ));
    }

    #[test]
    fn glob_exclude_matches_files() {
        let o = ov(&["**/*.min.js"]);
        assert!(path_excluded(&o, Path::new("web/static/app.min.js")));
        assert!(!path_excluded(&o, Path::new("web/static/app.js")));
    }

    #[test]
    fn multiple_patterns_combine() {
        let o = ov(&["target/", "dist/", "**/*.lock"]);
        assert!(path_excluded(&o, Path::new("target/x")));
        assert!(path_excluded(&o, Path::new("dist/bundle.js")));
        assert!(path_excluded(&o, Path::new("a/b/Cargo.lock")));
        assert!(!path_excluded(&o, Path::new("src/main.rs")));
    }

    #[test]
    fn blank_patterns_ignored() {
        let o = ov(&["", "   "]);
        assert!(!path_excluded(&o, Path::new("anything.rs")));
    }
}
