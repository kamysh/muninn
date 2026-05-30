use crate::{
    embeddings::EmbeddingBackend,
    graph,
    parser::{detect_language, extract_edges, parse_file, chunk_file},
    store::{upsert_chunk, delete_file_chunks},
    types::{BatchOutcome, StructuralEdge},
};
use sqlx::PgPool;
use uuid::Uuid;
use anyhow::Result;
use std::sync::Arc;
use std::path::Path;

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
const MAX_PARSER_BYTES: u64 = 1 * 1024 * 1024; // 1 MiB

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

pub async fn index_file(
    pool: &PgPool,
    repo_id: Uuid,
    path: &Path,
    embedder: &dyn EmbeddingBackend,
    max_chars: usize,
    embed_batch_size: usize,
    expected_dim: usize,
) -> Result<()> {
    let file_path = path.to_string_lossy().to_string();
    // Skip files larger than the cap before reading them into memory. Huge text
    // files (generated bundles, data dumps, vendored blobs) would otherwise
    // explode into thousands of low-value chunks and dominate the index.
    if let Ok(meta) = std::fs::metadata(path) {
        if meta.len() > MAX_FILE_BYTES {
            return Ok(());
        }
    }
    let bytes = std::fs::read(path)?;
    // Skip binary files (null byte is a reliable binary indicator)
    if bytes.contains(&0u8) {
        return Ok(());
    }
    let source = match String::from_utf8(bytes) {
        Ok(s) => s,
        Err(_) => return Ok(()), // Non-UTF-8 encoding — skip silently
    };

    let detected_language = detect_language(&file_path);
    // Gate the symbol-graph path on file size: above MAX_PARSER_BYTES we force
    // language to None so `parse_file`, `extract_edges`, and the symbol-graph
    // writes are all skipped — the file is still chunked + embedded + stored
    // for full-text / semantic search. Avoids the parser-recursion cost on
    // bundled megafiles (issue #6) up front, instead of relying on the per-
    // file timeout as a safety net.
    let language = if detected_language.is_some()
        && (source.len() as u64) > MAX_PARSER_BYTES
    {
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
    }

    if chunks.is_empty() {
        return Ok(());
    }

    // ValidChunk invariant: no chunk may have empty content.
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

    // Generate embeddings in batches (batch_size = texts per request)
    let batch_size = if embed_batch_size == 0 {
        chunks.len().max(1)
    } else {
        embed_batch_size
    };
    for chunk_batch in chunks.chunks_mut(batch_size) {
        let texts: Vec<String> = chunk_batch.iter().map(|c| c.content.clone()).collect();
        let embeddings = embedder.embed(&texts).await?;
        for (c, emb) in chunk_batch.iter_mut().zip(embeddings) {
            // ValidStoredEmbedding invariant: length must equal repo's registered
            // dimension. Reject length-0 (empty) and dimension-mismatch embeddings —
            // storing either causes silent vector-distance failures at query time.
            if emb.is_empty() {
                tracing::warn!(
                    "embedder returned empty vector for chunk in {}; storing without embedding",
                    file_path
                );
                // c.embedding stays None
            } else if emb.len() != expected_dim {
                return Err(anyhow::anyhow!(
                    "ValidStoredEmbedding violation: embedding dimension {} != expected {} \
                     for chunk in {}; switching backends requires unregister + re-index",
                    emb.len(), expected_dim, file_path
                ));
            } else {
                c.embedding = Some(emb);
            }
        }
    }

    delete_file_chunks(pool, repo_id, &file_path).await?;
    // Clear this file's old symbol nodes too: chunk_ids are regenerated on each
    // index, so MERGE-by-chunk_id below would leave the previous nodes dangling.
    // Best-effort, matching the graph-write calls further down.
    if let Err(e) = graph::delete_file_symbols(pool, repo_id, &file_path).await {
        tracing::warn!("failed to clear old graph nodes for {}: {}", file_path, e);
    }
    for chunk in &chunks {
        upsert_chunk(pool, chunk).await?;
    }

    // Persist parsed symbols into the per-repo AGE graph (IsolatedGraph invariant:
    // chunks are persisted above before symbols reference them).
    // Also build a range→chunk_id and name→chunk_id map for edge resolution.
    let mut range_to_chunk: std::collections::HashMap<(u32, u32), uuid::Uuid> =
        std::collections::HashMap::new();
    let mut name_to_chunk: std::collections::HashMap<String, uuid::Uuid> =
        std::collections::HashMap::new();

    let mut node_inputs: Vec<graph::SymbolNodeInput> = Vec::new();
    for chunk in &chunks {
        // chunk_file may split an oversized symbol body into multiple
        // sub-chunks; only the FIRST sub-chunk inherits the symbol's start
        // line, so match by start (not strict range equality).
        if let Some(sym) = symbols.iter().find(|s| s.range.start == chunk.range.start) {
            node_inputs.push(graph::SymbolNodeInput {
                chunk_id: chunk.id,
                name: sym.name.clone(),
                kind: sym.kind.clone(),
                file_path: file_path.clone(),
                start_line: sym.range.start,
                end_line: sym.range.end,
            });
            // Key by the symbol's full range, not the (possibly truncated)
            // first sub-chunk's range — edge resolution looks up by symbol
            // range and would otherwise miss split symbols.
            range_to_chunk.insert((sym.range.start, sym.range.end), chunk.id);
            // first occurrence wins for name lookup
            name_to_chunk.entry(sym.name.clone()).or_insert(chunk.id);
        }
    }
    // One batched write (≤4 round-trips) instead of one per symbol.
    if let Err(e) = graph::upsert_symbol_nodes(pool, repo_id, &node_inputs).await {
        tracing::warn!("failed to store {} symbol node(s) for {}: {}", node_inputs.len(), file_path, e);
    }

    // Persist structural edges (DEFINES, CALLS) derived from intra-file analysis.
    if let Some(lang) = language {
        let parsed_edges = extract_edges(&symbols, &source, &lang);
        let mut edges: Vec<StructuralEdge> = Vec::new();
        for pe in parsed_edges {
            let from_id = range_to_chunk.get(&(pe.from_range.start, pe.from_range.end));
            let to_id = name_to_chunk.get(&pe.to_name);
            if let (Some(&from), Some(&to)) = (from_id, to_id) {
                edges.push(StructuralEdge { from, to, relation: pe.relation });
            }
        }
        // One batched write (≤4 round-trips) instead of one per edge.
        if let Err(e) = graph::upsert_edges(pool, repo_id, &edges).await {
            tracing::warn!("failed to store {} edge(s) for {}: {}", edges.len(), file_path, e);
        }
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

/// Build an `ignore::overrides::Override` that excludes the given glob patterns
/// (relative to `repo_path`). With only negated (`!`) globs and no whitelist
/// globs, the `ignore` crate matches everything by default and ignores only
/// paths that hit one of these patterns — exactly the "index everything except
/// these" semantics we want. Shared by the full-repo walk and the file watcher
/// so both apply identical exclusions. `.git/` is pruned separately.
pub fn build_excludes(repo_path: &Path, exclude: &[String]) -> ignore::overrides::Override {
    use ignore::overrides::OverrideBuilder;
    let mut builder = OverrideBuilder::new(repo_path);
    for pat in exclude {
        let pat = pat.trim();
        if pat.is_empty() {
            continue;
        }
        // A leading `!` makes an override glob an *ignore* (exclude) rule.
        if let Err(e) = builder.add(&format!("!{pat}")) {
            tracing::warn!("ignoring invalid exclude glob {:?}: {}", pat, e);
        }
    }
    builder.build().unwrap_or_else(|e| {
        tracing::warn!(
            "failed to build exclude globset for {}: {}",
            repo_path.display(), e
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
        .skip(1) // rel itself already tested above
        .take_while(|a| !a.as_os_str().is_empty())
        .any(|ancestor| overrides.matched(ancestor, true).is_ignore())
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
// Pool, ids, embedder, config knobs and a progress callback — all distinct
// concerns; a param struct would obscure more than it clarifies.
#[allow(clippy::too_many_arguments)]
pub async fn index_repo(
    pool: &PgPool,
    repo_id: Uuid,
    repo_path: &Path,
    embedder: Arc<dyn EmbeddingBackend>,
    embed_batch_size: usize,
    expected_dim: usize,
    exclude: &[String],
    on_progress: impl Fn(usize, usize, &Path),
) -> Result<(BatchOutcome, Vec<SkipRecord>)> {
    use ignore::WalkBuilder;

    // Index everything under the repo root: no .gitignore / hidden-file
    // filtering. Only `.git/` (pruned below), binary/oversize files (skipped in
    // index_file), and the per-repo `exclude` globs are left out.
    let overrides = build_excludes(repo_path, exclude);
    let walker = WalkBuilder::new(repo_path)
        .standard_filters(false)
        .overrides(overrides)
        .filter_entry(|e| e.file_name() != ".git")
        .build();

    let mut files: Vec<std::path::PathBuf> = vec![];
    for entry in walker.flatten() {
        if entry.file_type().map(|t| t.is_file()).unwrap_or(false) {
            files.push(entry.path().to_owned());
        }
    }

    // The authoritative set of file paths after this walk. `index_file` stores
    // `file_path` as `path.to_string_lossy()`, so build `keep` the same way to
    // prune orphaned chunks (deleted-on-disk or newly-excluded files) below.
    let keep: Vec<String> = files.iter().map(|p| p.to_string_lossy().to_string()).collect();

    let total = files.len();
    let mut done = 0usize;
    let mut any_succeeded = false;
    let mut skips: Vec<SkipRecord> = Vec::new();

    for file in &files {
        // 1500-char cap keeps chunks at a useful search granularity: one
        // embedding per ~symbol-sized span rather than one blurred vector per
        // huge file. model2vec mean-pools over all tokens (no context-window
        // truncation), so this is a quality knob, not a hard limit.
        //
        // Per-file watchdog: `index_file` runs entirely inside one
        // `tokio::time::timeout`. If a single file's parse + edge-extract +
        // chunking + graph write together exceed `FILE_INDEX_TIMEOUT_SECS`, we
        // log a warning, record a SkipRecord with reason "file timed out",
        // and move on. This is the file-level analogue of the per-cypher
        // statement_timeout in `graph.rs` (issue #5) and addresses the parser
        // hang on dense TypeScript .d.ts files (issue #6). NOTE: tokio's
        // `timeout` does not cancel a blocking sub-task — if the work was
        // pinned inside `tokio::task::spawn_blocking` on a CPU-bound parser
        // recursion, that thread keeps running until it returns; the index
        // loop is unblocked regardless.
        let work = index_file(
            pool,
            repo_id,
            file,
            embedder.as_ref(),
            1500,
            embed_batch_size,
            expected_dim,
        );
        match tokio::time::timeout(
            std::time::Duration::from_secs(FILE_INDEX_TIMEOUT_SECS),
            work,
        )
        .await
        {
            Ok(Ok(())) => any_succeeded = true,
            Ok(Err(e)) => {
                // Render the full cause chain once, both for the tracing
                // warning (daemon log) and for the structured record (CLI).
                let reason = format!("{:#}", e);
                tracing::warn!("skipping {}: {}", file.display(), reason);
                skips.push(SkipRecord { path: file.clone(), reason });
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
                skips.push(SkipRecord { path: file.clone(), reason });
            }
        }
        done += 1;
        on_progress(done, total, file);
    }

    // finishIndex (Indexing → Indexed) requires BatchOutcome ≠ NoneSucceeded.
    // A totally-failed non-empty batch must NOT mark the repo as indexed.
    let any_failed = !skips.is_empty();
    if any_succeeded || files.is_empty() {
        // Authoritative reindex: drop chunks (and graph nodes) for files no
        // longer in the set — deleted on disk or newly matched by an exclude
        // glob. Skipped only when the whole batch failed: we must not destroy
        // data on a bad run. Files that failed *this* run stay in `keep`, so
        // their prior data is preserved. Non-fatal: a prune error leaves orphans
        // but the index is otherwise valid.
        //
        // Prune the graph first (per orphan file) so we never leave symbol nodes
        // pointing at chunks that no longer exist.
        match crate::store::file_paths_not_in(pool, repo_id, &keep).await {
            Ok(orphans) => {
                for path in &orphans {
                    if let Err(e) = crate::graph::delete_file_symbols(pool, repo_id, path).await {
                        tracing::warn!("graph prune failed for {}: {}", path, e);
                    }
                }
            }
            Err(e) => tracing::warn!("listing orphan files failed for repo {}: {}", repo_id, e),
        }
        match crate::store::prune_chunks_not_in(pool, repo_id, &keep).await {
            Ok(n) if n > 0 => tracing::info!(
                "reindex pruned {} orphaned chunk(s) in repo {}", n, repo_id),
            Ok(_) => {}
            Err(e) => tracing::warn!("orphan prune failed for repo {}: {}", repo_id, e),
        }
        crate::store::mark_indexed(pool, repo_id).await?;
        let outcome = if any_failed { BatchOutcome::SomeSucceeded } else { BatchOutcome::AllSucceeded };
        Ok((outcome, skips))
    } else {
        tracing::error!(
            "repo {}: all {} files failed to index — not marking as indexed",
            repo_id, files.len()
        );
        Err(anyhow::anyhow!(
            "BatchOutcome: no files were successfully indexed in repo {}",
            repo_id
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ov(globs: &[&str]) -> ignore::overrides::Override {
        let v: Vec<String> = globs.iter().map(|s| s.to_string()).collect();
        build_excludes(Path::new("/repo"), &v)
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
        // The directory itself and anything beneath it are excluded …
        assert!(path_excluded(&o, Path::new("target/debug/build/x.rs")));
        assert!(path_excluded(&o, Path::new("target/foo")));
        // … but unrelated paths are still indexed (node_modules NOT excluded).
        assert!(!path_excluded(&o, Path::new("src/lib.rs")));
        assert!(!path_excluded(&o, Path::new("node_modules/left-pad/index.js")));
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
        // Whitespace-only / empty entries must not turn into a match-all.
        let o = ov(&["", "   "]);
        assert!(!path_excluded(&o, Path::new("anything.rs")));
    }
}
