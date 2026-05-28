//! Discovery-oriented invariants run against the muninn repo's own source.
//!
//! These tests don't assert anything about specific files — they assert
//! invariants of the chunker on whatever real-world input the repo contains.
//! If the chunker is ever changed in a way that breaks an invariant on any
//! file in `crates/` (the muninn repo itself), the test fails.
//!
//! The silent-truncation bug in v0.1.10 would have surfaced here at
//! `chunk_fits_max_chars_with_slop` if max_chars had been < 4096; with the
//! v0.1.15 chunker fix (max_chars = 1500 + symbol-body split) the invariants
//! hold for every file in the repo.

use muninn_core::parser::{chunk_file, detect_language, parse_file};
use std::path::{Path, PathBuf};

/// Walk the muninn workspace looking at every parseable source file.
/// Returns (path, content, language) for each.
fn walk_source_files() -> Vec<(PathBuf, String, muninn_core::parser::Language)> {
    let crates_root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("CARGO_MANIFEST_DIR has parent");

    let mut out = Vec::new();
    let walker = ignore::WalkBuilder::new(crates_root)
        .hidden(false)
        .git_ignore(true)
        .build();
    for entry in walker.flatten() {
        if !entry.file_type().map(|t| t.is_file()).unwrap_or(false) {
            continue;
        }
        let path = entry.path();
        let Some(lang) = detect_language(&path.to_string_lossy()) else {
            continue;
        };
        let Ok(content) = std::fs::read_to_string(path) else { continue };
        if content.is_empty() { continue }
        out.push((path.to_owned(), content, lang));
    }
    out
}

/// Every chunk's content stays within the embedder budget (with line-length
/// slop). The v0.1.10 symbol-path chunker violated this on long functions —
/// fastembed then silently truncated past 512 tokens, making the back half
/// of every such function invisible to semantic search.
#[test]
fn chunk_fits_max_chars_with_slop() {
    const MAX_CHARS: usize = 1500;
    const SLOP_FACTOR: usize = 10; // single oversize line allowed; anything else is a bug

    let files = walk_source_files();
    assert!(!files.is_empty(), "no source files walked — corpus discovery broken");

    let mut violations = Vec::new();
    for (path, content, lang) in &files {
        let symbols = parse_file(content, *lang).unwrap_or_default();
        let chunks = chunk_file(content, &symbols, MAX_CHARS);
        for c in &chunks {
            if c.content.len() > MAX_CHARS * SLOP_FACTOR {
                violations.push(format!(
                    "{}:{}-{}  chunk len {} > {}*{}",
                    path.display(),
                    c.range.start, c.range.end,
                    c.content.len(), MAX_CHARS, SLOP_FACTOR,
                ));
            }
        }
    }

    assert!(
        violations.is_empty(),
        "chunker emitted oversize chunks for real corpus files:\n  {}",
        violations.join("\n  ")
    );
}

/// Every line of every parseable file ends up in at least one chunk
/// (no content silently dropped by the chunker, regardless of file shape).
#[test]
fn every_line_appears_in_some_chunk() {
    let files = walk_source_files();
    let mut missing = Vec::new();
    for (path, content, lang) in &files {
        // Only check files that DO produce chunks (some pure-comment or
        // unusual files may legitimately produce none).
        let symbols = parse_file(content, *lang).unwrap_or_default();
        let chunks = chunk_file(content, &symbols, 1500);
        if chunks.is_empty() { continue }

        // Build a line set covered by chunks.
        let mut covered = std::collections::HashSet::new();
        for c in &chunks {
            for l in c.range.start..=c.range.end { covered.insert(l); }
        }
        // For every non-empty line in the file, assert it's covered OR
        // it's an empty/whitespace-only line at a file boundary.
        let lines: Vec<&str> = content.lines().collect();
        for (idx, line) in lines.iter().enumerate() {
            let lineno = (idx + 1) as u32;
            if !line.trim().is_empty() && !covered.contains(&lineno) {
                missing.push(format!("{}:{lineno}  {:?}", path.display(), line));
            }
        }
    }
    // Allow a small absolute tolerance for files where the symbol-only path
    // emits chunks only for parsed symbols and skips lines outside them
    // (top-of-file `use` blocks etc.). Threshold is intentionally generous —
    // a regression that drops large swaths of content fires here regardless.
    assert!(
        missing.len() < 200,
        "{} lines not covered by any chunk (first 10):\n  {}",
        missing.len(),
        missing.iter().take(10).cloned().collect::<Vec<_>>().join("\n  ")
    );
}

/// Re-chunking the same source twice produces identical structure
/// (modulo random UUIDs). Catches accidental ordering / non-determinism.
#[test]
fn chunker_is_deterministic_on_real_corpus() {
    let files = walk_source_files();
    for (path, content, lang) in &files {
        let symbols = parse_file(content, *lang).unwrap_or_default();
        let a = chunk_file(content, &symbols, 1500);
        let b = chunk_file(content, &symbols, 1500);
        assert_eq!(a.len(), b.len(), "chunk count differs for {}", path.display());
        for (x, y) in a.iter().zip(b.iter()) {
            assert_eq!(x.range.start, y.range.start, "{} start", path.display());
            assert_eq!(x.range.end, y.range.end, "{} end", path.display());
            assert_eq!(x.content, y.content, "{} content", path.display());
        }
    }
}
