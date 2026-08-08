//! Adversarial / edge-case inputs the chunker should handle without panic
//! or silent data loss. Each fixture targets a class of input that has
//! historically broken text-processing pipelines.

use muninn_core::parser::{chunk_file, parse_file, Language};

#[test]
fn one_giant_single_line() {
    // 50 KB on one line — minified JSON, generated code, etc.
    // Must not panic. The single-line case forces the chunker's "even one
    // line exceeds max_chars" fallback path.
    let src = "x".repeat(50_000);
    let chunks = chunk_file(&src, &[], 1500);
    assert!(
        !chunks.is_empty(),
        "expected at least one chunk for non-empty input"
    );
    for c in &chunks {
        assert!(c.range.is_valid());
        assert!(!c.content.is_empty());
        // The single-line fallback must itself be byte-bounded — an
        // unbounded chunk here is exactly what let a multi-MB single-line
        // file (e.g. minified JSON with an embedded base64 blob) through to
        // Postgres's ~1MB tsvector limit and fail to index. Some slack for
        // multi-byte UTF-8 boundary rounding, none for "just emit it whole".
        assert!(
            c.content.len() <= 1500 + 4,
            "single-line fallback chunk exceeds max_chars: {} bytes",
            c.content.len()
        );
    }
}

#[test]
fn one_giant_single_line_past_tsvector_limit() {
    // Reproduces the real-world failure directly: a single line large enough
    // to exceed Postgres's tsvector size limit (1_048_575 bytes) if emitted
    // as one unbounded chunk. Every chunk must stay well under that.
    const TSVECTOR_LIMIT: usize = 1_048_575;
    let src = "y".repeat(TSVECTOR_LIMIT * 3);
    let chunks = chunk_file(&src, &[], 1500);
    assert!(!chunks.is_empty());
    for c in &chunks {
        assert!(
            c.content.len() < TSVECTOR_LIMIT,
            "chunk of {} bytes would still overflow tsvector's {} byte limit",
            c.content.len(),
            TSVECTOR_LIMIT
        );
    }
    // No content lost: total bytes across chunks (minus trailing newlines
    // the accumulator wouldn't add here, since it's all one line split into
    // pieces with no separators) reconstructs the source length.
    let total: usize = chunks.iter().map(|c| c.content.len()).sum();
    assert_eq!(total, src.len());
}

#[test]
fn one_giant_symbol_body() {
    // 400-line function body — the v0.1.10 chunker emitted this as a single
    // chunk that fastembed silently truncated past 512 tokens. The v0.1.15
    // splitter must break it into multiple chunks, all within budget.
    let body: Vec<String> = (0..400)
        .map(|i| format!("    let v_{i} = {i} * {i} + {i};"))
        .collect();
    let src = format!("fn giant() {{\n{}\n}}\n", body.join("\n"));
    let symbols = parse_file(&src, Language::Rust).unwrap();
    let chunks = chunk_file(&src, &symbols, 1500);

    assert!(
        chunks.len() >= 2,
        "oversize symbol should split, got {} chunks",
        chunks.len()
    );
    for c in &chunks {
        assert!(
            c.content.len() <= 1500 * 10,
            "sub-chunk len {}",
            c.content.len()
        );
    }

    // Every variable name appears somewhere in the concatenated chunks
    // (no silent line drops).
    let combined: String = chunks
        .iter()
        .map(|c| c.content.as_str())
        .collect::<Vec<_>>()
        .join("\n");
    for i in 0..400 {
        assert!(combined.contains(&format!("v_{i}")), "lost line for v_{i}");
    }

    // The first sub-chunk's start line matches the symbol's start
    // (pipeline.rs relies on this for graph linkage).
    let sym = &symbols[0];
    assert!(
        chunks.iter().any(|c| c.range.start == sym.range.start),
        "no sub-chunk inherits the symbol's start line"
    );
}

#[test]
fn unicode_mixed() {
    let src =
        "fn café() {\n    let π = 3.14;\n    let 中文 = \"日本語\";\n    let 🦀 = \"crab\";\n}\n";
    let symbols = parse_file(src, Language::Rust).unwrap_or_default();
    let _chunks = chunk_file(src, &symbols, 1500);
    // Just shouldn't panic or hang. Output validity is checked by other invariants.
}

#[test]
fn crlf_line_endings() {
    let src = "fn a() {\r\n    let x = 1;\r\n}\r\nfn b() {\r\n    let y = 2;\r\n}\r\n";
    let symbols = parse_file(src, Language::Rust).unwrap_or_default();
    let chunks = chunk_file(src, &symbols, 1500);
    for c in &chunks {
        assert!(c.range.is_valid());
        assert!(!c.content.is_empty());
    }
}

#[test]
fn no_symbols_no_newlines() {
    // No newlines, no parseable symbols — falls into the no-symbols path
    // with a single line longer than any reasonable max_chars.
    let src = "xx ".repeat(2000); // ~6000 chars, no \n
    let chunks = chunk_file(&src, &[], 1500);
    assert!(!chunks.is_empty());
    for c in &chunks {
        assert!(c.range.is_valid());
    }
}

#[test]
fn empty_file_no_crash() {
    assert!(chunk_file("", &[], 1500).is_empty());
    assert!(chunk_file("\n", &[], 1500)
        .iter()
        .all(|c| !c.content.is_empty()));
    assert!(chunk_file("   ", &[], 1500)
        .iter()
        .all(|c| c.range.is_valid()));
}

#[test]
fn only_blank_lines() {
    let src = "\n".repeat(100);
    let chunks = chunk_file(&src, &[], 1500);
    // May or may not produce chunks — either way, no panic and any chunks valid.
    for c in &chunks {
        assert!(c.range.is_valid());
    }
}

#[test]
fn nul_byte_in_content() {
    // \0 in a string. Should not panic the chunker.
    let src = "fn a() {\n    let s = \"\0\0\0\";\n}\n";
    let symbols = parse_file(src, Language::Rust).unwrap_or_default();
    let chunks = chunk_file(src, &symbols, 1500);
    for c in &chunks {
        assert!(c.range.is_valid());
    }
}

#[test]
fn giant_single_line_multibyte_utf8_no_panic() {
    // Multi-byte chars near a max_chars boundary must never split mid-codepoint.
    let src = "€".repeat(2000); // 3 bytes/char in UTF-8, 6000 bytes total
    let chunks = chunk_file(&src, &[], 1500);
    assert!(!chunks.is_empty());
    for c in &chunks {
        assert!(c.content.len() <= 1500 + 4);
        assert!(std::str::from_utf8(c.content.as_bytes()).is_ok());
    }
    let total: usize = chunks.iter().map(|c| c.content.len()).sum();
    assert_eq!(total, src.len());
}
