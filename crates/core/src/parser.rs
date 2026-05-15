use crate::types::{LineRange, StructuralRelation, SymbolKind};
use anyhow::Result;

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Language {
    Rust,
    Python,
    JavaScript,
    TypeScript,
}

pub fn detect_language(path: &str) -> Option<Language> {
    let ext = std::path::Path::new(path).extension()?.to_str()?;
    match ext {
        "rs" => Some(Language::Rust),
        "py" => Some(Language::Python),
        "js" | "jsx" => Some(Language::JavaScript),
        "ts" | "tsx" => Some(Language::TypeScript),
        _ => None,
    }
}

#[derive(Debug, Clone)]
pub struct ParsedSymbol {
    pub name: String,
    pub kind: SymbolKind,
    pub range: LineRange,
}

/// A directed structural relationship between two symbols in the same file,
/// identified by their line ranges (resolved to chunk_ids by the pipeline).
#[derive(Debug, Clone)]
pub struct ParsedEdge {
    /// Range of the source symbol (the one that defines/calls).
    pub from_range: LineRange,
    /// Name of the target symbol.
    pub to_name: String,
    pub relation: StructuralRelation,
}

/// Extract intra-file structural edges from a parsed symbol list.
///
/// Produces two kinds of edges:
/// - DEFINES: a Class/Module whose range contains a Function's range.
/// - CALLS: call expressions found inside a Function body that name another
///   symbol in the same file (same-file resolution only; cross-file calls
///   are not resolved here).
pub fn extract_edges(
    symbols: &[ParsedSymbol],
    source: &str,
    language: &Language,
) -> Vec<ParsedEdge> {
    let mut edges = extract_defines(symbols);
    edges.extend(extract_calls(symbols, source, language));
    edges
}

/// DEFINES edges: a container symbol (Class/Module) defines each symbol whose
/// range is strictly contained within it.
fn extract_defines(symbols: &[ParsedSymbol]) -> Vec<ParsedEdge> {
    let mut edges = Vec::new();
    for (i, outer) in symbols.iter().enumerate() {
        if !matches!(outer.kind, SymbolKind::Class | SymbolKind::Module) {
            continue;
        }
        for (j, inner) in symbols.iter().enumerate() {
            if i == j {
                continue;
            }
            if outer.range.start <= inner.range.start && inner.range.end <= outer.range.end {
                edges.push(ParsedEdge {
                    from_range: outer.range.clone(),
                    to_name: inner.name.clone(),
                    relation: StructuralRelation::Defines,
                });
            }
        }
    }
    edges
}

/// CALLS edges: for each Function symbol, walk its subtree in the tree-sitter
/// parse tree, find call expressions, and match callee names against other
/// symbols in the same file.
fn extract_calls(
    symbols: &[ParsedSymbol],
    source: &str,
    language: &Language,
) -> Vec<ParsedEdge> {
    // Build a set of known symbol names for fast lookup.
    let known: std::collections::HashSet<&str> =
        symbols.iter().map(|s| s.name.as_str()).collect();

    let mut parser = tree_sitter::Parser::new();
    let ts_lang = match language {
        Language::Rust => tree_sitter_rust::language(),
        Language::Python => tree_sitter_python::language(),
        Language::JavaScript => tree_sitter_javascript::language(),
        Language::TypeScript => tree_sitter_typescript::language_typescript(),
    };
    if parser.set_language(&ts_lang).is_err() {
        return vec![];
    }
    let tree = match parser.parse(source, None) {
        Some(t) => t,
        None => return vec![],
    };

    let call_node_kind = match language {
        Language::Rust => "call_expression",
        Language::Python => "call",
        Language::JavaScript | Language::TypeScript => "call_expression",
    };

    let mut edges = Vec::new();

    for sym in symbols {
        if sym.kind != SymbolKind::Function {
            continue;
        }
        // Find the tree-sitter node that corresponds to this function's range.
        let func_node = match find_node_at_range(tree.root_node(), source, &sym.range) {
            Some(n) => n,
            None => continue,
        };

        // Walk the function's subtree and collect call expression callee names.
        let callees = collect_callees(func_node, source, call_node_kind);
        for callee in callees {
            // Only emit edges to symbols we know exist in this file, and skip
            // self-calls.
            if callee != sym.name && known.contains(callee.as_str()) {
                edges.push(ParsedEdge {
                    from_range: sym.range.clone(),
                    to_name: callee,
                    relation: StructuralRelation::Calls,
                });
            }
        }
    }
    edges
}

/// Find the tree-sitter node whose start/end lines match the given LineRange.
fn find_node_at_range<'a>(
    root: tree_sitter::Node<'a>,
    _source: &str,
    range: &LineRange,
) -> Option<tree_sitter::Node<'a>> {
    let target_start = (range.start as usize).saturating_sub(1); // 0-based row
    let target_end = range.end as usize;

    // Depth-first search for the node whose row span matches.
    let mut stack = vec![root];
    while let Some(node) = stack.pop() {
        let start_row = node.start_position().row;
        let end_row = node.end_position().row + 1; // make inclusive end 1-past
        if start_row == target_start && end_row == target_end {
            return Some(node);
        }
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            stack.push(child);
        }
    }
    None
}

/// Collect unique callee names from call expressions within a node's subtree.
fn collect_callees(node: tree_sitter::Node, source: &str, call_kind: &str) -> Vec<String> {
    let mut callees = Vec::new();
    let mut seen = std::collections::HashSet::new();
    collect_callees_rec(node, source, call_kind, &mut callees, &mut seen);
    callees
}

fn collect_callees_rec(
    node: tree_sitter::Node,
    source: &str,
    call_kind: &str,
    out: &mut Vec<String>,
    seen: &mut std::collections::HashSet<String>,
) {
    if node.kind() == call_kind {
        // The function/callee is the "function" field (Rust, JS/TS) or
        // the first named child (Python).
        let callee_node = node.child_by_field_name("function")
            .or_else(|| node.named_child(0));

        if let Some(cn) = callee_node {
            // For `foo(...)` the node is an identifier; for `self.foo(...)`
            // or `obj.method(...)` we want the last identifier child.
            let name = extract_callee_name(cn, source);
            if !name.is_empty() && seen.insert(name.clone()) {
                out.push(name);
            }
        }
    }

    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        collect_callees_rec(child, source, call_kind, out, seen);
    }
}

/// Extract a simple name from a callee node.
/// For identifiers, returns the text directly.
/// For field expressions / attribute access (`a.b`), returns the field name (`b`).
fn extract_callee_name(node: tree_sitter::Node, source: &str) -> String {
    match node.kind() {
        "identifier" | "field_identifier" => {
            node.utf8_text(source.as_bytes())
                .unwrap_or("")
                .to_string()
        }
        // Rust: `field_expression` → last child is the method name
        // Python: `attribute` → `attribute` field
        // JS/TS: `member_expression` → `property` field
        _ => {
            let name_node = node.child_by_field_name("field")
                .or_else(|| node.child_by_field_name("attribute"))
                .or_else(|| node.child_by_field_name("property"));
            name_node
                .and_then(|n| n.utf8_text(source.as_bytes()).ok())
                .unwrap_or("")
                .to_string()
        }
    }
}

pub fn parse_file(source: &str, language: Language) -> Result<Vec<ParsedSymbol>> {
    let mut parser = tree_sitter::Parser::new();
    let ts_lang = match language {
        Language::Rust => tree_sitter_rust::language(),
        Language::Python => tree_sitter_python::language(),
        Language::JavaScript => tree_sitter_javascript::language(),
        Language::TypeScript => tree_sitter_typescript::language_typescript(),
    };
    parser.set_language(&ts_lang)?;

    let tree = parser.parse(source, None)
        .ok_or_else(|| anyhow::anyhow!("tree-sitter parse failed"))?;

    let mut symbols = Vec::new();
    extract_symbols(tree.root_node(), source, &language, &mut symbols);
    Ok(symbols)
}

/// Extract a display name for a symbol node.
/// For named declarations (functions, classes, modules) uses the "name" field.
/// For imports uses the first named child (the path/module being imported).
fn extract_symbol_name(
    kind: &SymbolKind,
    node: tree_sitter::Node,
    source: &str,
) -> String {
    match kind {
        SymbolKind::Import => {
            // Try "name" field first (Python), then first named child (Rust use_declaration path,
            // JS/TS import source).
            node.child_by_field_name("name")
                .or_else(|| node.child_by_field_name("source"))
                .or_else(|| (0..node.named_child_count()).find_map(|i| node.named_child(i)))
                .and_then(|n| n.utf8_text(source.as_bytes()).ok())
                .map(|s| s.trim_matches('"').trim_matches('\'').to_string())
                .unwrap_or_else(|| "<import>".to_string())
        }
        _ => {
            node.child_by_field_name("name")
                .and_then(|n| n.utf8_text(source.as_bytes()).ok())
                .unwrap_or("<anonymous>")
                .to_string()
        }
    }
}

fn extract_symbols(
    node: tree_sitter::Node,
    source: &str,
    language: &Language,
    out: &mut Vec<ParsedSymbol>,
) {
    let kind = match (language, node.kind()) {
        (Language::Rust, "function_item") => Some(SymbolKind::Function),
        (Language::Rust, "struct_item") | (Language::Rust, "impl_item") => Some(SymbolKind::Class),
        (Language::Rust, "mod_item") => Some(SymbolKind::Module),
        (Language::Rust, "use_declaration") => Some(SymbolKind::Import),
        (Language::Python, "function_definition") => Some(SymbolKind::Function),
        (Language::Python, "class_definition") => Some(SymbolKind::Class),
        (Language::Python, "import_statement") | (Language::Python, "import_from_statement") => Some(SymbolKind::Import),
        (Language::JavaScript | Language::TypeScript, "function_declaration") => Some(SymbolKind::Function),
        (Language::JavaScript | Language::TypeScript, "class_declaration") => Some(SymbolKind::Class),
        (Language::JavaScript | Language::TypeScript, "import_statement") => Some(SymbolKind::Import),
        _ => None,
    };

    if let Some(k) = kind {
        let name = extract_symbol_name(&k, node, source);
        let start_line = node.start_position().row as u32 + 1;
        let end_line = node.end_position().row as u32 + 1;
        out.push(ParsedSymbol {
            name,
            kind: k,
            range: LineRange { start: start_line, end: end_line },
        });
    }

    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        extract_symbols(child, source, language, out);
    }
}

/// Chunk file content by symbol boundaries; fall back to max_chars splitting
pub fn chunk_file(
    source: &str,
    symbols: &[ParsedSymbol],
    max_chars: usize,
) -> Vec<crate::types::Chunk> {
    use uuid::Uuid;
    let lines: Vec<&str> = source.lines().collect();
    let mut chunks = Vec::new();

    if symbols.is_empty() {
        let mut start = 0usize;
        while start < lines.len() {
            let mut acc = String::new();
            let mut end = start;
            while end < lines.len() && acc.len() + lines[end].len() < max_chars {
                acc.push_str(lines[end]);
                acc.push('\n');
                end += 1;
            }
            if end == start { acc = lines[start].to_string(); end += 1; }
            chunks.push(crate::types::Chunk {
                id: Uuid::new_v4(),
                repo_id: Uuid::nil(),
                file_path: String::new(),
                range: LineRange { start: start as u32 + 1, end: end as u32 },
                content: acc,
                embedding: None,
            });
            start = end;
        }
        return chunks;
    }

    for sym in symbols {
        let s = (sym.range.start as usize).saturating_sub(1);
        let e = sym.range.end as usize;
        let content: String = lines.get(s..e.min(lines.len()))
            .unwrap_or(&[])
            .join("\n");
        if content.is_empty() { continue; }
        chunks.push(crate::types::Chunk {
            id: Uuid::new_v4(),
            repo_id: Uuid::nil(),
            file_path: String::new(),
            range: sym.range.clone(),
            content,
            embedding: None,
        });
    }
    chunks
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn detect_rust_language() {
        assert_eq!(detect_language("foo.rs"), Some(Language::Rust));
    }

    #[test]
    fn detect_python_language() {
        assert_eq!(detect_language("bar.py"), Some(Language::Python));
    }

    #[test]
    fn detect_typescript_language() {
        assert_eq!(detect_language("baz.ts"), Some(Language::TypeScript));
    }

    #[test]
    fn detect_unknown_returns_none() {
        assert_eq!(detect_language("file.xyz"), None);
    }

    #[test]
    fn parse_rust_extracts_function() {
        let src = "fn hello_world() {\n    println!(\"hello\");\n}\n";
        let symbols = parse_file(src, Language::Rust).unwrap();
        assert!(symbols.iter().any(|s| s.name == "hello_world"));
    }

    #[test]
    fn chunk_by_symbols_respects_boundaries() {
        let src = "fn a() {}\nfn b() {}\n";
        let symbols = parse_file(src, Language::Rust).unwrap();
        let chunks = chunk_file(src, &symbols, 512);
        assert!(!chunks.is_empty());
        for c in &chunks {
            assert!(c.range.is_valid());
            assert!(!c.content.is_empty());
        }
    }

    #[test]
    fn detect_jsx_is_javascript() {
        assert_eq!(detect_language("comp.jsx"), Some(Language::JavaScript));
    }

    #[test]
    fn detect_tsx_is_typescript() {
        assert_eq!(detect_language("comp.tsx"), Some(Language::TypeScript));
    }

    #[test]
    fn parse_python_extracts_function() {
        let src = "def greet(name):\n    return 'hello ' + name\n";
        let symbols = parse_file(src, Language::Python).unwrap();
        assert!(symbols.iter().any(|s| s.name == "greet"));
    }

    #[test]
    fn parse_python_extracts_class() {
        let src = "class Foo:\n    pass\n";
        let symbols = parse_file(src, Language::Python).unwrap();
        assert!(symbols.iter().any(|s| s.name == "Foo"));
    }

    #[test]
    fn chunk_empty_source_produces_no_chunks() {
        let chunks = chunk_file("", &[], 512);
        assert!(chunks.is_empty());
    }

    #[test]
    fn chunk_respects_max_chars() {
        // source with no symbols falls back to max_chars splitting
        let long_line = "x".repeat(100);
        let src = format!("{}\n{}\n{}\n", long_line, long_line, long_line);
        let chunks = chunk_file(&src, &[], 150);
        for c in &chunks {
            assert!(!c.content.is_empty());
            assert!(c.range.is_valid());
        }
    }

    use quickcheck::quickcheck;

    quickcheck! {
        fn prop_chunk_all_ranges_valid(content: String) -> bool {
            let chunks = chunk_file(&content, &[], 256);
            chunks.iter().all(|c| c.range.is_valid())
        }

        fn prop_chunk_all_content_nonempty(content: String) -> bool {
            let chunks = chunk_file(&content, &[], 256);
            chunks.iter().all(|c| !c.content.is_empty())
        }

        fn prop_detect_language_rs_always_rust(stem: String) -> quickcheck::TestResult {
            let sanitized: String = stem.chars()
                .map(|c| if c.is_alphanumeric() || c == '-' { c } else { '_' })
                .collect();
            if sanitized.is_empty() || sanitized.starts_with('.') {
                return quickcheck::TestResult::discard();
            }
            let path = format!("{}.rs", sanitized);
            quickcheck::TestResult::from_bool(detect_language(&path) == Some(Language::Rust))
        }

        fn prop_detect_language_py_always_python(stem: String) -> quickcheck::TestResult {
            let sanitized: String = stem.chars()
                .map(|c| if c.is_alphanumeric() || c == '-' { c } else { '_' })
                .collect();
            if sanitized.is_empty() || sanitized.starts_with('.') {
                return quickcheck::TestResult::discard();
            }
            let path = format!("{}.py", sanitized);
            quickcheck::TestResult::from_bool(detect_language(&path) == Some(Language::Python))
        }
    }
}