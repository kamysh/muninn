use crate::types::{LineRange, SymbolKind};
use anyhow::Result;

#[derive(Debug, Clone, PartialEq)]
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

fn extract_symbols(
    node: tree_sitter::Node,
    source: &str,
    language: &Language,
    out: &mut Vec<ParsedSymbol>,
) {
    let kind = match (language, node.kind()) {
        (Language::Rust, "function_item") => Some(SymbolKind::Function),
        (Language::Rust, "struct_item") | (Language::Rust, "impl_item") => Some(SymbolKind::Class),
        (Language::Python, "function_definition") => Some(SymbolKind::Function),
        (Language::Python, "class_definition") => Some(SymbolKind::Class),
        (Language::JavaScript | Language::TypeScript, "function_declaration") => Some(SymbolKind::Function),
        (Language::JavaScript | Language::TypeScript, "class_declaration") => Some(SymbolKind::Class),
        _ => None,
    };

    if let Some(k) = kind {
        let name = node.child_by_field_name("name")
            .and_then(|n| n.utf8_text(source.as_bytes()).ok())
            .unwrap_or("<anonymous>")
            .to_string();
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
}