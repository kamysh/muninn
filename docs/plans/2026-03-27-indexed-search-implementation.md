# ai-mem Indexed Search Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Build a two-process Rust MCP server (`ai-mem`) that provides full-text, semantic, and structural code search over registered repositories for Claude Code.

**Architecture:** `ai-mem-index` daemon watches repos, parses files with tree-sitter, generates embeddings, and writes to PostgreSQL (pgvector + AGE). `ai-mem-mcp` is a lightweight MCP server that queries the same Postgres database to answer Claude's search requests. Shared config at `~/.config/ai-mem/config.toml`.

**Tech Stack:** Rust (tokio, sqlx, clap, serde), PostgreSQL 16+ (pgvector, apache-age), tree-sitter, rmcp (Rust MCP SDK), notify (file watching), Voyage AI / OpenAI / local embeddings.

---

## Prerequisites

- Nix with flakes enabled (`nix develop` provides everything below)
- PostgreSQL 16+ with pgvector and apache-age running externally
- Rust stable toolchain (provided by dev shell via rust-overlay)
- sqlx-cli (provided by dev shell)
- Agda + standard library (provided by dev shell)
- Voyage AI API key (for default embedding backend)

---

### Task 0: Nix Flake

**Files:**
- Create: `flake.nix`

Provides a reproducible dev shell via `nix develop` with: Rust stable + rust-analyzer + clippy + rustfmt, sqlx-cli, psql client, Agda with standard library, cargo-nextest, and pkg-config/openssl for reqwest. PostgreSQL with pgvector and AGE is assumed to be running externally.

**Step 1: Create flake.nix**

See `flake.nix` in repo root. Key structure:
- inputs: nixpkgs (unstable), rust-overlay, flake-utils
- `agdaWithStdlib`: agda + standard-library
- devShell exports: `DATABASE_URL`, `TEST_DATABASE_URL`
- PostgreSQL assumed external — only psql client included

**Step 2: Enter dev shell to verify**

```bash
nix develop
rustc --version   # stable
postgres --version
agda --version
sqlx --version
```

**Step 3: Commit**

```bash
git add flake.nix
git commit -m "chore: add Nix flake with Rust, PostgreSQL+pgvector+AGE, Agda dev shell"
```

---

### Task 1: Formal Agda Specification

**Files:**
- Create: `spec/AiMem.agda`
- Create: `spec/README.md`

This step has no Rust code. Write the formal specification in Agda before touching implementation.

**Step 1: Create the Agda spec file**

```agda
-- spec/AiMem.agda
module AiMem where

open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- ─── Core Types ────────────────────────────────────────────────────────────────

record UUID : Set where
  field value : String

record FilePath : Set where
  field value : String

record RepoId : Set where
  field value : UUID

record ChunkId : Set where
  field value : UUID

record LineRange : Set where
  field start : ℕ
        end   : ℕ

-- A chunk is a contiguous slice of a file with optional embedding
record Chunk : Set where
  field id        : ChunkId
        repoId    : RepoId
        filePath  : FilePath
        range     : LineRange
        content   : String
        embedding : Maybe (List Float)  -- absent until embedded

-- A registered repository
record Repo : Set where
  field id        : RepoId
        path      : FilePath
        name      : String
        indexedAt : Maybe String  -- ISO-8601, nothing = never indexed

-- ─── Repo Registration Invariants ──────────────────────────────────────────────

-- Two repos must not share the same path
UniqueRepoPaths : List Repo → Set
UniqueRepoPaths repos = ∀ (r1 r2 : Repo) →
  Repo.path r1 ≡ Repo.path r2 →
  Repo.id r1 ≡ Repo.id r2

-- ─── Indexing State Machine ────────────────────────────────────────────────────

data IndexState : Set where
  Unindexed  : IndexState   -- repo registered, never indexed
  Indexing   : IndexState   -- full reindex in progress
  Indexed    : IndexState   -- index up to date
  Watching   : IndexState   -- indexed + file watcher active
  Stale      : IndexState   -- indexed but watcher detected changes not yet applied

-- Valid transitions
data IndexTransition : IndexState → IndexState → Set where
  StartIndex   : IndexTransition Unindexed Indexing
  StartReindex : IndexTransition Indexed   Indexing
  StartReindex2: IndexTransition Stale     Indexing
  FinishIndex  : IndexTransition Indexing  Indexed
  AttachWatcher: IndexTransition Indexed   Watching
  DetectChange : IndexTransition Watching  Stale
  StartWatch   : IndexTransition Stale     Indexing

-- ─── Chunk Validity ────────────────────────────────────────────────────────────

open import Data.Nat using (ℕ; _≤_)

-- end line must be >= start line
ValidRange : LineRange → Set
ValidRange r = LineRange.start r ≤ LineRange.end r

-- A chunk's content must be non-empty
ValidChunk : Chunk → Set
ValidChunk c = Chunk.content c ≢ ""
  where open import Data.String using (_≢_)

-- ─── Query Semantics ───────────────────────────────────────────────────────────

-- Semantic similarity is a value in [0, 1]
record Similarity : Set where
  field value : Float
  -- invariant: 0.0 ≤ value ≤ 1.0 (enforced externally)

record SearchResult : Set where
  field chunk      : Chunk
        score      : Similarity
        filePath   : FilePath
        lineRange  : LineRange

-- Reciprocal Rank Fusion: given two ranked lists, merged rank is 1/(k + rank)
-- where k=60 is the standard constant
rrfScore : ℕ → Float
rrfScore rank = 1.0 / (60.0 + fromℕ rank)
  where open import Data.Float using (fromℕ)

-- Hybrid search result is the RRF-merged combination of semantic + fulltext results
-- The merged list must be no longer than the requested limit
HybridResultBound : (limit : ℕ) → List SearchResult → Set
HybridResultBound limit results = length results ≤ limit
  where open import Data.List using (length)

-- ─── Structural Relations ──────────────────────────────────────────────────────

data Relation : Set where
  Calls       : Relation
  Imports     : Relation
  Defines     : Relation
  InheritsFrom: Relation

record StructuralEdge : Set where
  field from     : ChunkId
        to       : ChunkId
        relation : Relation

-- ─── Embedding Backend ─────────────────────────────────────────────────────────

data EmbeddingBackend : Set where
  Voyage : EmbeddingBackend
  OpenAI : EmbeddingBackend
  Local  : EmbeddingBackend

-- Embedding dimension is fixed per backend+model
EmbeddingDimension : EmbeddingBackend → ℕ
EmbeddingDimension Voyage = 1024   -- voyage-code-3
EmbeddingDimension OpenAI = 1536   -- text-embedding-3-small
EmbeddingDimension Local  = 768    -- default fastembed model

-- All chunks for a repo must use the same embedding dimension
ConsistentEmbeddings : EmbeddingBackend → List Chunk → Set
ConsistentEmbeddings backend chunks =
  ∀ (c : Chunk) →
    Maybe.map length (Chunk.embedding c) ≡ just (EmbeddingDimension backend)
  where
    open import Data.Maybe using (map)
    open import Data.List using (length)
```

**Step 2: Create spec README**

```markdown
<!-- spec/README.md -->
# Formal Specification

This directory contains the Agda formal specification for ai-mem.

## Checking the spec

Install Agda (2.6.4+):

    cabal install Agda

Check the spec:

    agda spec/AiMem.agda

## What is specified

- Core data types: Chunk, Repo, LineRange, SearchResult, StructuralEdge
- Repo registration invariant: unique paths
- Indexing state machine with valid transitions
- Chunk and range validity invariants
- Query semantics: similarity bounds, RRF scoring, hybrid result bounds
- Embedding backend dimension consistency
```

**Step 3: Verify spec type-checks**

```bash
agda spec/AiMem.agda
```
Expected: no errors (some holes may remain for Float arithmetic — acceptable for spec phase)

**Step 4: Commit**

```bash
git add spec/
git commit -m "spec: formal Agda specification for ai-mem data types and invariants"
```

---

### Task 2: Rust Workspace Setup

**Files:**
- Create: `Cargo.toml` (workspace)
- Create: `crates/core/Cargo.toml`
- Create: `crates/core/src/lib.rs`
- Create: `crates/indexer/Cargo.toml`
- Create: `crates/indexer/src/main.rs`
- Create: `crates/mcp/Cargo.toml`
- Create: `crates/mcp/src/main.rs`
- Create: `crates/cli/Cargo.toml`
- Create: `crates/cli/src/main.rs`

**Step 1: Create workspace Cargo.toml**

```toml
# Cargo.toml
[workspace]
members = [
    "crates/core",
    "crates/indexer",
    "crates/mcp",
    "crates/cli",
]
resolver = "2"

[workspace.dependencies]
tokio = { version = "1", features = ["full"] }
sqlx = { version = "0.7", features = ["runtime-tokio-rustls", "postgres", "uuid", "chrono", "json"] }
serde = { version = "1", features = ["derive"] }
serde_json = "1"
toml = "0.8"
uuid = { version = "1", features = ["v4", "serde"] }
chrono = { version = "0.4", features = ["serde"] }
anyhow = "1"
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter"] }
clap = { version = "4", features = ["derive"] }
```

**Step 2: Create core crate**

```toml
# crates/core/Cargo.toml
[package]
name = "ai-mem-core"
version = "0.1.0"
edition = "2021"

[dependencies]
serde = { workspace = true }
uuid = { workspace = true }
chrono = { workspace = true }
anyhow = { workspace = true }
```

```rust
// crates/core/src/lib.rs
pub mod config;
pub mod types;
```

**Step 3: Create indexer, mcp, cli crate stubs**

```toml
# crates/indexer/Cargo.toml
[package]
name = "ai-mem-index"
version = "0.1.0"
edition = "2021"

[[bin]]
name = "ai-mem-index"
path = "src/main.rs"

[dependencies]
ai-mem-core = { path = "../core" }
tokio = { workspace = true }
anyhow = { workspace = true }
tracing = { workspace = true }
tracing-subscriber = { workspace = true }
```

```rust
// crates/indexer/src/main.rs
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    tracing_subscriber::fmt::init();
    tracing::info!("ai-mem-index starting");
    Ok(())
}
```

```toml
# crates/mcp/Cargo.toml
[package]
name = "ai-mem-mcp"
version = "0.1.0"
edition = "2021"

[[bin]]
name = "ai-mem-mcp"
path = "src/main.rs"

[dependencies]
ai-mem-core = { path = "../core" }
tokio = { workspace = true }
anyhow = { workspace = true }
tracing = { workspace = true }
tracing-subscriber = { workspace = true }
```

```rust
// crates/mcp/src/main.rs
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    tracing_subscriber::fmt::init();
    tracing::info!("ai-mem-mcp starting");
    Ok(())
}
```

```toml
# crates/cli/Cargo.toml
[package]
name = "ai-mem"
version = "0.1.0"
edition = "2021"

[[bin]]
name = "ai-mem"
path = "src/main.rs"

[dependencies]
ai-mem-core = { path = "../core" }
clap = { workspace = true }
anyhow = { workspace = true }
tokio = { workspace = true }
```

```rust
// crates/cli/src/main.rs
use clap::Parser;

#[derive(Parser)]
#[command(name = "ai-mem", about = "ai-mem repository index manager")]
struct Cli {}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let _cli = Cli::parse();
    Ok(())
}
```

**Step 4: Verify workspace builds**

```bash
cargo build
```
Expected: all four crates compile with 0 errors.

**Step 5: Commit**

```bash
git add Cargo.toml crates/
git commit -m "chore: initialize Rust workspace with core, indexer, mcp, cli crates"
```

---

### Task 3: Core Types and Config

**Files:**
- Create: `crates/core/src/types.rs`
- Create: `crates/core/src/config.rs`
- Create: `crates/core/src/tests/types_test.rs`

**Step 1: Write failing tests**

```rust
// crates/core/src/tests/types_test.rs
#[cfg(test)]
mod tests {
    use crate::types::*;
    use crate::config::*;

    #[test]
    fn line_range_valid() {
        let r = LineRange { start: 1, end: 10 };
        assert!(r.is_valid());
    }

    #[test]
    fn line_range_single_line_valid() {
        let r = LineRange { start: 5, end: 5 };
        assert!(r.is_valid());
    }

    #[test]
    fn line_range_inverted_invalid() {
        let r = LineRange { start: 10, end: 5 };
        assert!(!r.is_valid());
    }

    #[test]
    fn config_default_embedding_is_voyage() {
        let cfg = EmbeddingConfig::default();
        assert_eq!(cfg.backend, EmbeddingBackend::Voyage);
        assert_eq!(cfg.model, "voyage-code-3");
        assert_eq!(cfg.batch_size, 64);
    }

    #[test]
    fn config_default_debounce() {
        let cfg = WatcherConfig::default();
        assert_eq!(cfg.debounce_ms, 300);
    }
}
```

**Step 2: Run to verify failure**

```bash
cargo test -p ai-mem-core 2>&1 | head -20
```
Expected: compile error — `types` and `config` modules are empty.

**Step 3: Implement types**

```rust
// crates/core/src/types.rs
use serde::{Deserialize, Serialize};
use uuid::Uuid;
use chrono::{DateTime, Utc};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LineRange {
    pub start: u32,
    pub end: u32,
}

impl LineRange {
    pub fn is_valid(&self) -> bool {
        self.start <= self.end
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Repo {
    pub id: Uuid,
    pub path: String,
    pub name: String,
    pub indexed_at: Option<DateTime<Utc>>,
    pub config: Option<serde_json::Value>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Chunk {
    pub id: Uuid,
    pub repo_id: Uuid,
    pub file_path: String,
    pub range: LineRange,
    pub content: String,
    pub embedding: Option<Vec<f32>>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SearchResult {
    pub chunk: Chunk,
    pub score: f32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Symbol {
    pub name: String,
    pub kind: SymbolKind,
    pub file_path: String,
    pub range: LineRange,
    pub chunk_id: Uuid,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum SymbolKind {
    Function,
    Class,
    Module,
    Import,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum StructuralRelation {
    Callers,
    Callees,
    Imports,
    Inheritors,
}
```

**Step 4: Implement config**

```rust
// crates/core/src/config.rs
use serde::{Deserialize, Serialize};
use uuid::Uuid;

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(rename_all = "lowercase")]
pub enum EmbeddingBackend {
    Voyage,
    OpenAI,
    Local,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DatabaseConfig {
    pub dsn: String,
}

impl Default for DatabaseConfig {
    fn default() -> Self {
        Self { dsn: "postgresql://localhost/ai_mem".to_string() }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EmbeddingConfig {
    pub backend: EmbeddingBackend,
    pub api_key: Option<String>,
    pub model: String,
    pub batch_size: usize,
}

impl Default for EmbeddingConfig {
    fn default() -> Self {
        Self {
            backend: EmbeddingBackend::Voyage,
            api_key: None,
            model: "voyage-code-3".to_string(),
            batch_size: 64,
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WatcherConfig {
    pub debounce_ms: u64,
}

impl Default for WatcherConfig {
    fn default() -> Self {
        Self { debounce_ms: 300 }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RepoEntry {
    pub id: Uuid,
    pub path: String,
    pub name: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct AppConfig {
    pub database: DatabaseConfig,
    pub embeddings: EmbeddingConfig,
    pub watcher: WatcherConfig,
    #[serde(default)]
    pub repos: Vec<RepoEntry>,
}

impl AppConfig {
    pub fn config_path() -> std::path::PathBuf {
        let home = std::env::var("HOME").unwrap_or_default();
        std::path::PathBuf::from(home).join(".config/ai-mem/config.toml")
    }

    pub fn load() -> anyhow::Result<Self> {
        let path = Self::config_path();
        if !path.exists() {
            return Ok(Self::default());
        }
        let content = std::fs::read_to_string(&path)?;
        Ok(toml::from_str(&content)?)
    }

    pub fn save(&self) -> anyhow::Result<()> {
        let path = Self::config_path();
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        std::fs::write(&path, toml::to_string_pretty(self)?)?;
        Ok(())
    }
}
```

Add `toml` dependency to core:

```toml
# crates/core/Cargo.toml (add to [dependencies])
toml = { workspace = true }
serde_json = { workspace = true }
```

**Step 5: Run tests**

```bash
cargo test -p ai-mem-core
```
Expected: 5 tests pass.

**Step 6: Commit**

```bash
git add crates/core/
git commit -m "feat(core): add types and config with validation"
```

---

### Task 4: Database Migrations

**Files:**
- Create: `migrations/001_initial.sql`
- Create: `crates/core/src/db.rs`

**Step 1: Create migration**

```sql
-- migrations/001_initial.sql
-- Enable required extensions
CREATE EXTENSION IF NOT EXISTS "pgcrypto";
CREATE EXTENSION IF NOT EXISTS "vector";
CREATE EXTENSION IF NOT EXISTS "age";

-- Repos registry
CREATE TABLE IF NOT EXISTS repos (
    id          UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    path        TEXT UNIQUE NOT NULL,
    name        TEXT NOT NULL,
    indexed_at  TIMESTAMPTZ,
    config      JSONB
);

-- File chunks with full-text and vector search
CREATE TABLE IF NOT EXISTS chunks (
    id          UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    repo_id     UUID NOT NULL REFERENCES repos(id) ON DELETE CASCADE,
    file_path   TEXT NOT NULL,
    start_line  INT NOT NULL,
    end_line    INT NOT NULL CHECK (end_line >= start_line),
    content     TEXT NOT NULL CHECK (content <> ''),
    ts_vector   TSVECTOR GENERATED ALWAYS AS (to_tsvector('english', content)) STORED,
    embedding   VECTOR(1024)
);

CREATE INDEX IF NOT EXISTS chunks_ts_vector_idx ON chunks USING GIN (ts_vector);
CREATE INDEX IF NOT EXISTS chunks_embedding_idx ON chunks USING hnsw (embedding vector_cosine_ops);
CREATE INDEX IF NOT EXISTS chunks_repo_file_idx ON chunks (repo_id, file_path);

-- AGE graph for structural relationships
SELECT create_graph('code_graph');
```

**Step 2: Run migration**

```bash
export DATABASE_URL="postgresql://localhost/ai_mem"
psql $DATABASE_URL -c "CREATE DATABASE ai_mem;" 2>/dev/null || true
sqlx migrate run --source migrations
```
Expected: `Applied 001_initial.sql`

**Step 3: Implement db connection helper**

```rust
// crates/core/src/db.rs
use sqlx::{PgPool, postgres::PgPoolOptions};

pub async fn connect(dsn: &str) -> anyhow::Result<PgPool> {
    let pool = PgPoolOptions::new()
        .max_connections(10)
        .connect(dsn)
        .await?;
    Ok(pool)
}
```

Add `sqlx` to core `Cargo.toml`:

```toml
sqlx = { workspace = true }
```

Update `crates/core/src/lib.rs`:

```rust
pub mod config;
pub mod db;
pub mod types;
```

**Step 4: Verify compilation**

```bash
cargo build -p ai-mem-core
```
Expected: compiles cleanly.

**Step 5: Commit**

```bash
git add migrations/ crates/core/src/db.rs crates/core/src/lib.rs crates/core/Cargo.toml
git commit -m "feat(db): add initial schema migration and connection helper"
```

---

### Task 5: Tree-sitter Parsing

**Files:**
- Create: `crates/core/src/parser.rs`
- Tests inline in `crates/core/src/parser.rs`

Add to workspace `Cargo.toml` `[workspace.dependencies]`:

```toml
tree-sitter = "0.22"
tree-sitter-rust = "0.21"
tree-sitter-python = "0.21"
tree-sitter-javascript = "0.21"
tree-sitter-typescript = "0.21"
```

Add to `crates/core/Cargo.toml`:

```toml
tree-sitter = { workspace = true }
tree-sitter-rust = { workspace = true }
tree-sitter-python = { workspace = true }
tree-sitter-javascript = { workspace = true }
tree-sitter-typescript = { workspace = true }
```

**Step 1: Write failing tests**

```rust
// at bottom of crates/core/src/parser.rs
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
        let src = r#"
fn hello_world() {
    println!("hello");
}
"#;
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
```

**Step 2: Run to verify failure**

```bash
cargo test -p ai-mem-core parser 2>&1 | head -10
```
Expected: compile error — `parser` module not found.

**Step 3: Implement parser**

```rust
// crates/core/src/parser.rs
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

/// Chunk file content by symbol boundaries, splitting further if > max_chars
pub fn chunk_file(
    source: &str,
    symbols: &[ParsedSymbol],
    max_chars: usize,
) -> Vec<crate::types::Chunk> {
    use uuid::Uuid;
    let lines: Vec<&str> = source.lines().collect();
    let mut chunks = Vec::new();

    if symbols.is_empty() {
        // No symbols: chunk by max_chars
        let mut start = 0usize;
        while start < lines.len() {
            let mut acc = String::new();
            let mut end = start;
            while end < lines.len() && acc.len() + lines[end].len() < max_chars {
                acc.push_str(lines[end]);
                acc.push('\n');
                end += 1;
            }
            if end == start { end += 1; acc = lines[start].to_string(); } // avoid infinite loop on giant lines
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
```

Add `tree-sitter` crates to `crates/core/Cargo.toml` and `pub mod parser;` to `lib.rs`.

**Step 4: Run tests**

```bash
cargo test -p ai-mem-core parser
```
Expected: 6 tests pass.

**Step 5: Commit**

```bash
git add crates/core/src/parser.rs crates/core/src/lib.rs crates/core/Cargo.toml Cargo.toml
git commit -m "feat(parser): tree-sitter file parsing and symbol-boundary chunking"
```

---

### Task 6: Embedding Backends

**Files:**
- Create: `crates/core/src/embeddings.rs`
- Tests inline

Add to workspace dependencies:

```toml
reqwest = { version = "0.12", features = ["json", "rustls-tls"], default-features = false }
```

**Step 1: Write failing tests**

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn embedding_dimension_voyage() {
        assert_eq!(EmbeddingBackendConfig::voyage_code_3_dimension(), 1024);
    }

    #[tokio::test]
    async fn mock_backend_returns_correct_dimension() {
        let backend = MockEmbeddingBackend { dimension: 1024 };
        let results = backend.embed(&["hello world".to_string()]).await.unwrap();
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].len(), 1024);
    }
}
```

**Step 2: Run to verify failure**

```bash
cargo test -p ai-mem-core embeddings 2>&1 | head -10
```
Expected: compile error.

**Step 3: Implement embeddings**

```rust
// crates/core/src/embeddings.rs
use anyhow::Result;

pub trait EmbeddingBackend: Send + Sync {
    fn embed<'a>(
        &'a self,
        texts: &'a [String],
    ) -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<Vec<Vec<f32>>>> + Send + 'a>>;
}

pub struct EmbeddingBackendConfig;

impl EmbeddingBackendConfig {
    pub fn voyage_code_3_dimension() -> usize { 1024 }
}

// ── Voyage AI ─────────────────────────────────────────────────────────────────

pub struct VoyageBackend {
    pub api_key: String,
    pub model: String,
    client: reqwest::Client,
}

impl VoyageBackend {
    pub fn new(api_key: String, model: String) -> Self {
        Self { api_key, model, client: reqwest::Client::new() }
    }
}

impl EmbeddingBackend for VoyageBackend {
    fn embed<'a>(
        &'a self,
        texts: &'a [String],
    ) -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<Vec<Vec<f32>>>> + Send + 'a>> {
        Box::pin(async move {
            let body = serde_json::json!({
                "input": texts,
                "model": self.model,
                "input_type": "document"
            });
            let resp: serde_json::Value = self.client
                .post("https://api.voyageai.com/v1/embeddings")
                .bearer_auth(&self.api_key)
                .json(&body)
                .send()
                .await?
                .error_for_status()?
                .json()
                .await?;
            let embeddings = resp["data"]
                .as_array()
                .ok_or_else(|| anyhow::anyhow!("unexpected response shape"))?
                .iter()
                .map(|item| {
                    item["embedding"]
                        .as_array()
                        .unwrap_or(&vec![])
                        .iter()
                        .map(|v| v.as_f64().unwrap_or(0.0) as f32)
                        .collect()
                })
                .collect();
            Ok(embeddings)
        })
    }
}

// ── OpenAI ────────────────────────────────────────────────────────────────────

pub struct OpenAIBackend {
    pub api_key: String,
    pub model: String,
    client: reqwest::Client,
}

impl OpenAIBackend {
    pub fn new(api_key: String, model: String) -> Self {
        Self { api_key, model, client: reqwest::Client::new() }
    }
}

impl EmbeddingBackend for OpenAIBackend {
    fn embed<'a>(
        &'a self,
        texts: &'a [String],
    ) -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<Vec<Vec<f32>>>> + Send + 'a>> {
        Box::pin(async move {
            let body = serde_json::json!({
                "input": texts,
                "model": self.model
            });
            let resp: serde_json::Value = self.client
                .post("https://api.openai.com/v1/embeddings")
                .bearer_auth(&self.api_key)
                .json(&body)
                .send()
                .await?
                .error_for_status()?
                .json()
                .await?;
            let embeddings = resp["data"]
                .as_array()
                .ok_or_else(|| anyhow::anyhow!("unexpected response shape"))?
                .iter()
                .map(|item| {
                    item["embedding"]
                        .as_array()
                        .unwrap_or(&vec![])
                        .iter()
                        .map(|v| v.as_f64().unwrap_or(0.0) as f32)
                        .collect()
                })
                .collect();
            Ok(embeddings)
        })
    }
}

// ── Mock (for tests) ──────────────────────────────────────────────────────────

pub struct MockEmbeddingBackend {
    pub dimension: usize,
}

impl EmbeddingBackend for MockEmbeddingBackend {
    fn embed<'a>(
        &'a self,
        texts: &'a [String],
    ) -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<Vec<Vec<f32>>>> + Send + 'a>> {
        let dim = self.dimension;
        let n = texts.len();
        Box::pin(async move {
            Ok((0..n).map(|_| vec![0.0f32; dim]).collect())
        })
    }
}

// ── Factory ───────────────────────────────────────────────────────────────────

pub fn make_backend(cfg: &crate::config::EmbeddingConfig) -> Box<dyn EmbeddingBackend> {
    use crate::config::EmbeddingBackend as B;
    match cfg.backend {
        B::Voyage => Box::new(VoyageBackend::new(
            cfg.api_key.clone().unwrap_or_default(),
            cfg.model.clone(),
        )),
        B::OpenAI => Box::new(OpenAIBackend::new(
            cfg.api_key.clone().unwrap_or_default(),
            cfg.model.clone(),
        )),
        B::Local => Box::new(MockEmbeddingBackend { dimension: 768 }),
    }
}
```

**Step 4: Run tests**

```bash
cargo test -p ai-mem-core embeddings
```
Expected: 2 tests pass.

**Step 5: Commit**

```bash
git add crates/core/src/embeddings.rs crates/core/src/lib.rs crates/core/Cargo.toml Cargo.toml
git commit -m "feat(embeddings): configurable backend with Voyage, OpenAI, and mock implementations"
```

---

### Task 7: Repo Store (DB operations)

**Files:**
- Create: `crates/core/src/store.rs`
- Tests inline (require `TEST_DATABASE_URL` env var)

**Step 1: Write failing tests**

```rust
// in store.rs #[cfg(test)] block
#[tokio::test]
async fn repo_register_and_fetch() {
    let pool = test_pool().await;
    let repo = register_repo(&pool, "/tmp/test-repo", "test-repo").await.unwrap();
    assert_eq!(repo.path, "/tmp/test-repo");

    let fetched = get_repo_by_path(&pool, "/tmp/test-repo").await.unwrap();
    assert!(fetched.is_some());
    assert_eq!(fetched.unwrap().name, "test-repo");

    delete_repo(&pool, repo.id).await.unwrap();
}

#[tokio::test]
async fn duplicate_path_errors() {
    let pool = test_pool().await;
    register_repo(&pool, "/tmp/dup-repo", "dup").await.unwrap();
    let result = register_repo(&pool, "/tmp/dup-repo", "dup2").await;
    assert!(result.is_err());
    // cleanup
    let repo = get_repo_by_path(&pool, "/tmp/dup-repo").await.unwrap().unwrap();
    delete_repo(&pool, repo.id).await.unwrap();
}
```

**Step 2: Run to verify failure**

```bash
TEST_DATABASE_URL="postgresql://localhost/ai_mem" cargo test -p ai-mem-core store 2>&1 | head -10
```
Expected: compile error.

**Step 3: Implement store**

```rust
// crates/core/src/store.rs
use crate::types::{Repo, Chunk, SearchResult};
use sqlx::PgPool;
use uuid::Uuid;
use anyhow::Result;

pub async fn register_repo(pool: &PgPool, path: &str, name: &str) -> Result<Repo> {
    let repo = sqlx::query_as!(
        Repo,
        r#"
        INSERT INTO repos (id, path, name)
        VALUES (gen_random_uuid(), $1, $2)
        RETURNING id, path, name, indexed_at, config
        "#,
        path, name
    )
    .fetch_one(pool)
    .await?;
    Ok(repo)
}

pub async fn get_repo_by_path(pool: &PgPool, path: &str) -> Result<Option<Repo>> {
    let repo = sqlx::query_as!(
        Repo,
        "SELECT id, path, name, indexed_at, config FROM repos WHERE path = $1",
        path
    )
    .fetch_optional(pool)
    .await?;
    Ok(repo)
}

pub async fn list_repos(pool: &PgPool) -> Result<Vec<Repo>> {
    let repos = sqlx::query_as!(
        Repo,
        "SELECT id, path, name, indexed_at, config FROM repos ORDER BY name"
    )
    .fetch_all(pool)
    .await?;
    Ok(repos)
}

pub async fn delete_repo(pool: &PgPool, repo_id: Uuid) -> Result<()> {
    sqlx::query!("DELETE FROM repos WHERE id = $1", repo_id)
        .execute(pool)
        .await?;
    Ok(())
}

pub async fn mark_indexed(pool: &PgPool, repo_id: Uuid) -> Result<()> {
    sqlx::query!(
        "UPDATE repos SET indexed_at = NOW() WHERE id = $1",
        repo_id
    )
    .execute(pool)
    .await?;
    Ok(())
}

pub async fn upsert_chunk(pool: &PgPool, chunk: &Chunk) -> Result<Uuid> {
    let id = sqlx::query_scalar!(
        r#"
        INSERT INTO chunks (id, repo_id, file_path, start_line, end_line, content, embedding)
        VALUES ($1, $2, $3, $4, $5, $6, $7)
        ON CONFLICT (id) DO UPDATE
            SET content = EXCLUDED.content,
                embedding = EXCLUDED.embedding
        RETURNING id
        "#,
        chunk.id,
        chunk.repo_id,
        chunk.file_path,
        chunk.range.start as i32,
        chunk.range.end as i32,
        chunk.content,
        chunk.embedding.as_deref() as _,
    )
    .fetch_one(pool)
    .await?;
    Ok(id)
}

pub async fn delete_file_chunks(pool: &PgPool, repo_id: Uuid, file_path: &str) -> Result<()> {
    sqlx::query!(
        "DELETE FROM chunks WHERE repo_id = $1 AND file_path = $2",
        repo_id, file_path
    )
    .execute(pool)
    .await?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    async fn test_pool() -> PgPool {
        let url = std::env::var("TEST_DATABASE_URL")
            .unwrap_or_else(|_| "postgresql://localhost/ai_mem".to_string());
        crate::db::connect(&url).await.unwrap()
    }

    // tests go here (see Step 1 above)
}
```

**Step 4: Run tests**

```bash
TEST_DATABASE_URL="postgresql://localhost/ai_mem" cargo test -p ai-mem-core store
```
Expected: 2 tests pass.

**Step 5: Commit**

```bash
git add crates/core/src/store.rs crates/core/src/lib.rs
git commit -m "feat(store): repo and chunk database operations"
```

---

### Task 8: Indexing Pipeline

**Files:**
- Create: `crates/indexer/src/pipeline.rs`
- Modify: `crates/indexer/src/main.rs`

Add to `crates/indexer/Cargo.toml`:

```toml
ai-mem-core = { path = "../core" }
sqlx = { workspace = true }
ignore = "0.4"
tokio = { workspace = true }
```

**Step 1: Write failing test**

```rust
// crates/indexer/src/pipeline.rs #[cfg(test)]
#[tokio::test]
async fn index_single_rust_file() {
    let dir = tempfile::tempdir().unwrap();
    let file = dir.path().join("foo.rs");
    std::fs::write(&file, "fn hello() { println!(\"hi\"); }\n").unwrap();

    let backend = Arc::new(ai_mem_core::embeddings::MockEmbeddingBackend { dimension: 1024 });
    let pool = test_pool().await;
    let repo_id = uuid::Uuid::new_v4();

    index_file(&pool, repo_id, &file, backend.as_ref(), 512).await.unwrap();

    let chunks: Vec<_> = sqlx::query!(
        "SELECT id FROM chunks WHERE repo_id = $1 AND file_path = $2",
        repo_id, file.to_str().unwrap()
    )
    .fetch_all(&pool)
    .await
    .unwrap();

    assert!(!chunks.is_empty());
}
```

**Step 2: Run to verify failure**

```bash
cargo test -p ai-mem-index pipeline 2>&1 | head -10
```
Expected: compile error.

**Step 3: Implement pipeline**

```rust
// crates/indexer/src/pipeline.rs
use ai_mem_core::{
    embeddings::EmbeddingBackend,
    parser::{detect_language, parse_file, chunk_file},
    store::{upsert_chunk, delete_file_chunks},
    types::Chunk,
};
use sqlx::PgPool;
use uuid::Uuid;
use anyhow::Result;
use std::sync::Arc;
use std::path::Path;

pub async fn index_file(
    pool: &PgPool,
    repo_id: Uuid,
    path: &Path,
    embedder: &dyn EmbeddingBackend,
    max_chars: usize,
) -> Result<()> {
    let file_path = path.to_string_lossy().to_string();
    let source = std::fs::read_to_string(path)?;

    let language = detect_language(&file_path);
    let symbols = match language {
        Some(lang) => parse_file(&source, lang).unwrap_or_default(),
        None => vec![],
    };

    let mut chunks = chunk_file(&source, &symbols, max_chars);
    for c in &mut chunks {
        c.repo_id = repo_id;
        c.file_path = file_path.clone();
    }

    // Generate embeddings in one batch
    let texts: Vec<String> = chunks.iter().map(|c| c.content.clone()).collect();
    let embeddings = embedder.embed(&texts).await?;
    for (c, emb) in chunks.iter_mut().zip(embeddings) {
        c.embedding = Some(emb);
    }

    // Delete old chunks for this file, then upsert new ones
    delete_file_chunks(pool, repo_id, &file_path).await?;
    for chunk in &chunks {
        upsert_chunk(pool, chunk).await?;
    }

    Ok(())
}

pub async fn index_repo(
    pool: &PgPool,
    repo_id: Uuid,
    repo_path: &Path,
    embedder: Arc<dyn EmbeddingBackend>,
    batch_size: usize,
) -> Result<()> {
    use ignore::WalkBuilder;

    let walker = WalkBuilder::new(repo_path)
        .hidden(false)
        .git_ignore(true)
        .build();

    let mut files: Vec<std::path::PathBuf> = vec![];
    for entry in walker.flatten() {
        if entry.file_type().map(|t| t.is_file()).unwrap_or(false) {
            files.push(entry.path().to_owned());
        }
    }

    // Process in batches
    for batch in files.chunks(batch_size) {
        for file in batch {
            if let Err(e) = index_file(pool, repo_id, file, embedder.as_ref(), 4096).await {
                tracing::warn!("skipping {}: {}", file.display(), e);
            }
        }
    }

    ai_mem_core::store::mark_indexed(pool, repo_id).await?;
    Ok(())
}
```

**Step 4: Run tests**

```bash
TEST_DATABASE_URL="postgresql://localhost/ai_mem" cargo test -p ai-mem-index pipeline
```
Expected: test passes.

**Step 5: Commit**

```bash
git add crates/indexer/
git commit -m "feat(indexer): full file and repo indexing pipeline"
```

---

### Task 9: File Watcher

**Files:**
- Create: `crates/indexer/src/watcher.rs`
- Modify: `crates/indexer/src/main.rs`

Add to `crates/indexer/Cargo.toml`:

```toml
notify = "6"
tokio = { workspace = true }
```

**Step 1: Implement watcher**

No unit test for the watcher itself (it wraps OS inotify). Write it and verify it compiles.

```rust
// crates/indexer/src/watcher.rs
use notify::{Watcher, RecursiveMode, Event, EventKind, Config as NotifyConfig};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Duration;
use tokio::sync::mpsc;
use sqlx::PgPool;
use uuid::Uuid;
use anyhow::Result;
use ai_mem_core::embeddings::EmbeddingBackend;
use crate::pipeline::index_file;

pub async fn watch_repo(
    pool: PgPool,
    repo_id: Uuid,
    repo_path: PathBuf,
    embedder: Arc<dyn EmbeddingBackend>,
    debounce_ms: u64,
) -> Result<()> {
    let (tx, mut rx) = mpsc::channel::<PathBuf>(256);

    let mut watcher = notify::recommended_watcher(move |res: notify::Result<Event>| {
        if let Ok(event) = res {
            match event.kind {
                EventKind::Create(_) | EventKind::Modify(_) | EventKind::Remove(_) => {
                    for path in event.paths {
                        let _ = tx.blocking_send(path);
                    }
                }
                _ => {}
            }
        }
    })?;

    watcher.watch(&repo_path, RecursiveMode::Recursive)?;
    tracing::info!("watching {} for changes", repo_path.display());

    let debounce = Duration::from_millis(debounce_ms);

    loop {
        // Collect debounced batch
        let Some(first) = rx.recv().await else { break };
        let mut batch = vec![first];
        let _ = tokio::time::timeout(debounce, async {
            while let Some(p) = rx.recv().await {
                batch.push(p);
            }
        }).await;

        // Deduplicate paths
        batch.sort();
        batch.dedup();

        for path in batch {
            if path.exists() {
                if let Err(e) = index_file(&pool, repo_id, &path, embedder.as_ref(), 4096).await {
                    tracing::warn!("incremental index error for {}: {}", path.display(), e);
                }
            } else {
                // File deleted — chunks already removed by index_file's delete step
                if let Err(e) = ai_mem_core::store::delete_file_chunks(
                    &pool, repo_id,
                    path.to_string_lossy().as_ref()
                ).await {
                    tracing::warn!("failed to delete chunks for {}: {}", path.display(), e);
                }
            }
        }
    }

    Ok(())
}
```

**Step 2: Wire into main**

```rust
// crates/indexer/src/main.rs
mod pipeline;
mod watcher;

use ai_mem_core::{config::AppConfig, db, embeddings::make_backend};
use std::sync::Arc;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    tracing_subscriber::fmt::init();

    let cfg = AppConfig::load()?;
    let pool = db::connect(&cfg.database.dsn).await?;
    let embedder = Arc::from(make_backend(&cfg.embeddings));

    let mut handles = vec![];

    for repo_entry in &cfg.repos {
        let path = std::path::PathBuf::from(&repo_entry.path);
        let repo_row = ai_mem_core::store::get_repo_by_path(&pool, &repo_entry.path).await?;
        let repo = match repo_row {
            Some(r) => r,
            None => ai_mem_core::store::register_repo(&pool, &repo_entry.path, &repo_entry.name).await?,
        };

        if repo.indexed_at.is_none() {
            tracing::info!("full reindex: {}", repo_entry.path);
            pipeline::index_repo(&pool, repo.id, &path, embedder.clone(), cfg.embeddings.batch_size).await?;
        }

        let pool2 = pool.clone();
        let embedder2 = embedder.clone();
        let path2 = path.clone();
        let id = repo.id;
        let debounce = cfg.watcher.debounce_ms;

        handles.push(tokio::spawn(async move {
            if let Err(e) = watcher::watch_repo(pool2, id, path2, embedder2, debounce).await {
                tracing::error!("watcher error: {}", e);
            }
        }));
    }

    futures::future::join_all(handles).await;
    Ok(())
}
```

Add `futures = "0.3"` to workspace and indexer dependencies.

**Step 3: Verify compilation**

```bash
cargo build -p ai-mem-index
```
Expected: clean build.

**Step 4: Commit**

```bash
git add crates/indexer/
git commit -m "feat(indexer): file watcher with debounced incremental updates"
```

---

### Task 10: AGE Graph — Structural Relationships

**Files:**
- Create: `crates/core/src/graph.rs`

**Step 1: Write failing test**

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn insert_and_query_calls_edge() {
        let pool = test_pool().await;
        let caller_id = Uuid::new_v4();
        let callee_id = Uuid::new_v4();

        upsert_symbol_node(&pool, caller_id, "foo", "Function", "/a.rs", 1, 5).await.unwrap();
        upsert_symbol_node(&pool, callee_id, "bar", "Function", "/a.rs", 7, 12).await.unwrap();
        upsert_edge(&pool, caller_id, callee_id, "CALLS").await.unwrap();

        let callers = query_related(&pool, "bar", "callers").await.unwrap();
        assert!(callers.iter().any(|s| s.name == "foo"));
    }
}
```

**Step 2: Implement graph**

```rust
// crates/core/src/graph.rs
use sqlx::PgPool;
use uuid::Uuid;
use anyhow::Result;
use crate::types::{Symbol, SymbolKind, LineRange};

pub async fn upsert_symbol_node(
    pool: &PgPool,
    chunk_id: Uuid,
    name: &str,
    kind: &str,
    file_path: &str,
    start_line: u32,
    end_line: u32,
) -> Result<()> {
    // AGE uses SQL functions for Cypher
    let cypher = format!(
        r#"SELECT * FROM cypher('code_graph', $$
            MERGE (n:{kind} {{chunk_id: '{chunk_id}'}})
            SET n.name = '{name}',
                n.file_path = '{file_path}',
                n.start_line = {start_line},
                n.end_line = {end_line}
        $$) AS (result agtype)"#,
        kind = kind,
        chunk_id = chunk_id,
        name = name.replace('\'', "\\'"),
        file_path = file_path.replace('\'', "\\'"),
        start_line = start_line,
        end_line = end_line,
    );
    sqlx::query(&cypher).execute(pool).await?;
    Ok(())
}

pub async fn upsert_edge(
    pool: &PgPool,
    from_chunk_id: Uuid,
    to_chunk_id: Uuid,
    relation: &str,
) -> Result<()> {
    let cypher = format!(
        r#"SELECT * FROM cypher('code_graph', $$
            MATCH (a {{chunk_id: '{from}'}}), (b {{chunk_id: '{to}'}})
            MERGE (a)-[:{rel}]->(b)
        $$) AS (result agtype)"#,
        from = from_chunk_id,
        to = to_chunk_id,
        rel = relation,
    );
    sqlx::query(&cypher).execute(pool).await?;
    Ok(())
}

pub async fn query_related(
    pool: &PgPool,
    symbol_name: &str,
    relation: &str,
) -> Result<Vec<Symbol>> {
    let (pattern, dir) = match relation {
        "callers"    => ("CALLS", "incoming"),
        "callees"    => ("CALLS", "outgoing"),
        "imports"    => ("IMPORTS", "outgoing"),
        "inheritors" => ("INHERITS_FROM", "incoming"),
        _            => return Err(anyhow::anyhow!("unknown relation: {}", relation)),
    };

    let cypher = if dir == "incoming" {
        format!(
            r#"SELECT * FROM cypher('code_graph', $$
                MATCH (a)-[:{pattern}]->(b {{name: '{name}'}})
                RETURN a.chunk_id, a.name, a.file_path, a.start_line, a.end_line, labels(a)[0]
            $$) AS (chunk_id agtype, name agtype, file_path agtype, start_line agtype, end_line agtype, kind agtype)"#,
            pattern = pattern, name = symbol_name.replace('\'', "\\'")
        )
    } else {
        format!(
            r#"SELECT * FROM cypher('code_graph', $$
                MATCH (a {{name: '{name}'}})-[:{pattern}]->(b)
                RETURN b.chunk_id, b.name, b.file_path, b.start_line, b.end_line, labels(b)[0]
            $$) AS (chunk_id agtype, name agtype, file_path agtype, start_line agtype, end_line agtype, kind agtype)"#,
            pattern = pattern, name = symbol_name.replace('\'', "\\'")
        )
    };

    // Parse AGE agtype results — returned as JSON strings
    let rows = sqlx::query(&cypher).fetch_all(pool).await?;
    let mut symbols = vec![];
    for row in rows {
        use sqlx::Row;
        let name: String = row.try_get::<serde_json::Value, _>("name")
            .ok().and_then(|v| v.as_str().map(String::from))
            .unwrap_or_default();
        let file_path: String = row.try_get::<serde_json::Value, _>("file_path")
            .ok().and_then(|v| v.as_str().map(String::from))
            .unwrap_or_default();
        let start_line: u32 = row.try_get::<serde_json::Value, _>("start_line")
            .ok().and_then(|v| v.as_u64()).unwrap_or(0) as u32;
        let end_line: u32 = row.try_get::<serde_json::Value, _>("end_line")
            .ok().and_then(|v| v.as_u64()).unwrap_or(0) as u32;
        let chunk_id: Uuid = row.try_get::<serde_json::Value, _>("chunk_id")
            .ok().and_then(|v| v.as_str().and_then(|s| s.parse().ok()))
            .unwrap_or_else(Uuid::nil);

        symbols.push(Symbol {
            name,
            kind: SymbolKind::Function,
            file_path,
            range: LineRange { start: start_line, end: end_line },
            chunk_id,
        });
    }
    Ok(symbols)
}
```

**Step 3: Run tests**

```bash
TEST_DATABASE_URL="postgresql://localhost/ai_mem" cargo test -p ai-mem-core graph
```
Expected: test passes.

**Step 4: Commit**

```bash
git add crates/core/src/graph.rs crates/core/src/lib.rs
git commit -m "feat(graph): AGE graph nodes and structural relationship queries"
```

---

### Task 11: Search Queries

**Files:**
- Create: `crates/core/src/search.rs`
- Tests inline

**Step 1: Write failing tests**

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rrf_merge_combines_results() {
        let r1 = SearchResult { chunk: make_chunk("a"), score: 0.9 };
        let r2 = SearchResult { chunk: make_chunk("b"), score: 0.8 };
        let r3 = SearchResult { chunk: make_chunk("a"), score: 0.7 }; // duplicate

        let semantic = vec![r1.clone(), r2.clone()];
        let fulltext = vec![r3, r2.clone()];
        let merged = rrf_merge(semantic, fulltext, 2);

        assert_eq!(merged.len(), 2);
        // "a" should rank first (appears in both lists)
        assert_eq!(merged[0].chunk.id, r1.chunk.id);
    }
}
```

**Step 2: Implement search**

```rust
// crates/core/src/search.rs
use crate::types::{Chunk, SearchResult, LineRange};
use sqlx::PgPool;
use uuid::Uuid;
use anyhow::Result;

pub async fn fulltext_search(
    pool: &PgPool,
    query: &str,
    repo_id: Option<Uuid>,
    limit: i64,
) -> Result<Vec<SearchResult>> {
    let rows = sqlx::query!(
        r#"
        SELECT id, repo_id, file_path, start_line, end_line, content,
               ts_rank(ts_vector, plainto_tsquery('english', $1)) AS score
        FROM chunks
        WHERE ts_vector @@ plainto_tsquery('english', $1)
          AND ($2::uuid IS NULL OR repo_id = $2)
        ORDER BY score DESC
        LIMIT $3
        "#,
        query, repo_id, limit
    )
    .fetch_all(pool)
    .await?;

    Ok(rows.into_iter().map(|r| SearchResult {
        score: r.score.unwrap_or(0.0) as f32,
        chunk: Chunk {
            id: r.id,
            repo_id: r.repo_id,
            file_path: r.file_path,
            range: LineRange { start: r.start_line as u32, end: r.end_line as u32 },
            content: r.content,
            embedding: None,
        },
    }).collect())
}

pub async fn semantic_search(
    pool: &PgPool,
    query_embedding: &[f32],
    repo_id: Option<Uuid>,
    limit: i64,
) -> Result<Vec<SearchResult>> {
    // pgvector cosine distance: 1 - cosine_similarity
    let rows = sqlx::query!(
        r#"
        SELECT id, repo_id, file_path, start_line, end_line, content,
               1 - (embedding <=> $1::vector) AS score
        FROM chunks
        WHERE embedding IS NOT NULL
          AND ($2::uuid IS NULL OR repo_id = $2)
        ORDER BY embedding <=> $1::vector
        LIMIT $3
        "#,
        query_embedding as _, repo_id, limit
    )
    .fetch_all(pool)
    .await?;

    Ok(rows.into_iter().map(|r| SearchResult {
        score: r.score.unwrap_or(0.0) as f32,
        chunk: Chunk {
            id: r.id,
            repo_id: r.repo_id,
            file_path: r.file_path,
            range: LineRange { start: r.start_line as u32, end: r.end_line as u32 },
            content: r.content,
            embedding: None,
        },
    }).collect())
}

/// Reciprocal Rank Fusion: merge two ranked result lists
pub fn rrf_merge(
    list_a: Vec<SearchResult>,
    list_b: Vec<SearchResult>,
    limit: usize,
) -> Vec<SearchResult> {
    use std::collections::HashMap;
    const K: f32 = 60.0;

    let mut scores: HashMap<Uuid, (f32, SearchResult)> = HashMap::new();

    for (rank, result) in list_a.into_iter().enumerate() {
        let rrf = 1.0 / (K + rank as f32 + 1.0);
        let id = result.chunk.id;
        scores.entry(id).and_modify(|e| e.0 += rrf).or_insert((rrf, result));
    }
    for (rank, result) in list_b.into_iter().enumerate() {
        let rrf = 1.0 / (K + rank as f32 + 1.0);
        let id = result.chunk.id;
        scores.entry(id).and_modify(|e| e.0 += rrf).or_insert((rrf, result));
    }

    let mut results: Vec<(f32, SearchResult)> = scores.into_values().collect();
    results.sort_by(|a, b| b.0.partial_cmp(&a.0).unwrap_or(std::cmp::Ordering::Equal));
    results.truncate(limit);
    results.into_iter().map(|(score, mut r)| { r.score = score; r }).collect()
}
```

**Step 3: Run tests**

```bash
cargo test -p ai-mem-core search
```
Expected: test passes.

**Step 4: Commit**

```bash
git add crates/core/src/search.rs crates/core/src/lib.rs
git commit -m "feat(search): fulltext, semantic, and RRF hybrid search queries"
```

---

### Task 12: MCP Server

**Files:**
- Modify: `crates/mcp/src/main.rs`
- Create: `crates/mcp/src/tools.rs`

Add to `crates/mcp/Cargo.toml`:

```toml
rmcp = { version = "0.1", features = ["server", "transport-io"] }
ai-mem-core = { path = "../core" }
sqlx = { workspace = true }
serde = { workspace = true }
serde_json = { workspace = true }
```

**Step 1: Implement tools**

```rust
// crates/mcp/src/tools.rs
use ai_mem_core::{search, graph, store, embeddings::EmbeddingBackend, types::StructuralRelation};
use sqlx::PgPool;
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use uuid::Uuid;

pub struct SearchContext {
    pub pool: PgPool,
    pub embedder: Arc<dyn EmbeddingBackend>,
}

#[derive(Deserialize)]
pub struct HybridSearchParams {
    pub query: String,
    pub repo: Option<String>,
    pub limit: Option<i64>,
}

#[derive(Serialize)]
pub struct SearchResponse {
    pub results: Vec<SearchResultItem>,
}

#[derive(Serialize)]
pub struct SearchResultItem {
    pub file_path: String,
    pub start_line: u32,
    pub end_line: u32,
    pub score: f32,
    pub content: String,
}

impl From<ai_mem_core::types::SearchResult> for SearchResultItem {
    fn from(r: ai_mem_core::types::SearchResult) -> Self {
        Self {
            file_path: r.chunk.file_path,
            start_line: r.chunk.range.start,
            end_line: r.chunk.range.end,
            score: r.score,
            content: r.chunk.content,
        }
    }
}

pub async fn handle_search_hybrid(
    ctx: &SearchContext,
    params: HybridSearchParams,
) -> anyhow::Result<SearchResponse> {
    let limit = params.limit.unwrap_or(10);
    let repo_id = resolve_repo_id(&ctx.pool, params.repo.as_deref()).await?;

    let embedding = ctx.embedder.embed(&[params.query.clone()]).await?;
    let query_vec = embedding.into_iter().next().unwrap_or_default();

    let semantic = search::semantic_search(&ctx.pool, &query_vec, repo_id, limit * 2).await?;
    let fulltext = search::fulltext_search(&ctx.pool, &params.query, repo_id, limit * 2).await?;
    let merged = search::rrf_merge(semantic, fulltext, limit as usize);

    Ok(SearchResponse { results: merged.into_iter().map(Into::into).collect() })
}

pub async fn handle_search_fulltext(
    ctx: &SearchContext,
    params: HybridSearchParams,
) -> anyhow::Result<SearchResponse> {
    let limit = params.limit.unwrap_or(10);
    let repo_id = resolve_repo_id(&ctx.pool, params.repo.as_deref()).await?;
    let results = search::fulltext_search(&ctx.pool, &params.query, repo_id, limit).await?;
    Ok(SearchResponse { results: results.into_iter().map(Into::into).collect() })
}

pub async fn handle_search_semantic(
    ctx: &SearchContext,
    params: HybridSearchParams,
) -> anyhow::Result<SearchResponse> {
    let limit = params.limit.unwrap_or(10);
    let repo_id = resolve_repo_id(&ctx.pool, params.repo.as_deref()).await?;
    let embedding = ctx.embedder.embed(&[params.query.clone()]).await?;
    let query_vec = embedding.into_iter().next().unwrap_or_default();
    let results = search::semantic_search(&ctx.pool, &query_vec, repo_id, limit).await?;
    Ok(SearchResponse { results: results.into_iter().map(Into::into).collect() })
}

#[derive(Deserialize)]
pub struct StructuralParams {
    pub symbol: String,
    pub relation: String,
    pub repo: Option<String>,
}

pub async fn handle_search_structural(
    ctx: &SearchContext,
    params: StructuralParams,
) -> anyhow::Result<serde_json::Value> {
    let symbols = graph::query_related(&ctx.pool, &params.symbol, &params.relation).await?;
    Ok(serde_json::json!({ "symbols": symbols }))
}

async fn resolve_repo_id(pool: &PgPool, name_or_path: Option<&str>) -> anyhow::Result<Option<Uuid>> {
    let Some(key) = name_or_path else { return Ok(None) };
    let repo = store::get_repo_by_path(pool, key).await?;
    Ok(repo.map(|r| r.id))
}
```

**Step 2: Implement MCP server main**

```rust
// crates/mcp/src/main.rs
mod tools;

use ai_mem_core::{config::AppConfig, db, embeddings::make_backend};
use rmcp::{ServerHandler, Tool, ToolResult, Error as McpError};
use std::sync::Arc;
use tools::SearchContext;

struct AiMemServer {
    ctx: Arc<SearchContext>,
}

#[rmcp::tool(name = "search_hybrid")]
async fn search_hybrid(
    server: &AiMemServer,
    #[tool(param)] query: String,
    #[tool(param)] repo: Option<String>,
    #[tool(param)] limit: Option<i64>,
) -> ToolResult {
    let result = tools::handle_search_hybrid(
        &server.ctx,
        tools::HybridSearchParams { query, repo, limit },
    ).await.map_err(|e| McpError::internal_error(e.to_string(), None))?;
    Ok(serde_json::to_value(result)?)
}

#[rmcp::tool(name = "search_fulltext")]
async fn search_fulltext(
    server: &AiMemServer,
    #[tool(param)] query: String,
    #[tool(param)] repo: Option<String>,
    #[tool(param)] limit: Option<i64>,
) -> ToolResult {
    let result = tools::handle_search_fulltext(
        &server.ctx,
        tools::HybridSearchParams { query, repo, limit },
    ).await.map_err(|e| McpError::internal_error(e.to_string(), None))?;
    Ok(serde_json::to_value(result)?)
}

#[rmcp::tool(name = "search_semantic")]
async fn search_semantic(
    server: &AiMemServer,
    #[tool(param)] query: String,
    #[tool(param)] repo: Option<String>,
    #[tool(param)] limit: Option<i64>,
) -> ToolResult {
    let result = tools::handle_search_semantic(
        &server.ctx,
        tools::HybridSearchParams { query, repo, limit },
    ).await.map_err(|e| McpError::internal_error(e.to_string(), None))?;
    Ok(serde_json::to_value(result)?)
}

#[rmcp::tool(name = "search_structural")]
async fn search_structural(
    server: &AiMemServer,
    #[tool(param)] symbol: String,
    #[tool(param)] relation: String,
    #[tool(param)] repo: Option<String>,
) -> ToolResult {
    let result = tools::handle_search_structural(
        &server.ctx,
        tools::StructuralParams { symbol, relation, repo },
    ).await.map_err(|e| McpError::internal_error(e.to_string(), None))?;
    Ok(result)
}

impl ServerHandler for AiMemServer {
    fn get_info(&self) -> rmcp::ServerInfo {
        rmcp::ServerInfo {
            name: "ai-mem".to_string(),
            version: env!("CARGO_PKG_VERSION").to_string(),
            ..Default::default()
        }
    }
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    tracing_subscriber::fmt::init();

    let cfg = AppConfig::load()?;
    let pool = db::connect(&cfg.database.dsn).await?;
    let embedder = Arc::from(make_backend(&cfg.embeddings));

    let ctx = Arc::new(SearchContext { pool, embedder });
    let server = AiMemServer { ctx };

    rmcp::serve_stdio(server).await?;
    Ok(())
}
```

**Step 3: Verify compilation**

```bash
cargo build -p ai-mem-mcp
```
Expected: clean build.

**Step 4: Commit**

```bash
git add crates/mcp/
git commit -m "feat(mcp): MCP server with hybrid, fulltext, semantic, and structural search tools"
```

---

### Task 13: CLI

**Files:**
- Modify: `crates/cli/src/main.rs`

**Step 1: Implement CLI**

```rust
// crates/cli/src/main.rs
use clap::{Parser, Subcommand};
use ai_mem_core::{config::AppConfig, db, store};
use uuid::Uuid;

#[derive(Parser)]
#[command(name = "ai-mem", about = "ai-mem repository index manager")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Register a repository and trigger indexing
    Register {
        path: String,
        #[arg(long)]
        name: Option<String>,
    },
    /// Unregister a repository and delete its index
    Unregister { path: String },
    /// List registered repositories
    List,
    /// Force full reindex of a repository
    Reindex {
        #[arg(conflicts_with = "all")]
        path: Option<String>,
        #[arg(long)]
        all: bool,
    },
    /// Show indexer daemon status
    Status,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let cli = Cli::parse();
    let mut cfg = AppConfig::load()?;
    let pool = db::connect(&cfg.database.dsn).await?;

    match cli.command {
        Commands::Register { path, name } => {
            let name = name.unwrap_or_else(|| {
                std::path::Path::new(&path)
                    .file_name()
                    .unwrap_or_default()
                    .to_string_lossy()
                    .to_string()
            });
            let repo = store::register_repo(&pool, &path, &name).await?;
            cfg.repos.push(ai_mem_core::config::RepoEntry {
                id: repo.id,
                path: path.clone(),
                name: name.clone(),
            });
            cfg.save()?;
            println!("Registered: {} ({})", name, path);
        }

        Commands::Unregister { path } => {
            if let Some(repo) = store::get_repo_by_path(&pool, &path).await? {
                store::delete_repo(&pool, repo.id).await?;
                cfg.repos.retain(|r| r.path != path);
                cfg.save()?;
                println!("Unregistered: {}", path);
            } else {
                println!("Not found: {}", path);
            }
        }

        Commands::List => {
            let repos = store::list_repos(&pool).await?;
            if repos.is_empty() {
                println!("No repositories registered.");
            } else {
                for repo in repos {
                    let status = repo.indexed_at
                        .map(|t| format!("indexed at {}", t.format("%Y-%m-%d %H:%M")))
                        .unwrap_or_else(|| "never indexed".to_string());
                    println!("{:20}  {}  [{}]", repo.name, repo.path, status);
                }
            }
        }

        Commands::Reindex { path, all } => {
            if all {
                sqlx::query!("UPDATE repos SET indexed_at = NULL")
                    .execute(&pool).await?;
                println!("Marked all repos for reindex. Restart ai-mem-index to reindex.");
            } else if let Some(p) = path {
                sqlx::query!("UPDATE repos SET indexed_at = NULL WHERE path = $1", p)
                    .execute(&pool).await?;
                println!("Marked {} for reindex. Restart ai-mem-index to reindex.", p);
            }
        }

        Commands::Status => {
            let repos = store::list_repos(&pool).await?;
            println!("Registered repos: {}", repos.len());
            for r in &repos {
                println!("  {} - {}", r.name, r.indexed_at.map(|t| t.to_string()).unwrap_or("unindexed".into()));
            }
        }
    }

    Ok(())
}
```

Add `chrono = { workspace = true }` to `crates/cli/Cargo.toml`.

**Step 2: Verify build**

```bash
cargo build -p ai-mem
```
Expected: clean build.

**Step 3: Smoke test**

```bash
./target/debug/ai-mem --help
./target/debug/ai-mem list
```
Expected: help text and empty repo list.

**Step 4: Commit**

```bash
git add crates/cli/
git commit -m "feat(cli): register, unregister, list, reindex, and status commands"
```

---

### Task 14: Claude Code MCP Registration

**Files:**
- Create: `install.sh`

**Step 1: Create install script**

```bash
#!/usr/bin/env bash
# install.sh — register ai-mem-mcp with Claude Code

set -euo pipefail

BINARY_DIR="${CARGO_TARGET_DIR:-target}/release"

echo "Building release binaries..."
cargo build --release

echo "Installing to ~/.local/bin..."
mkdir -p ~/.local/bin
cp "$BINARY_DIR/ai-mem-index" ~/.local/bin/
cp "$BINARY_DIR/ai-mem-mcp" ~/.local/bin/
cp "$BINARY_DIR/ai-mem" ~/.local/bin/

echo "Registering ai-mem-mcp with Claude Code..."
claude mcp add ai-mem ~/.local/bin/ai-mem-mcp

echo "Done. Run 'ai-mem register <path>' to index your first repo."
```

```bash
chmod +x install.sh
```

**Step 2: Create systemd user unit**

```ini
# ai-mem-index.service
[Unit]
Description=ai-mem indexer daemon
After=network.target postgresql.service

[Service]
ExecStart=%h/.local/bin/ai-mem-index
Restart=on-failure
Environment=RUST_LOG=info

[Install]
WantedBy=default.target
```

**Step 3: Commit**

```bash
git add install.sh ai-mem-index.service
git commit -m "chore: install script and systemd unit for ai-mem-index daemon"
```

---

## Summary

After all tasks complete you will have:

- `flake.nix` — reproducible dev environment (`nix develop`)
- `spec/AiMem.agda` — formal Agda specification
- `crates/core` — shared types, config, DB, parser, embeddings, search, graph
- `crates/indexer` — full reindex + incremental file watcher daemon
- `crates/mcp` — MCP server with 4 search tools
- `crates/cli` — repo management CLI
- `migrations/` — database schema
- `install.sh` — one-command setup

Run `nix develop`, then `./install.sh`, then `ai-mem register /path/to/repo` to start using it.