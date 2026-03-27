-- Enable required extensions
CREATE EXTENSION IF NOT EXISTS "pgcrypto";
CREATE EXTENSION IF NOT EXISTS "vector";
CREATE EXTENSION IF NOT EXISTS "age";
LOAD 'age';
SET search_path = ag_catalog, "$user", public;

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
SELECT * FROM ag_catalog.create_graph('code_graph');