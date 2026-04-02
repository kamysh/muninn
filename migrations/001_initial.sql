DO $$
BEGIN
    IF NOT EXISTS (SELECT 1 FROM pg_extension WHERE extname = 'pgcrypto') THEN
        RAISE EXCEPTION 'Missing extension pgcrypto. Install with: CREATE EXTENSION pgcrypto;';
    END IF;
    IF NOT EXISTS (SELECT 1 FROM pg_extension WHERE extname = 'vector') THEN
        RAISE EXCEPTION 'Missing extension vector (pgvector). Install with: CREATE EXTENSION vector;';
    END IF;
    IF NOT EXISTS (SELECT 1 FROM pg_extension WHERE extname = 'age') THEN
        RAISE EXCEPTION 'Missing extension age (Apache AGE). Install with: CREATE EXTENSION age;';
    END IF;
    IF NOT has_schema_privilege(current_user, 'ag_catalog', 'USAGE') THEN
        RAISE EXCEPTION 'Missing USAGE on schema ag_catalog. Run: GRANT USAGE ON SCHEMA ag_catalog TO %;', current_user;
    END IF;
END $$;

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
DO $$
BEGIN
    IF NOT EXISTS (SELECT 1 FROM ag_catalog.ag_graph WHERE name = 'code_graph') THEN
        PERFORM ag_catalog.create_graph('code_graph');
    END IF;
END $$;
