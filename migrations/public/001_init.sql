-- #!migration
-- name: "init",
-- description: "Consolidated initial schema for the public database, replacing the former 001-014 migration chain (per user directive: treat pre-reinstall history as void, combine into one file containing only the FINAL table state, not migration history). Defines the tables as they existed after all 14 original migrations: repos, mcp_usage, knowledge. Deliberately excludes: the original shared `chunks` table (created in old 001, dropped in old 002 once per-repo tables were introduced), the shared `code_graph` AGE graph (created in old 001, never referenced again anywhere in the Rust code — dead; per-repo graphs are named code_graph_<uuid> instead), and the muninn_cypher stored procedure (created and dropped within old 008 itself). Per-repo objects (chunks_<uuid> tables in the old design, repo_<uuid> schemas in the current one) and per-repo AGE graphs are created dynamically by application code (store::register_repo), not by this static chain — see migrations/repo/ for the current per-repo schema template. Old migration 014's per-repo AGE-index backfill loop is also excluded here: it is a runtime maintenance operation over dynamic per-repo graphs (a no-op on a fresh database with zero repos), and register_repo already creates the same indexes for every new repo going forward.";
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

-- Repos registry. Column set is the final state after old migrations
-- 001 (create), 003 (+embedding_dim), 004 (-config), 009 (+ever_indexed),
-- 010+012 (+/-indexing_heartbeat, replaced by an advisory lock),
-- 011+012 (+preempt_requested, +/-lock_holder), 013 (+paused).
-- Matches store::REPO_COLUMNS exactly.
CREATE TABLE IF NOT EXISTS repos (
    id                 UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    path               TEXT UNIQUE NOT NULL,
    name               TEXT NOT NULL,
    indexed_at         TIMESTAMPTZ,
    embedding_dim      INT NOT NULL DEFAULT 1024,
    ever_indexed       BOOLEAN NOT NULL DEFAULT FALSE,
    preempt_requested  BOOLEAN NOT NULL DEFAULT FALSE,
    paused             BOOLEAN NOT NULL DEFAULT FALSE
);

-- MCP tool-call usage tracking (old migration 006).
CREATE TABLE IF NOT EXISTS mcp_usage (
    id            BIGSERIAL PRIMARY KEY,
    ts            TIMESTAMPTZ NOT NULL DEFAULT now(),
    tool          TEXT NOT NULL,
    repo_path     TEXT,
    duration_ms   INT,
    result_count  INT
);

CREATE INDEX IF NOT EXISTS mcp_usage_ts_idx ON mcp_usage (ts);
CREATE INDEX IF NOT EXISTS mcp_usage_tool_idx ON mcp_usage (tool);

-- Manually curated knowledge items, independent of code chunks (old migration 007).
CREATE TABLE IF NOT EXISTS knowledge (
    id            UUID        PRIMARY KEY DEFAULT gen_random_uuid(),
    repo_path     TEXT        NOT NULL,
    title         TEXT        NOT NULL CHECK (title  <> ''),
    body          TEXT        NOT NULL CHECK (body   <> ''),
    tags          TEXT[]      NOT NULL DEFAULT '{}',
    related_files TEXT[]      NOT NULL DEFAULT '{}',
    created_at    TIMESTAMPTZ NOT NULL DEFAULT now(),
    updated_at    TIMESTAMPTZ NOT NULL DEFAULT now(),
    embedding     vector,
    ts_vector     TSVECTOR GENERATED ALWAYS AS (
        to_tsvector('english', title || ' ' || body)
    ) STORED
);

CREATE INDEX IF NOT EXISTS knowledge_repo_path_idx ON knowledge (repo_path);
CREATE INDEX IF NOT EXISTS knowledge_ts_idx        ON knowledge USING GIN (ts_vector);
