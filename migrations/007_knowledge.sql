-- #!migration
-- name: "knowledge",
-- description: "Knowledge items: manually curated notes and lessons attached to a repo. Distinct from code chunks: not derived from source files, searched independently.",
-- requires: "mcp-usage";
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
