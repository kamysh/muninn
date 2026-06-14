-- #!migration
-- name: "mcp-usage",
-- description: "mcp-usage",
-- requires: "backfill-repo-embedding-dim";
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
