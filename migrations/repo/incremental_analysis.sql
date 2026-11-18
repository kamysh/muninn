-- #!migration
-- name: "repo-incremental-analysis-reuse",
-- description: "Retain exact source and versioned structural analysis for worktree reconciliation.",
-- requires: ["repo-worktree-file-deltas"];
CREATE TABLE file_content_cache (
    file_version uuid PRIMARY KEY REFERENCES file_versions(id) ON DELETE CASCADE,
    source text NOT NULL
);
CREATE TABLE file_analysis_cache (
    file_version uuid NOT NULL REFERENCES file_versions(id) ON DELETE CASCADE,
    analysis_identity text NOT NULL,
    symbols jsonb NOT NULL,
    candidates jsonb NOT NULL,
    PRIMARY KEY (file_version, analysis_identity)
);
ALTER TABLE file_versions DROP CONSTRAINT file_versions_path_content_hash_tier_key;
CREATE INDEX file_versions_hash_candidates_idx ON file_versions(path, content_hash, tier);
