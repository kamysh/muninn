-- #!migration
-- name: "repo-worktree-file-deltas",
-- description: "One current base with shared file versions and per-checkout file deltas. AGE graphs are managed separately through AGE APIs.",
-- requires: ["repo-checkout-observations"];
CREATE TABLE file_versions (
    id uuid PRIMARY KEY,
    path text NOT NULL CHECK (path <> ''),
    content_hash bytea NOT NULL,
    tier smallint NOT NULL CHECK (tier IN (1, 2)),
    UNIQUE (path, content_hash, tier)
);
ALTER TABLE chunks
    ADD COLUMN file_version uuid REFERENCES file_versions(id) ON DELETE CASCADE,
    ADD COLUMN in_base boolean NOT NULL DEFAULT true;
CREATE INDEX chunks_file_version_idx ON chunks (file_version);
CREATE TABLE base_files (
    path text PRIMARY KEY,
    version uuid NOT NULL REFERENCES file_versions(id)
);
CREATE TABLE file_deltas (
    checkout uuid NOT NULL REFERENCES checkouts(id) ON DELETE CASCADE,
    path text NOT NULL,
    version uuid REFERENCES file_versions(id),
    PRIMARY KEY (checkout, path)
);
CREATE INDEX file_deltas_version_idx ON file_deltas(version);
ALTER TABLE checkouts ADD COLUMN indexed_at timestamptz;
CREATE TABLE worktree_base (
    singleton boolean PRIMARY KEY DEFAULT true CHECK (singleton),
    checkout uuid NOT NULL REFERENCES checkouts(id)
);

-- #!migration
-- name: "repo-worktree-base-indexes",
-- description: "Keep expensive search indexes on the current base only; delta chunks are reached through file-version references.";
DROP INDEX chunks_emb_idx;
DROP INDEX chunks_ts_idx;
CREATE INDEX chunks_emb_idx ON chunks USING hnsw (embedding public.vector_cosine_ops) WHERE in_base;
CREATE INDEX chunks_ts_idx ON chunks USING gin (ts_vector) WHERE in_base;
