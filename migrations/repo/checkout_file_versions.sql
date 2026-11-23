-- #!migration
-- name: "repo-checkout-file-versions",
-- description: "Resolve old moving-base views into independent checkout membership in shared file versions.",
-- requires: ["repo-worktree-initial-progress", "repo-worktree-base-indexes", "repo-worktree-structural-snapshots"];
CREATE TABLE checkout_file_versions (
    checkout uuid NOT NULL REFERENCES checkouts(id) ON DELETE CASCADE,
    version uuid NOT NULL REFERENCES file_versions(id),
    PRIMARY KEY (checkout, version)
);
CREATE INDEX checkout_file_versions_version_idx ON checkout_file_versions(version);
ALTER TABLE checkouts
    ADD COLUMN publication_generation bigint NOT NULL DEFAULT 0,
    ADD COLUMN indexed_git_head text,
    ADD COLUMN unreadable_paths text[] NOT NULL DEFAULT ARRAY[]::text[];

INSERT INTO checkout_file_versions (checkout, version)
SELECT c.id, b.version
FROM checkouts c CROSS JOIN base_files b
WHERE c.indexed_at IS NOT NULL AND c.registration_state <> 'retired'
  AND NOT EXISTS (
    SELECT FROM file_deltas d WHERE d.checkout = c.id AND d.path = b.path
  )
UNION
SELECT d.checkout, d.version
FROM file_deltas d
JOIN checkouts c ON c.id = d.checkout
WHERE d.version IS NOT NULL
  AND (c.indexed_at IS NOT NULL OR c.registration_state = 'retired');

-- The old tables served as compact references. The new memberships are now
-- the roots for every published or deliberately retained view.
DROP TABLE file_deltas;
DROP TABLE base_files;
DROP INDEX chunks_emb_idx;
DROP INDEX chunks_ts_idx;
CREATE INDEX chunks_emb_idx ON chunks USING hnsw (embedding public.vector_cosine_ops)
    WHERE embedding IS NOT NULL;
CREATE INDEX chunks_ts_idx ON chunks USING gin (ts_vector);
