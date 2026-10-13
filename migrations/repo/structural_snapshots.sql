-- #!migration
-- name: "repo-worktree-structural-snapshots",
-- description: "Publish linked checkout symbols and edges atomically without rebuilding an AGE graph. Existing graphs remain readable until their checkout is next reconciled.",
-- requires: ["repo-worktree-file-deltas"];
CREATE TABLE checkout_structural_snapshots (
    checkout uuid PRIMARY KEY REFERENCES checkouts(id) ON DELETE CASCADE,
    nodes jsonb NOT NULL CHECK (jsonb_typeof(nodes) = 'array'),
    edges jsonb NOT NULL CHECK (jsonb_typeof(edges) = 'array')
);
