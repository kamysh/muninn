-- #!migration
-- name: "repo-selection-maintenance",
-- description: "Durable selection refresh requests serialized by the family lock.",
-- requires: ["repo-worktree-file-deltas"];
CREATE TABLE selection_maintenance (
    target uuid PRIMARY KEY,
    requested bigint NOT NULL CHECK (requested >= 0),
    completed bigint NOT NULL DEFAULT 0 CHECK (completed >= 0 AND completed <= requested),
    last_error text
);
