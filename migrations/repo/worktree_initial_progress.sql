-- #!migration
-- name: "repo-worktree-initial-progress",
-- description: "Pin prepared file versions across retries of the first linked checkout publication.",
-- requires: ["repo-selection-maintenance"];
CREATE TABLE checkout_prepared_files (
    checkout uuid NOT NULL REFERENCES checkouts(id) ON DELETE CASCADE,
    path text NOT NULL,
    version uuid NOT NULL REFERENCES file_versions(id),
    PRIMARY KEY (checkout, path, version)
);
CREATE INDEX checkout_prepared_files_version_idx ON checkout_prepared_files(version);
