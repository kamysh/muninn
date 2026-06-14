-- #!migration
-- name: "drop-repo-config",
-- description: "drop-repo-config",
-- requires: "repo-embedding-dim";
ALTER TABLE repos DROP COLUMN IF EXISTS config;
