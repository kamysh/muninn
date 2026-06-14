-- #!migration
-- name: "repo_ever_indexed",
-- description: "Add ever_indexed flag: true after the first successful index, survives reindex reset. Existing repos with indexed_at IS NOT NULL have been indexed before.",
-- requires: "age_cypher_wrapper";
ALTER TABLE repos ADD COLUMN ever_indexed BOOLEAN NOT NULL DEFAULT FALSE;
UPDATE repos SET ever_indexed = TRUE WHERE indexed_at IS NOT NULL;
