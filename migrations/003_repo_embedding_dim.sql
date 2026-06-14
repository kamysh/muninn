-- #!migration
-- name: "repo-embedding-dim",
-- description: "003_repo_embedding_dim.sql Record the embedding vector dimension used when each repo was registered. This is the authoritative source for which VECTOR(n) type the per-repo chunks table was created with.  The indexer reads it from the Repo record rather than from the current config, so switching embedding backends in config does not silently corrupt existing tables.",
-- requires: "per-repo-storage";
ALTER TABLE repos ADD COLUMN embedding_dim INT NOT NULL DEFAULT 1024;
