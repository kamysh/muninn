-- #!migration
-- name: "repo-file-layout",
-- description: "Distinguish text-only and structurally chunked layouts of the same file contents.",
-- requires: ["repo-checkout-symlinks"];
ALTER TABLE file_versions ADD COLUMN structured boolean;
ALTER TABLE checkouts ADD COLUMN oversized_paths text[] NOT NULL DEFAULT '{}';
