-- #!migration
-- name: "repo-checkout-symlinks",
-- description: "Remember whether selected checkout files have aliases that can be affected by events on their physical paths.",
-- requires: ["repo-checkout-file-versions"];
ALTER TABLE checkouts ADD COLUMN scans_aliases boolean NOT NULL DEFAULT false;
