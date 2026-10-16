-- #!migration
-- name: "repo-missing-checkout-grace",
-- description: "Track how long a Git-listed checkout has been absent before retiring it.",
-- requires: ["repo-checkout-observations"];
ALTER TABLE checkouts ADD COLUMN missing_since timestamptz;
