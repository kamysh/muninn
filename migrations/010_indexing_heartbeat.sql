-- #!migration
-- name: "indexing_heartbeat",
-- description: "Add indexing_heartbeat column: the distributed mutex for index_repo exclusion. NULL       = unlocked (no writer active) non-NULL   = locked; holder pulses every 60 s Stale if heartbeat < NOW() - INTERVAL '2 minutes' (holder process is dead)",
-- requires: "repo_ever_indexed";
ALTER TABLE repos ADD COLUMN indexing_heartbeat TIMESTAMPTZ;
