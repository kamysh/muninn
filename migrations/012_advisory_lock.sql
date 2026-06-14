-- #!migration
-- name: "advisory-lock",
-- description: "Switch the index mutex from a heartbeat timestamp to a PostgreSQL session-scoped advisory lock (spec: Muninn.AdvisoryLock). Liveness is now the connection itself — the DB frees the lock when the holding session ends — so the heartbeat timestamp and the holder column are no longer needed. The lock itself is not a column; only the preemption signal remains in the table.",
-- requires: "lock-holder-preempt";
ALTER TABLE repos DROP COLUMN indexing_heartbeat;
ALTER TABLE repos DROP COLUMN lock_holder;
