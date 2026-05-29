-- Lock holder kind + foreground preemption signal (spec: Muninn.IndexFsm).
--
-- lock_holder: who currently holds the indexing lock. NULL iff
--   indexing_heartbeat is NULL. 'fg' = foreground CLI job (interactive, never
--   preempted); 'bg' = background daemon reindex (yields to a waiting fg).
-- preempt_requested: a foreground job is waiting for the lock and has asked the
--   background holder to yield. The daemon polls this flag every ~10 s while
--   reindexing and releases the lock when it is set.
ALTER TABLE repos ADD COLUMN lock_holder TEXT CHECK (lock_holder IN ('fg', 'bg'));
ALTER TABLE repos ADD COLUMN preempt_requested BOOLEAN NOT NULL DEFAULT FALSE;
