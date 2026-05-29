-- `muninn pause` / `muninn resume`: when true, the indexer daemon skips this repo
-- entirely (no reindex, no watcher) without dropping its index data. Spec:
-- Muninn.Types.Repo.paused / Muninn.Index.daemonDecision (paused → Skip).
ALTER TABLE repos ADD COLUMN paused BOOLEAN NOT NULL DEFAULT FALSE;
