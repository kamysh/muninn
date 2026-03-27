-- 002_per_repo_storage.sql
-- Replace the shared chunks table with per-repo dedicated tables.
--
-- Per-repo tables (chunks_<repo_id_simple>) and AGE graphs
-- (code_graph_<repo_id_simple>) are created and dropped dynamically by
-- register_repo() and delete_repo() in store.rs.  Each repo gets its own
-- HNSW index and GIN ts_vector index, scoping all searches to a single repo
-- without post-filtering overhead.

DROP TABLE IF EXISTS chunks CASCADE;