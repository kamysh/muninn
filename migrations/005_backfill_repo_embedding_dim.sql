-- 005_backfill_repo_embedding_dim.sql
-- Backfill repos.embedding_dim from the per-repo chunks table VECTOR(n) typmod.
-- typmod for pgvector is the declared dimension (e.g., vector(10) => atttypmod = 10).

UPDATE repos r
SET embedding_dim = a.atttypmod
FROM pg_class c
JOIN pg_attribute a ON a.attrelid = c.oid AND a.attname = 'embedding'
WHERE c.relname = 'chunks_' || replace(r.id::text, '-', '')
  AND a.atttypmod > 0;
