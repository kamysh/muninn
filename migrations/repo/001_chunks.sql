-- #!migration
-- name: "repo-chunks",
-- description: "Per-repo chunk table template. Applied identically to every repo's own Postgres schema via kryzhen's schema-templating (kryzhen::migrate(client, migrations, Some(schema), false) — see db::run_repo_migrations). Holds file chunks: content, tier (Tier1/Tier2), embedding lifecycle state, a content_hash for dedup, and the embedding vector. Unqualified DDL below lands in whatever schema kryzhen sets via SET LOCAL search_path, so this script is schema-agnostic on purpose. The embedding column's SQL type is vector(N), where N is this repo's configured embedding dimension (512/1024/1536/...) — that varies per repo, yet the script text below is still byte-identical across every schema it is applied to (satisfying kryzhen's one-checksum-per-name invariant): the trailing DO block reads this repo's embedding_dim from public.repos (matched via current_schema(), which kryzhen sets to repo_<simple-uuid> before running this script) and builds the ALTER TABLE/CREATE INDEX dynamically via EXECUTE format(...). A dimensionless vector column was considered instead (would let the whole table be static DDL) but rejected: pgvector's HNSW index requires a fixed-dimension column type (verified live — CREATE INDEX ... USING hnsw on an unconstrained vector column errors 'column does not have dimensions'). So the DATA the script reads varies per repo; the script TEXT does not.";
CREATE TABLE IF NOT EXISTS chunks (
    id              UUID PRIMARY KEY,
    repo_id         UUID NOT NULL,
    file_path       TEXT NOT NULL,
    start_line      INT NOT NULL,
    end_line        INT NOT NULL CHECK (end_line >= start_line),
    content         TEXT NOT NULL CHECK (content <> ''),
    ts_vector       TSVECTOR GENERATED ALWAYS AS (to_tsvector('english', content)) STORED,
    tier            SMALLINT NOT NULL DEFAULT 1,
    embedding_state TEXT NOT NULL DEFAULT 'embedded'
                    CHECK (embedding_state IN ('embedded','pending','absent')),
    content_hash    BYTEA
);

CREATE INDEX IF NOT EXISTS chunks_ts_idx ON chunks USING GIN (ts_vector);

-- Partial index over the Tier-2 backfill backlog — the daemon's "find work"
-- query is WHERE embedding_state = 'pending'.
CREATE INDEX IF NOT EXISTS chunks_pending_idx ON chunks (embedding_state) WHERE embedding_state = 'pending';

CREATE INDEX IF NOT EXISTS chunks_file_idx ON chunks (file_path);

-- Add the embedding column at this repo's own dimension (see description above
-- for why this can be dynamic while the script stays static).
DO $do$
DECLARE
    repo_uuid uuid := replace(current_schema(), 'repo_', '')::uuid;
    dim       int;
BEGIN
    SELECT embedding_dim INTO dim FROM public.repos WHERE id = repo_uuid;
    IF dim IS NULL THEN
        RAISE EXCEPTION 'repo-chunks: no repos row for schema %', current_schema();
    END IF;

    IF NOT EXISTS (
        SELECT 1 FROM information_schema.columns
        WHERE table_schema = current_schema() AND table_name = 'chunks' AND column_name = 'embedding'
    ) THEN
        EXECUTE format('ALTER TABLE chunks ADD COLUMN embedding public.vector(%s)', dim);
    END IF;

    IF NOT EXISTS (
        SELECT 1 FROM pg_indexes
        WHERE schemaname = current_schema() AND tablename = 'chunks' AND indexname = 'chunks_emb_idx'
    ) THEN
        EXECUTE 'CREATE INDEX chunks_emb_idx ON chunks USING hnsw (embedding public.vector_cosine_ops)';
    END IF;
END
$do$;
