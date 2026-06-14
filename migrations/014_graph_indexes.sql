-- #!migration
-- name: "graph-indexes",
-- description: "Backfill btree expression indexes on the per-repo AGE graphs. Issue: per-repo `code_graph_<uuid>` schemas had no indexes on the properties muninn matches by (`chunk_id`, `file_path`). `MERGE (n:Label {chunk_id: ...})` in `upsert_symbol_nodes` and `MATCH (n {file_path: ...}) DETACH DELETE n` in `delete_file_symbols` therefore degraded to a full sequential scan of the label tables for every row in `UNWIND $rows`. For a large file (e.g. a minified TypeScript bundle with thousands of symbols), a single MERGE step spent tens of minutes inside AGE with no observable progress — see issue #5. Fix: btree expression indexes on the agtype property access for every per-repo graph and every known vertex label. Empirically a single chunk_id lookup on a 26 793-row `Function` label drops from a 14.9 ms seq scan to a 1.5 ms bitmap index scan; the MERGE that does this lookup once per UNWIND row goes from minutes to subsecond. This migration is idempotent: existing graphs already missing label tables get them created via AGE's `create_vlabel`; existing indexes are skipped via `CREATE INDEX IF NOT EXISTS`. New repos pick up the same indexes through `store::register_repo`, which is updated to call `create_vlabel` + the indexes for the four known labels (Function/Class/Import/Module) at registration time.",
-- requires: "repo-paused";
DO $migration$
DECLARE
    g  TEXT;
    lbl TEXT;
    labels TEXT[] := ARRAY['Function', 'Class', 'Import', 'Module'];
BEGIN
    FOR g IN
        SELECT name FROM ag_catalog.ag_graph WHERE name LIKE 'code_graph_%'
    LOOP
        FOREACH lbl IN ARRAY labels
        LOOP
            -- Step 1: try to eagerly create the label table. AGE creates it
            -- lazily when the first vertex of that label is written; this is
            -- the eager path. Failure here (already-exists, role permission,
            -- etc.) is non-fatal — Step 2 only creates indexes if the table
            -- actually ends up existing.
            BEGIN
                PERFORM ag_catalog.create_vlabel(g, lbl);
            EXCEPTION WHEN others THEN
                NULL;
            END;

            -- Step 2: only create the property indexes if the label table is
            -- actually present in the catalog. Empty graphs (e.g. a repo with
            -- no parsed symbols of this label) skip cleanly; once a future
            -- write creates the table, the next register_repo / migration pass
            -- will pick up the indexes.
            IF EXISTS (
                SELECT 1
                FROM pg_class c
                JOIN pg_namespace n ON c.relnamespace = n.oid
                WHERE n.nspname = g AND c.relname = lbl
            ) THEN
                -- chunk_id index (the MERGE-by-chunk_id hot path).
                EXECUTE format(
                    'CREATE INDEX IF NOT EXISTS %I ON %I.%I USING btree '
                    '((properties -> ''"chunk_id"''::ag_catalog.agtype))',
                    lbl || '_chunk_id_idx',
                    g,
                    lbl
                );

                -- file_path index (the DETACH-DELETE-by-file_path hot path).
                EXECUTE format(
                    'CREATE INDEX IF NOT EXISTS %I ON %I.%I USING btree '
                    '((properties -> ''"file_path"''::ag_catalog.agtype))',
                    lbl || '_file_path_idx',
                    g,
                    lbl
                );
            END IF;
        END LOOP;
    END LOOP;
END
$migration$;
