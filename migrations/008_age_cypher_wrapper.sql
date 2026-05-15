-- Wrapper for ag_catalog.cypher that accepts plain text parameters.
--
-- AGE 1.6.0 requires the third argument to cypher() to be a bare $N Param
-- node (not a TypeCast), and sqlx cannot send parameters with the agtype OID.
-- This function accepts gname, query, and params as plain text, then executes
-- the cypher call via dynamic SQL (EXECUTE...USING) so the $1 Param inside
-- the dynamic string is correctly typed as ag_catalog.agtype.
CREATE OR REPLACE FUNCTION muninn_cypher(gname text, query text, params text)
RETURNS SETOF ag_catalog.agtype AS $func$
BEGIN
    RETURN QUERY EXECUTE format(
        'SELECT result FROM ag_catalog.cypher(%L, $$%s$$, $1) AS (result ag_catalog.agtype)',
        gname, query
    ) USING params::ag_catalog.agtype;
END;
$func$ LANGUAGE plpgsql;