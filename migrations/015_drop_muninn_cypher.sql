-- #!migration
-- name: "drop_muninn_cypher",
-- description: "Drop the muninn_cypher stored procedure — replaced by PREPARE/EXECUTE/DEALLOCATE in graph.rs which enforces the query/data boundary at the protocol level (spec: Muninn.Storage, GRAPH-WRITE TIMEOUT section).",
-- requires: "graph_indexes";
DROP FUNCTION IF EXISTS muninn_cypher(text, text, text);
