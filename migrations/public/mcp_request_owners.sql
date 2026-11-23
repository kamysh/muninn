-- #!migration
-- name: "mcp-request-owners",
-- description: "Installation-wide owner of a resumable MCP operation ID. Deleting the family leaves an ID-only marker.",
-- requires: ["receipt-markers", "public-family-identity"];
CREATE TABLE mcp_request_owners (
    operation_id text PRIMARY KEY,
    family_id uuid REFERENCES repos(id) ON DELETE SET NULL
);
CREATE INDEX mcp_request_owners_family_idx ON mcp_request_owners (family_id);
