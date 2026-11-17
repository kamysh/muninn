-- #!migration
-- name: "receipt-markers",
-- description: "Installation-owned ID-only receipt markers; finished receipts compact to the operation ID alone and never belong to a removed family.",
-- requires: ["init"];

CREATE TABLE receipt_markers (
    operation_id text PRIMARY KEY,
    created_at timestamptz NOT NULL DEFAULT now()
);
