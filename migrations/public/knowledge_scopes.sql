-- #!migration
-- name: "knowledge-family-scopes",
-- description: "Bind newly recorded notes to a repository family and an optional checkout identity while preserving existing path-keyed notes.",
-- requires: ["public-family-identity"];
ALTER TABLE knowledge
    ADD COLUMN family_id uuid,
    ADD COLUMN checkout_key bytea,
    ADD CONSTRAINT knowledge_checkout_requires_family
        CHECK (checkout_key IS NULL OR family_id IS NOT NULL);

CREATE INDEX knowledge_family_checkout_idx ON knowledge(family_id, checkout_key)
    WHERE family_id IS NOT NULL;
