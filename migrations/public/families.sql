-- #!migration
-- name: "public-family-identity",
-- description: "Add lossless family identity and logical retirement to the existing registry. Preserve legacy IDs and path uniqueness; filesystem identity import is explicit.",
-- requires: ["init"];
ALTER TABLE repos
    ADD COLUMN family_kind text,
    ADD COLUMN path_encoding text,
    ADD COLUMN family_key bytea,
    ADD COLUMN retired_at timestamptz,
    ADD CONSTRAINT repos_family_identity_complete CHECK (
        (family_kind IS NULL AND path_encoding IS NULL AND family_key IS NULL)
        OR (family_kind IS NOT NULL AND path_encoding IS NOT NULL AND family_key IS NOT NULL)
    ),
    ADD CONSTRAINT repos_family_kind_valid CHECK (family_kind IN ('git', 'directory')),
    ADD CONSTRAINT repos_path_encoding_valid CHECK (path_encoding IN ('unix-bytes', 'windows-utf16le')),
    ADD CONSTRAINT repos_family_key_nonempty CHECK (octet_length(family_key) > 0);

-- Compare the full bytes after a digest match; collisions are errors, not aliases.
CREATE UNIQUE INDEX repos_live_family_identity_idx
    ON repos (family_kind, path_encoding, pg_catalog.sha256(family_key))
    WHERE retired_at IS NULL AND family_key IS NOT NULL;

-- #!migration
-- name: "public-family-lifecycle",
-- description: "Record preparation state, storage generation and explicit indexing authorization. Existing registrations remain legacy and are not automatically enabled or imported.";
ALTER TABLE repos
    ADD COLUMN schema_state text NOT NULL DEFAULT 'pending',
    ADD COLUMN schema_error text,
    ADD COLUMN storage_generation text NOT NULL DEFAULT 'legacy',
    ADD COLUMN indexing_enabled_at timestamptz,
    ADD COLUMN indexing_enable_origin text,
    ADD CONSTRAINT repos_schema_state_valid CHECK (schema_state IN ('pending', 'migrating', 'ready', 'failed')),
    ADD CONSTRAINT repos_storage_generation_valid CHECK (storage_generation IN ('legacy', 'snapshots')),
    ADD CONSTRAINT repos_ready_identity CHECK (schema_state <> 'ready' OR family_key IS NOT NULL),
    ADD CONSTRAINT repos_snapshot_identity CHECK (storage_generation <> 'snapshots' OR family_key IS NOT NULL),
    ADD CONSTRAINT repos_indexing_authorization_complete CHECK (
        (indexing_enabled_at IS NULL AND indexing_enable_origin IS NULL)
        OR (indexing_enabled_at IS NOT NULL AND indexing_enable_origin IS NOT NULL)
    ),
    ADD CONSTRAINT repos_indexing_origin_valid CHECK (indexing_enable_origin IN ('explicit-start', 'legacy-import'));

-- #!migration
-- name: "public-family-registration-intent",
-- description: "Persist explicit new-family creation provenance and its frozen initial policy/defaults for interruption recovery. Completed policy remains authoritative in the family application schema.";
ALTER TABLE repos
    ADD COLUMN registration_intent jsonb,
    ADD COLUMN registration_completed_at timestamptz,
    ADD CONSTRAINT repos_registration_intent_shape CHECK (
        registration_intent IS NULL OR COALESCE(
            jsonb_typeof(registration_intent) = 'object'
            AND registration_intent ?& ARRAY['format_version','policy','defaults']
            AND registration_intent - ARRAY['format_version','policy','defaults'] = '{}'::jsonb
            AND registration_intent->'format_version' = '1'::jsonb
            AND jsonb_typeof(registration_intent->'policy') = 'object'
            AND jsonb_typeof(registration_intent->'defaults') = 'object'
            AND family_key IS NOT NULL, false)
    ),
    ADD CONSTRAINT repos_registration_completion CHECK (
        registration_completed_at IS NULL OR registration_intent IS NOT NULL
    );

CREATE FUNCTION preserve_family_registration_intent() RETURNS trigger
LANGUAGE plpgsql AS $$
BEGIN
    IF NEW.registration_intent IS DISTINCT FROM OLD.registration_intent THEN
        RAISE EXCEPTION 'registration intent is immutable; legacy provenance cannot be replaced'
            USING ERRCODE = '23000';
    END IF;
    IF OLD.registration_completed_at IS NOT NULL
       AND NEW.registration_completed_at IS DISTINCT FROM OLD.registration_completed_at THEN
        RAISE EXCEPTION 'registration completion is irreversible'
            USING ERRCODE = '23000';
    END IF;
    RETURN NEW;
END $$;
CREATE TRIGGER repos_preserve_registration_intent BEFORE UPDATE ON repos
    FOR EACH ROW EXECUTE FUNCTION preserve_family_registration_intent();
