-- #!migration
-- name: "repo-policy-file-limits",
-- description: "Validate optional file limits without rewriting immutable policy history.",
-- requires: ["repo-family-policy", "repo-file-layout"];
ALTER FUNCTION valid_family_policy(jsonb) RENAME TO valid_family_policy_v1;
CREATE FUNCTION valid_family_policy(doc jsonb) RETURNS boolean
LANGUAGE plpgsql IMMUTABLE STRICT SET search_path FROM CURRENT AS $$
DECLARE limits jsonb;
BEGIN
    IF NOT valid_family_policy_v1(doc - 'limits') THEN
        RETURN false;
    END IF;
    IF NOT doc ? 'limits' THEN
        RETURN true;
    END IF;
    limits := doc->'limits';
    IF jsonb_typeof(limits) IS DISTINCT FROM 'object'
       OR limits - ARRAY['selected_bytes', 'structural_bytes'] <> '{}'::jsonb
       OR jsonb_typeof(limits->'selected_bytes') IS DISTINCT FROM 'number'
       OR jsonb_typeof(limits->'structural_bytes') IS DISTINCT FROM 'number'
       OR (limits->>'selected_bytes') !~ '^[0-9]+$'
       OR (limits->>'structural_bytes') !~ '^[0-9]+$' THEN
        RETURN false;
    END IF;
    RETURN (limits->>'selected_bytes')::numeric <= 9007199254740991
       AND (limits->>'structural_bytes')::numeric <= (limits->>'selected_bytes')::numeric;
END $$;
ALTER TABLE policy_versions DROP CONSTRAINT policy_versions_policy_check,
   ADD CONSTRAINT policy_versions_policy_check CHECK (valid_family_policy(policy));
