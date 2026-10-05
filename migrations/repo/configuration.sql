-- #!migration
-- name: "repo-family-policy",
-- description: "Immutable family policy/default history and an atomic current-version pointer. No initialization, import, indexing authorization or AGE objects.",
-- requires: ["repo-checkout-observations"];
CREATE FUNCTION valid_policy_rules(doc jsonb) RETURNS boolean
LANGUAGE plpgsql IMMUTABLE STRICT AS $$
BEGIN
    IF jsonb_typeof(doc) IS DISTINCT FROM 'object'
       OR NOT (doc ?& ARRAY['exclude','vendor'])
       OR doc - ARRAY['exclude','vendor'] <> '{}'::jsonb THEN RETURN false; END IF;
    IF jsonb_typeof(doc->'exclude') IS DISTINCT FROM 'array'
       OR jsonb_typeof(doc->'vendor') IS DISTINCT FROM 'array' THEN RETURN false; END IF;
    RETURN NOT EXISTS (
        SELECT 1 FROM jsonb_array_elements((doc->'exclude') || (doc->'vendor')) AS rule
        WHERE jsonb_typeof(rule) <> 'string' OR btrim(rule #>> '{}') IN ('','!')
    );
END $$;

CREATE FUNCTION valid_family_policy(doc jsonb) RETURNS boolean
LANGUAGE plpgsql IMMUTABLE STRICT SET search_path FROM CURRENT AS $$
DECLARE e jsonb; w jsonb;
BEGIN
    IF jsonb_typeof(doc) IS DISTINCT FROM 'object'
       OR NOT (doc ?& ARRAY['name','index','watcher','embeddings'])
       OR doc - ARRAY['name','index','watcher','embeddings'] <> '{}'::jsonb THEN RETURN false; END IF;
    IF jsonb_typeof(doc->'name') IS DISTINCT FROM 'string'
       OR btrim(doc->>'name') = '' OR NOT valid_policy_rules(doc->'index') THEN RETURN false; END IF;
    e := doc->'embeddings'; w := doc->'watcher';
    IF jsonb_typeof(e) IS DISTINCT FROM 'object' OR jsonb_typeof(w) IS DISTINCT FROM 'object'
       OR NOT (e ?& ARRAY['backend','model','batch_size']) OR NOT (w ? 'debounce_ms')
       OR e - ARRAY['backend','model','batch_size'] <> '{}'::jsonb
       OR w - 'debounce_ms' <> '{}'::jsonb THEN RETURN false; END IF;
    IF jsonb_typeof(e->'batch_size') IS DISTINCT FROM 'number'
       OR jsonb_typeof(w->'debounce_ms') IS DISTINCT FROM 'number'
       OR (e->>'batch_size') !~ '^[0-9]+$' OR (w->>'debounce_ms') !~ '^[0-9]+$' THEN RETURN false; END IF;
    RETURN COALESCE(
        (e->>'batch_size')::numeric BETWEEN 1 AND 4294967295
        AND (w->>'debounce_ms')::numeric BETWEEN 0 AND 9007199254740991
        AND ((e->>'backend' = 'local' AND e->'model' = 'null'::jsonb)
          OR (e->>'backend' = 'voyage' AND e->'model' = '"voyage-code-3"'::jsonb)
          OR (e->>'backend' = 'openai' AND e->'model' = '"text-embedding-3-small"'::jsonb)), false);
END $$;

CREATE TABLE policy_defaults (
    revision text PRIMARY KEY CHECK (btrim(revision) <> ''),
    format_version integer NOT NULL CHECK (format_version = 1),
    document jsonb NOT NULL CHECK (
        jsonb_typeof(document) = 'object'
        AND document ?& ARRAY['format_version','revision','index']
        AND document - ARRAY['format_version','revision','index'] = '{}'::jsonb
        AND document->'format_version' = '1'::jsonb
        AND document->'revision' = to_jsonb(revision)
        AND valid_policy_rules(document->'index')
    )
);
CREATE TABLE policy_versions (
    revision bigint PRIMARY KEY CHECK (revision BETWEEN 1 AND 9007199254740991),
    format_version integer NOT NULL CHECK (format_version = 1),
    defaults_revision text NOT NULL REFERENCES policy_defaults(revision),
    policy jsonb NOT NULL CHECK (valid_family_policy(policy)),
    recorded_at timestamptz NOT NULL DEFAULT now()
);
CREATE TABLE family_policy (
    singleton boolean PRIMARY KEY DEFAULT true CHECK (singleton),
    current_revision bigint NOT NULL REFERENCES policy_versions(revision)
);
CREATE FUNCTION reject_policy_history_mutation() RETURNS trigger
LANGUAGE plpgsql AS $$
BEGIN
    RAISE EXCEPTION 'policy history is immutable' USING ERRCODE = '23000';
END $$;
CREATE TRIGGER policy_defaults_immutable BEFORE UPDATE OR DELETE ON policy_defaults
    FOR EACH ROW EXECUTE FUNCTION reject_policy_history_mutation();
CREATE TRIGGER policy_versions_immutable BEFORE UPDATE OR DELETE ON policy_versions
    FOR EACH ROW EXECUTE FUNCTION reject_policy_history_mutation();
