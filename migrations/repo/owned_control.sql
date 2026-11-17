-- #!migration
-- name: "repo-owned-control-records",
-- description: "Family-owned logical control records: legacy file facts, configuration staging, accepted work, cleanup tasks, readers, continuations and durable receipts. Matches the formal OwnedState.Body categories legacy, staging, acceptedWork, cleanupWork, activeReader, continuation and receipt.",
-- requires: ["repo-checkout-registry"];

CREATE TABLE legacy_files (
    path text PRIMARY KEY,
    git_answer text NOT NULL,
    payload text NOT NULL,
    created_at timestamptz NOT NULL DEFAULT now()
);

CREATE TABLE staging (
    id uuid PRIMARY KEY DEFAULT gen_random_uuid(),
    payload text NOT NULL,
    created_at timestamptz NOT NULL DEFAULT now()
);

CREATE TABLE accepted_work (
    id uuid PRIMARY KEY DEFAULT gen_random_uuid(),
    operation_id text NOT NULL,
    captured_ids uuid[] NOT NULL DEFAULT '{}',
    payload text NOT NULL,
    created_at timestamptz NOT NULL DEFAULT now()
);
CREATE INDEX accepted_work_operation_idx ON accepted_work (operation_id);

CREATE TABLE cleanup_work (
    id uuid PRIMARY KEY DEFAULT gen_random_uuid(),
    operation_id text NOT NULL,
    captured_ids uuid[] NOT NULL DEFAULT '{}',
    payload text NOT NULL,
    created_at timestamptz NOT NULL DEFAULT now()
);
CREATE INDEX cleanup_work_operation_idx ON cleanup_work (operation_id);

CREATE TABLE active_readers (
    id uuid PRIMARY KEY DEFAULT gen_random_uuid(),
    references uuid[] NOT NULL DEFAULT '{}',
    payload text NOT NULL,
    created_at timestamptz NOT NULL DEFAULT now()
);

CREATE TABLE continuations (
    id uuid PRIMARY KEY DEFAULT gen_random_uuid(),
    captured_ids uuid[] NOT NULL DEFAULT '{}',
    payload text NOT NULL,
    created_at timestamptz NOT NULL DEFAULT now()
);

CREATE TABLE receipts (
    operation_id text PRIMARY KEY,
    state text NOT NULL CHECK (state IN ('active', 'finished')),
    input jsonb,
    work jsonb,
    result jsonb,
    created_at timestamptz NOT NULL DEFAULT now(),
    updated_at timestamptz NOT NULL DEFAULT now()
);
