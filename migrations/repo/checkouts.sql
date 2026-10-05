-- #!migration
-- name: "repo-checkout-registry",
-- description: "Checkout registration metadata, templated into each family's application schema. Contains no file copies, snapshot placeholders or AGE objects.",
-- requires: ["repo-chunks"];
CREATE TABLE checkouts (
    id uuid PRIMARY KEY DEFAULT gen_random_uuid(),
    root bytea NOT NULL CHECK (octet_length(root) > 0),
    git_dir bytea CHECK (octet_length(git_dir) > 0),
    incarnation uuid NOT NULL UNIQUE DEFAULT gen_random_uuid(),
    registration_state text NOT NULL DEFAULT 'active'
        CHECK (registration_state IN ('active', 'suppressed', 'retired')),
    paused boolean NOT NULL DEFAULT false,
    created_at timestamptz NOT NULL DEFAULT now(),
    retired_at timestamptz,
    CONSTRAINT checkouts_retirement_consistent CHECK (
        (registration_state = 'retired') = (retired_at IS NOT NULL)
    )
);

CREATE UNIQUE INDEX checkouts_live_root_idx ON checkouts (pg_catalog.sha256(root))
    WHERE registration_state <> 'retired';
CREATE UNIQUE INDEX checkouts_live_git_dir_idx ON checkouts (pg_catalog.sha256(git_dir))
    WHERE git_dir IS NOT NULL AND registration_state <> 'retired';

-- #!migration
-- name: "repo-checkout-observations",
-- description: "Persist checkout generation and availability/Git observations. Unknown is the initial state; observations do not authorize publication or indexing.";
ALTER TABLE checkouts
    ADD COLUMN dirty_generation bigint NOT NULL DEFAULT 0 CHECK (dirty_generation >= 0),
    ADD COLUMN availability text NOT NULL DEFAULT 'unknown'
        CHECK (availability IN ('unknown', 'available', 'unavailable')),
    ADD COLUMN git_state text NOT NULL DEFAULT 'unknown'
        CHECK (git_state IN ('unknown', 'clear', 'blocked', 'not-git')),
    ADD COLUMN merge_in_progress boolean,
    ADD COLUMN rebase_merge_in_progress boolean,
    ADD COLUMN rebase_apply_in_progress boolean,
    ADD COLUMN unmerged_index boolean,
    ADD COLUMN observed_at timestamptz,
    ADD COLUMN last_seen_at timestamptz,
    ADD COLUMN observation_error text,
    ADD CONSTRAINT checkouts_git_observation_consistent CHECK (
        (git_state IN ('unknown', 'not-git')
            AND merge_in_progress IS NULL AND rebase_merge_in_progress IS NULL
            AND rebase_apply_in_progress IS NULL AND unmerged_index IS NULL)
        OR
        (git_state IN ('clear', 'blocked')
            AND merge_in_progress IS NOT NULL AND rebase_merge_in_progress IS NOT NULL
            AND rebase_apply_in_progress IS NOT NULL AND unmerged_index IS NOT NULL
            AND ((git_state = 'blocked') =
                (merge_in_progress OR rebase_merge_in_progress OR rebase_apply_in_progress OR unmerged_index)))
    ),
    ADD CONSTRAINT checkouts_git_observation_timestamp CHECK (git_state = 'unknown' OR observed_at IS NOT NULL);
