-- #!migration
-- name: "public-live-family-paths",
-- description: "Track confirmed missing family roots and allow a replacement clone at a retired family's path while retaining the old index.",
-- requires: ["public-family-identity"];
ALTER TABLE public.repos DROP CONSTRAINT repos_path_key;
ALTER TABLE public.repos ADD COLUMN missing_since timestamptz;
CREATE UNIQUE INDEX repos_live_path_idx ON public.repos(path)
    WHERE retired_at IS NULL;
