#!/usr/bin/env bash
# Reusable crash-injection boundary check. Runs INSIDE the guarded disposable
# fixture (invoked as the payload of muninn-setup/test-persistence.sh); it
# never reads Muninn config or a live database.
#
# The exclusion adapter must register every named commit boundary from
# spec/CRASH-BOUNDARIES.json in a `pub const CRASH_BOUNDARIES: &[&str]` table.
# This check enumerates the registered boundaries against the manifest and
# reports the retry-outcome status per boundary. Missing registrations fail
# the check: a crash at an unregistered boundary cannot be retried against the
# independently specified world outcome, so the coverage must stay red until
# the adapter registers it.
set -euo pipefail
repo=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo"
: "${MUNINN_PERSISTENCE_TEST_CONFIG:?run inside the guarded persistence harness}"

manifest=spec/CRASH-BOUNDARIES.json
jq -e '.schema == 1 and (.boundaries | length > 0)' "$manifest" >/dev/null
jq -e '.adapter_registration.status == "absent" or .adapter_registration.status == "present"' "$manifest" >/dev/null

adapter_file="$repo/$(jq -r '.adapter_registration.rust' "$manifest")"
symbol=$(jq -r '.adapter_registration.symbol' "$manifest")
registered=$(mktemp)
if [[ -f "$adapter_file" ]]; then
    sed -n "s/.*\"\([a-z.]*\)\".*/\\1/p" "$adapter_file" | grep '^exclusion\.' >"$registered" || true
fi

failures=0
while read -r name; do
    if grep -qx "$name" "$registered"; then
        echo "boundary $name: registered"
    else
        echo "boundary $name: NOT REGISTERED — crashes here cannot be retried against the world outcome"
        failures=$((failures + 1))
    fi
done < <(jq -r '.boundaries[].name' "$manifest")

if jq -e '.adapter_registration.status == "absent"' "$manifest" >/dev/null; then
    echo "Exclusion adapter status: ABSENT. The harness reports; it does not invent a happy-path result."
    echo "No runtime repair or deployment is authorized by this slice."
    exit 1
fi

if [[ "$failures" -gt 0 ]]; then
    echo "Missing boundary registrations: $failures"
    exit 1
fi
echo "All exclusion commit boundaries registered; retry assertions belong to the adapter's own harness run."
