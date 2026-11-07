#!/usr/bin/env bash
# Focused process-level start/progress regression, using the guarded disposable DB.
set -euo pipefail
repo=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo"
if [[ "${1:-}" == --fixture ]]; then
    : "${MUNINN_PERSISTENCE_TEST_CONFIG:?use the disposable persistence harness}"
    exec cargo test -p muninn --test start_progress --locked --offline -- --ignored --nocapture
fi
[[ $# == 0 ]] || { echo 'Usage: bash muninn-setup/test-start-progress.sh' >&2; exit 2; }
cargo test -p muninn --test start_progress --locked --offline --no-run
exec bash muninn-setup/test-persistence.sh "$repo/muninn-setup/test-start-progress.sh" --fixture
