#!/usr/bin/env bash
# Complete Rust suite, including ignored DB/terminal/performance tests.
set -euo pipefail
repo=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo"
case "${1:-}" in
    --fixture)
        : "${MUNINN_PERSISTENCE_TEST_CONFIG:?use the disposable persistence harness}"
        # The upgrade test must begin on the empty fixture. It exercises the
        # historical-to-current migration and prepares public tables used below.
        # Keep the workspace feature set so this reuses the prebuilt executables.
        cargo test --workspace --all-targets --locked --offline -- \
            family_persistence --exact --ignored --nocapture
        # terminal_session is a subprocess entry point, exercised by every PTY
        # parent test with its required terminal and scenario environment.
        # family_persistence has already run above against the empty fixture.
        result=0
        cargo test --workspace --all-targets --locked --offline --no-fail-fast -- \
            --include-ignored --nocapture --test-threads=1 --skip tui::tests::terminal_session \
            --skip family_persistence || result=$?
        cargo test --workspace --doc --locked --offline || result=$?
        exit "$result"
        ;;
    '')
        # Compilation precedes the fixture's bounded execution window.
        cargo test --workspace --all-targets --locked --offline --no-run
        MUNINN_TEST_TIMEOUT_SECONDS="${MUNINN_TEST_TIMEOUT_SECONDS:-1800}" \
            bash muninn-setup/test-persistence.sh "$repo/muninn-setup/test-all.sh" --fixture
        ;;
    *)
        echo 'Usage: bash muninn-setup/test-all.sh' >&2
        exit 2
        ;;
esac
