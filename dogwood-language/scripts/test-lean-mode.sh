#!/usr/bin/env bash
#
# test-lean-mode.sh — Run the crate's tests with the Lean frontend, and check that
# exactly the tests listed in tests/lean-mode-expected.txt fail.
#
# Usage:
#   ./dogwood-language/scripts/test-lean-mode.sh [CARGO TEST ARGS...]
#   ./dogwood-language/scripts/test-lean-mode.sh --from-log FILE
#
# Runs `cargo test --no-fail-fast --features lean-frontend` on the crate with
# DOGWOOD_FRONTEND=lean (every service schema the tests build without an explicit
# frontend lowers and validates with the Lean frontend). Arguments are passed to
# `cargo test`, e.g. `--features experimental-arithmetic` or `--release`.
# LEAN_MODE_LOG=FILE keeps the output of `cargo test` in FILE; `--from-log FILE`
# checks such an output again, without running the tests.
#
# A few tests read what the Lean frontend's results carry in another form: the
# wording and positions of Cedar's own diagnostics, the positions of the
# findings inside a temporal leaf, and the source locations of the lowered Cedar
# policies. tests/lean-mode-expected.txt lists them, one per line, with the
# reason. The run fails if a listed test passes, if a test that is not listed
# fails, or if a test binary does not finish (a crash, say), so the list is
# exactly the Lean frontend's known differences in form.
#
# Exit code:
#   0 — the failing tests are exactly the listed ones
#   1 — they differ (both differences are printed)
#   2 — the tests did not build or did not run to the end
#
set -euo pipefail

CRATE="$(cd "$(dirname "$0")/.." && pwd)"
EXPECTED="$CRATE/tests/lean-mode-expected.txt"
WORK="$(mktemp -d)"
trap 'rm -r "$WORK"' EXIT

cd "$CRATE"
status=0
if [ "${1:-}" = "--from-log" ]; then
    # Check the output of an earlier run instead.
    cp "$2" "$WORK/log"
else
    DOGWOOD_FRONTEND=lean cargo test --no-fail-fast --features lean-frontend "$@" \
        >"$WORK/log" 2>&1 || status=$?
    if [ -n "${LEAN_MODE_LOG:-}" ]; then
        cp "$WORK/log" "$LEAN_MODE_LOG"
    fi
fi

# Each test binary's failing tests, as `<binary source> <test name>`, and the
# binaries that did not report a result.
awk -v unfinished="$WORK/unfinished" '
    /^ *(Running|Doc-tests) / {
        if (binary != "" && !done) print binary > unfinished
        binary = ($1 == "Doc-tests") ? "doc-tests" : ($2 == "unittests") ? $3 : $2
        done = 0; next
    }
    /^test result: / { done = 1; next }
    /^test .* \.\.\. FAILED$/ {
        name = $0; sub(/^test /, "", name); sub(/ \.\.\. FAILED$/, "", name)
        print binary, name
    }
    END { if (binary != "" && !done) print binary > unfinished }
' "$WORK/log" | sort -u >"$WORK/actual"

if ! grep -q '^ *Running ' "$WORK/log"; then
    tail -n 40 "$WORK/log" >&2
    echo "error: the tests did not build (cargo test exited with $status)" >&2
    exit 2
fi
if [ -s "$WORK/unfinished" ]; then
    tail -n 40 "$WORK/log" >&2
    echo "error: these test binaries did not run to the end:" >&2
    sed 's/^/  /' "$WORK/unfinished" >&2
    exit 2
fi

{ grep -v -e '^#' -e '^[[:space:]]*$' "$EXPECTED" || true; } | awk '{ print $1, $2 }' |
    sort -u >"$WORK/expected"

comm -13 "$WORK/expected" "$WORK/actual" >"$WORK/unexpected"
comm -23 "$WORK/expected" "$WORK/actual" >"$WORK/fixed"
passed=$(awk '/^test result: /{ n += $4 } END { print n + 0 }' "$WORK/log")
failed=$(wc -l <"$WORK/actual")

if [ -s "$WORK/unexpected" ] || [ -s "$WORK/fixed" ]; then
    if [ -s "$WORK/unexpected" ]; then
        echo "Tests that fail in Lean mode but are not in tests/lean-mode-expected.txt:"
        sed 's/^/  /' "$WORK/unexpected"
    fi
    if [ -s "$WORK/fixed" ]; then
        echo "Tests in tests/lean-mode-expected.txt that pass in Lean mode (remove them):"
        sed 's/^/  /' "$WORK/fixed"
    fi
    exit 1
fi
echo "Lean mode: $passed passed; $failed failed, exactly the tests tests/lean-mode-expected.txt lists."
