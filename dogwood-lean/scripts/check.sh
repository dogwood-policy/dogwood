#!/usr/bin/env bash
# Checks the specification: every module of the default library `Dogwood`, with
# its proofs and examples, builds, no declaration is left `sorry`ed, and every
# theorem that Axioms.lean names rests on Lean's three standard axioms (`propext`,
# `Classical.choice` and `Quot.sound`) alone.
#
# Usage: dogwood-lean/scripts/check.sh [PROJECT [LOGS]]
#
# PROJECT is the Lake project to check, dogwood-lean/ by default. LOGS is the
# directory for the logs of the build and of the axioms, PROJECT/.lake by default.
# LAKE names the `lake` to run, as a command name or an absolute path, the one on
# the PATH by default.
#
# `lake build` fails when a module does not parse or a proof does not close. Lean
# reports a declaration left `sorry`ed as a warning, not as an error, so the script
# fails on that warning. `lake env lean Axioms.lean` prints the axioms of each
# theorem. The script fails when an axiom beyond the standard three appears (a
# `sorry` adds `sorryAx`, and a `native_decide` adds an axiom of its own), and when
# the number of theorems reported is not the number that Axioms.lean names.
set -euo pipefail
# An exported CDPATH makes `cd` print the directory, which `$(cd … && pwd)` reads.
unset CDPATH

project="$(cd "${1:-$(dirname "$0")/..}" && pwd)"
logs="${2:-$project/.lake}"
mkdir -p "$logs"
logs="$(cd "$logs" && pwd)"
lake="${LAKE:-lake}"
build_log="$logs/lean-library-build.log"
axioms_log="$logs/lean-axioms.log"

echo "[lean] building the specification, its proofs and its examples" >&2
(cd "$project" && "$lake" build) 2>&1 | tee "$build_log"
if grep -q 'declaration uses' "$build_log"; then
  grep 'declaration uses' "$build_log" >&2
  echo '[lean] ERROR: a declaration is left `sorry`ed' >&2
  exit 1
fi

echo "[lean] checking the axioms of every theorem" >&2
if ! (cd "$project" && "$lake" env lean Axioms.lean) > "$axioms_log" 2>&1; then
  cat "$axioms_log" >&2
  echo "[lean] ERROR: Axioms.lean did not elaborate" >&2
  exit 1
fi
# `#print axioms` writes one message for each theorem, `'<name>' depends on axioms:
# […]`, and its list of axioms can continue on the next lines. Join the lines
# before the lists are read.
joined="$(tr '\n' ' ' < "$axioms_log")"
bad="$(grep -oE 'axioms: \[[^]]*\]' <<< "$joined" | tr -d '[]' |
  sed 's/axioms: //' | tr ',' '\n' | tr -d ' ' | sort -u |
  grep -vxF -e propext -e Classical.choice -e Quot.sound || true)"
if [[ -n "$bad" ]]; then
  # The messages of the theorems that rest on such an axiom, so that the output
  # shows them without the log.
  grep -oE "'[^ ]+' depends on axioms: \[[^]]*\]" <<< "$joined" |
    grep -vE 'axioms: \[((propext|Classical\.choice|Quot\.sound),? *)*\]$' >&2 || true
  echo "[lean] ERROR: a theorem rests on an axiom beyond Lean's three standard ones:" \
    "${bad//$'\n'/ } (see $axioms_log)" >&2
  exit 1
fi
want="$(grep -c '^#print axioms ' "$project/Axioms.lean" || true)"
got="$(grep -c "^'" "$axioms_log" || true)"
if [[ "$want" != "$got" ]]; then
  echo "[lean] ERROR: Axioms.lean names $want theorems and $got were reported" \
    "(see $axioms_log)" >&2
  exit 1
fi
echo "[lean] $got theorems, each on Lean's three standard axioms alone" >&2
