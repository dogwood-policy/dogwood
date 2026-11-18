#!/usr/bin/env bash
# Generated differential testing: write bundles with conformance/gen/gen.py, export them with the
# bridge, and run both harnesses on them (the Lean frontend against the crate, stage by stage;
# the specification against the crate's validator and verdicts, with the crate's temporal engine
# run whole and partitioned by the universal pins).
#
# Usage: dogwood-lean/conformance/gen-run.sh SEED COUNT [run.py options]...
#
# The bundles, the exports and the summary go to $GEN_OUT/<SEED>-<start> (GEN_OUT defaults to
# $TMPDIR/dogwood-gen, or /tmp/dogwood-gen). Options are passed to conformance/gen/run.py:
# `--start I` (the first bundle index, default 0), `--chunk K` (bundles per export, 250),
# `--jobs J` (chunks in parallel, 4), `--family F` (repeatable: generate only these families),
# `--spans` (compare source spans in the frontend harness), `--timeout S` (seconds a harness may
# take on one chunk, 600), `--keep-json` (keep the exports), `--no-partitioned`. A bundle is a
# function of the seed and its index alone: `conformance/gen/gen.py --seed SEED --start I
# --count 1 --out DIR` writes it again.
#
# Building the executables compiles C with the compiler the Lean toolchain bundles. Where that
# compiler does not run, set LEAN_CC to another C compiler.
set -euo pipefail

if [ $# -lt 2 ]; then
  echo "usage: $0 SEED COUNT [run.py options]..." >&2
  exit 2
fi
seed=$1
count=$2
shift 2

here="$(cd "$(dirname "$0")/.." && pwd)"
start=0
args=("$@")
for ((i = 0; i < ${#args[@]}; i++)); do
  if [ "${args[$i]}" = "--start" ]; then start=${args[$((i + 1))]}; fi
done
out="${GEN_OUT:-${TMPDIR:-/tmp}/dogwood-gen}/$seed-$start"
mkdir -p "$out"

export RUSTUP_TOOLCHAIN="${RUSTUP_TOOLCHAIN:-stable}"
export CARGO_TARGET_DIR="$here/bridge/target"
(cd "$here/bridge" && cargo build --release --quiet)
cd "$here"
lake build frontend-diff conformance
exec python3 "$here/conformance/gen/run.py" --seed "$seed" --count "$count" --out "$out" "$@"
