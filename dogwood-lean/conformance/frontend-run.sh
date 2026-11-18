#!/usr/bin/env bash
# Differential run of the Lean frontend (`Dogwood.Frontend`) against the dogwood-language
# crate's frontend, stage by stage, on the same bundle groups as conformance/run.sh.
#
# Usage: dogwood-lean/conformance/frontend-run.sh [--no-export] [--group NAME]...
#                                                [frontend-diff options]...
#
# Builds bridge/ against the in-tree crate (with its `frontend-export` feature), exports each
# bundle group with `--frontend` to conformance/frontend-out/<Group>.json, builds the Lake
# project's `frontend-diff` executable, and runs it on the groups with every baseline in
# conformance/frontend-baseline/. Every other option is passed to `frontend-diff`, for example
# `--check cedarify` to run one check, `--bundle 0042` to run on matching bundles, `--diffs 20`
# to print more disagreements, `--spans` to compare source spans too.
#
# --no-export reuses the JSON files from the last export. --group restricts the run (and the
# export) to the named groups. FRONTEND_OUT names another directory to read the JSON files from,
# for example the export of another checkout of the same crate; it requires --no-export.
#
# Building the executable compiles C with the compiler the Lean toolchain bundles. Where that
# compiler does not run (on a host whose glibc is too old for the bundled clang), set LEAN_CC to
# another C compiler.
set -euo pipefail

here="$(cd "$(dirname "$0")/.." && pwd)"
src="$(cd "$here/.." && pwd)"
tests="$src/dogwood-language/tests"
fixture="$tests/fixtures/request_response.dwschema"

export_json=1
selected=()
passthrough=()
while [ $# -gt 0 ]; do
  case "$1" in
    --no-export) export_json=0; shift ;;
    --group) selected+=("$2"); shift 2 ;;
    *) passthrough+=("$1"); shift ;;
  esac
done

groups=(Examples Mixed ExpectedFailures TemporalCorpus Arithmetic Providers Probes FrontendProbes
  ManyTemporal ManyProviders ManyMixed)
if [ ${#selected[@]} -gt 0 ]; then
  groups=("${selected[@]}")
fi

out="${FRONTEND_OUT:-$here/conformance/frontend-out}"
if [ -n "${FRONTEND_OUT:-}" ] && [ "$export_json" = 1 ]; then
  echo "error: FRONTEND_OUT is only read; pass --no-export" >&2
  exit 2
fi
mkdir -p "$out"

if [ "$export_json" = 1 ]; then
  # The bridge's own toolchain and target directory, as in conformance/run.sh.
  export RUSTUP_TOOLCHAIN="${RUSTUP_TOOLCHAIN:-stable}"
  export CARGO_TARGET_DIR="$here/bridge/target"
  (cd "$here/bridge" && cargo build --release --quiet)
  bridge="$CARGO_TARGET_DIR/release/dogwood-lean-bridge"

  export_group() {
    local group=$1
    shift
    "$bridge" --frontend --out "$out/$group.json" "$@"
  }

  for g in "${groups[@]}"; do
    case "$g" in
      Examples) export_group Examples "$src"/dogwood-docs/examples/*/ ;;
      Mixed) export_group Mixed --default-event-schema "$fixture" \
        "$tests"/passing/mixed/corpus/*/ "$tests"/passing/macros/corpus/*/ ;;
      ExpectedFailures) export_group ExpectedFailures --default-event-schema "$fixture" \
        "$tests"/expected_failures/corpus/*/ ;;
      TemporalCorpus) export_group TemporalCorpus --default-event-schema "$fixture" \
        --shared-schema "$tests/passing/temporal_only/shared_schema.cedarschema" \
        "$tests"/passing/temporal_only/corpus/*/ ;;
      Arithmetic) export_group Arithmetic --default-event-schema "$fixture" \
        "$tests"/experimental/corpus/*/ ;;
      Providers) export_group Providers --default-event-schema "$fixture" \
        --shared-schema "$tests/passing/provider_only/shared_schema.cedarschema" \
        "$tests"/passing/provider_only/corpus/*/ ;;
      Probes) export_group Probes "$here"/conformance/probes/*/ ;;
      # Stable ids, distincters and several policy sets lowered together.
      FrontendProbes) export_group FrontendProbes --default-event-schema "$fixture" \
        "$here"/conformance/frontend-probes/*/ ;;
      # Corpus bundles lowered together, a few at a time, over the first one's schemas.
      ManyTemporal) export_group ManyTemporal --many 3 --default-event-schema "$fixture" \
        --shared-schema "$tests/passing/temporal_only/shared_schema.cedarschema" \
        "$tests"/passing/temporal_only/corpus/*/ ;;
      ManyProviders) export_group ManyProviders --many 2 --default-event-schema "$fixture" \
        --shared-schema "$tests/passing/provider_only/shared_schema.cedarschema" \
        "$tests"/passing/provider_only/corpus/*/ ;;
      ManyMixed) export_group ManyMixed --many 2 --default-event-schema "$fixture" \
        "$tests"/passing/mixed/corpus/*/ "$tests"/passing/macros/corpus/*/ ;;
      *) echo "error: unknown group $g" >&2; exit 2 ;;
    esac
  done
fi

cd "$here"
files=()
for g in "${groups[@]}"; do
  files+=("$out/$g.json")
done
baselines=()
for b in "$here"/conformance/frontend-baseline/*.txt; do
  [ -e "$b" ] && baselines+=(--baseline "$b")
done
lake build frontend-diff
# (`${a[@]+"${a[@]}"}` expands an empty array under `set -u` on older bash.)
exec "$here/.lake/build/bin/frontend-diff" ${baselines[@]+"${baselines[@]}"} \
  ${passthrough[@]+"${passthrough[@]}"} "${files[@]}"
