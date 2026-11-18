#!/usr/bin/env bash
# Differential conformance run: the specification's validity decision procedure,
# by category, and its decisions, against the dogwood-language crate in this
# repository, on the guide's example bundles, the crate's own test corpora, and
# the probes in conformance/probes.
#
# Usage: dogwood-lean/conformance/run.sh
#
# Builds bridge/ against the in-tree crate, exports each bundle group as JSON to
# conformance/out/, builds the Lake project's `conformance` executable, and
# runs it on the groups with the baseline conformance/baseline.txt. The run
# fails if a lowered bundle disagrees with the specification in a way the
# baseline does not list.
#
# Building the executable compiles C with the compiler the Lean toolchain
# bundles. Where that compiler does not run (on a host whose glibc is too old
# for the bundled clang), set LEAN_CC to another C compiler.
set -euo pipefail

here="$(cd "$(dirname "$0")/.." && pwd)"
src="$(cd "$here/.." && pwd)"
tests="$src/dogwood-language/tests"
fixture="$tests/fixtures/request_response.dwschema"

# Build the bridge with a rustup toolchain and a target directory of its own,
# whatever toolchain file or Cargo configuration the repository has.
export RUSTUP_TOOLCHAIN="${RUSTUP_TOOLCHAIN:-stable}"
export CARGO_TARGET_DIR="$here/bridge/target"

(cd "$here/bridge" && cargo build --release --quiet)
bridge="$CARGO_TARGET_DIR/release/dogwood-lean-bridge"

# The Cedar release on both sides must agree: the crate's cedar-policy, as the
# bridge resolved it, and the cedar-spec tag the Lake project requires.
cargo_cedar="$(grep -A1 '^name = "cedar-policy"$' "$here/bridge/Cargo.lock" | sed -n 's/^version = "\(.*\)"$/\1/p')"
lean_cedar="$(sed -n 's/.*cedar-spec" @ "v\([^"]*\)".*/\1/p' "$here/lakefile.lean")"
if [ "$cargo_cedar" != "$lean_cedar" ]; then
  echo "error: the bridge resolved cedar-policy $cargo_cedar, but lakefile.lean requires cedar-spec v$lean_cedar" >&2
  exit 1
fi

out="$here/conformance/out"
mkdir -p "$out"

export_group() {
  local group=$1
  shift
  "$bridge" --out "$out/$group.json" "$@"
}

groups=(Examples Mixed ExpectedFailures TemporalCorpus Arithmetic Providers Probes)
export_group Examples "$src"/dogwood-docs/examples/*/
export_group Mixed --default-event-schema "$fixture" \
  "$tests"/passing/mixed/corpus/*/ "$tests"/passing/macros/corpus/*/
export_group ExpectedFailures --default-event-schema "$fixture" \
  "$tests"/expected_failures/corpus/*/
export_group TemporalCorpus --default-event-schema "$fixture" \
  --shared-schema "$tests/passing/temporal_only/shared_schema.cedarschema" \
  "$tests"/passing/temporal_only/corpus/*/
export_group Arithmetic --default-event-schema "$fixture" \
  "$tests"/experimental/corpus/*/
export_group Providers --default-event-schema "$fixture" \
  --shared-schema "$tests/passing/provider_only/shared_schema.cedarschema" \
  "$tests"/passing/provider_only/corpus/*/
export_group Probes "$here"/conformance/probes/*/

cd "$here"
files=()
for g in "${groups[@]}"; do
  files+=("$out/$g.json")
done
lake exe conformance --baseline "$here/conformance/baseline.txt" "${files[@]}"
