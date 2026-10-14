#!/usr/bin/env bash
# Refresh every example bundle's `explain.out`: run `dogwood explain` on the
# bundle's inputs, exactly as dogwood-docs/tests/examples.rs does, and write
# the result next to them. Run it after an intended change to the
# informalizer's wording, then review the diff.
#
# Run from the package root (the directory containing Cargo.toml):
#
#     dogwood-docs/examples/regenerate-explain.sh
set -euo pipefail

root="$(cd "$(dirname "$0")/../.." && pwd)"
examples="$root/dogwood-docs/examples"

cd "$root"
cargo build -q --bin dogwood
# Wherever cargo put it (CARGO_TARGET_DIR or a build config may redirect it).
target_dir="$(cargo metadata --no-deps --format-version 1 \
    | sed -n 's/.*"target_directory":"\([^"]*\)".*/\1/p')"
dogwood="$target_dir/debug/dogwood"

count=0
for dir in "$examples"/*/; do
    [ -f "$dir/policy.dw" ] && [ -f "$dir/schema.cedarschema" ] || continue

    # The same flags as the examples harness: macros.dw is a --macros
    # library, providers.json a --providers file, and events.dwschema (or
    # event.dwschema) overrides the default event schema.
    args=(explain "$dir/policy.dw" --policy-schema "$dir/schema.cedarschema")
    [ -f "$dir/macros.dw" ]      && args+=(--macros "$dir/macros.dw")
    [ -f "$dir/providers.json" ] && args+=(--providers "$dir/providers.json")
    for evt in events.dwschema event.dwschema; do
        [ -f "$dir/$evt" ] && { args+=(--event-schema "$dir/$evt"); break; }
    done

    "$dogwood" "${args[@]}" > "$dir/explain.out"
    count=$((count + 1))
done

echo "regenerated explain.out in $count example bundles under $examples"
