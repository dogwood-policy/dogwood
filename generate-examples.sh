#!/bin/bash
# Generate mdBook-compatible markdown pages for each example in dogwood-docs/examples/.
# Produces:
#   dogwood-docs/mdbook-src/examples/index.md   (table of all examples)
#   dogwood-docs/mdbook-src/examples/<name>.md  (per-example detail page)
# Also appends example entries to SUMMARY.md.

set -euo pipefail

EXAMPLES_DIR="dogwood-docs/examples"
OUTPUT_DIR="dogwood-docs/mdbook-src/examples"
SUMMARY="dogwood-docs/mdbook-src/SUMMARY.md"

mkdir -p "$OUTPUT_DIR"

# --- Build index page with table ---
{
  echo "# Examples"
  echo ""
  echo "| Example | Description |"
  echo "|---------|-------------|"
} > "$OUTPUT_DIR/index.md"

# Collect example entries for SUMMARY.md
SUMMARY_ENTRIES=""

for dir in "$EXAMPLES_DIR"/*/; do
  [ -d "$dir" ] || continue
  name=$(basename "$dir")
  readme="$dir/README.md"

  if [ ! -f "$readme" ]; then
    continue
  fi

  # Extract first paragraph (after the heading) as description
  description=$(sed -n '/^$/,/^$/{ /^$/d; p; }' "$readme" | head -1 | sed 's/|/\\|/g')

  # Add to index table
  echo "| [$name](./${name}.md) | $description |" >> "$OUTPUT_DIR/index.md"

  # --- Build per-example page ---
  {
    # Include the README content
    cat "$readme"
    echo ""

    # Policy
    if [ -f "$dir/policy.dw" ]; then
      echo "## Policy"
      echo ""
      echo '```text'
      cat "$dir/policy.dw"
      echo '```'
      echo ""
    fi

    # Schema
    if [ -f "$dir/schema.cedarschema" ]; then
      echo "## Schema"
      echo ""
      echo '```text'
      cat "$dir/schema.cedarschema"
      echo '```'
      echo ""
    fi

    # Trace
    if [ -f "$dir/trace.log" ]; then
      echo "## Trace"
      echo ""
      echo '```text'
      cat "$dir/trace.log"
      echo '```'
      echo ""
    fi

    # Expected output
    if [ -f "$dir/expected.out" ]; then
      echo "## Expected Output"
      echo ""
      echo '```text'
      cat "$dir/expected.out"
      echo '```'
      echo ""
    fi

    # Macros (if present)
    if [ -f "$dir/macros.dw" ]; then
      echo "## Macros"
      echo ""
      echo '```text'
      cat "$dir/macros.dw"
      echo '```'
      echo ""
    fi

    # Providers (if present)
    if [ -f "$dir/providers.json" ]; then
      echo "## Provider Declarations"
      echo ""
      echo '```json'
      cat "$dir/providers.json"
      echo '```'
      echo ""
    fi

    # Event schema (if present)
    if [ -f "$dir/event.dwschema" ] || [ -f "$dir/events.dwschema" ]; then
      echo "## Event Schema"
      echo ""
      echo '```text'
      cat "$dir"/event*.dwschema 2>/dev/null
      echo '```'
      echo ""
    fi
  } > "$OUTPUT_DIR/${name}.md"

  SUMMARY_ENTRIES="${SUMMARY_ENTRIES}  - [${name}](./examples/${name}.md)
"
done

# --- Update SUMMARY.md with example entries ---
# Replace everything from "# Examples" onward with the index + individual pages.
# Individual pages must be in SUMMARY.md for mdBook to build them, but we hide
# them from the sidebar via CSS.
tmp=$(mktemp)
sed '/^# Examples/,$d' "$SUMMARY" > "$tmp"
mv "$tmp" "$SUMMARY"

{
  echo "# Examples"
  echo ""
  echo "- [Examples Index](./examples/index.md)"
  echo "$SUMMARY_ENTRIES"
} >> "$SUMMARY"

echo "Generated $(ls "$OUTPUT_DIR"/*.md | wc -l | tr -d ' ') example pages."
