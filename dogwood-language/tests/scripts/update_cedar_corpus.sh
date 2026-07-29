#!/usr/bin/env bash
# Fetches the Cedar fuzz corpus from cedar-policy/cedar-integration-tests
# and unpacks it into tests/passing/cedar_only/corpus_fuzz/.
#
# Extracts: .cedar, .cedarschema, .json (manifest), .entities.json
#
# Only downloads if the remote file is newer than our local copy (uses
# ETag for conditional fetch). Run this locally before raising a CR to
# pick up any upstream corpus changes.
#
# Usage (from the dogwood-language/ directory):
#   ./tests/scripts/update_cedar_corpus.sh          # conditional fetch
#   ./tests/scripts/update_cedar_corpus.sh --force  # always re-download

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PKG_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"
CORPUS_DIR="$PKG_DIR/tests/passing/cedar_only/corpus_fuzz"
CACHE_DIR="$PKG_DIR/../target/cedar-corpus-cache"
TAR_FILE="$CACHE_DIR/corpus-tests.tar.gz"
ETAG_FILE="$CACHE_DIR/etag.txt"
URL="https://github.com/cedar-policy/cedar-integration-tests/raw/main/corpus-tests.tar.gz"

mkdir -p "$CACHE_DIR"
mkdir -p "$CORPUS_DIR"

FORCE=0
if [[ "${1:-}" == "--force" ]]; then
    FORCE=1
fi

# Conditional fetch using ETag
CURL_OPTS=(-sL -o "$TAR_FILE" -w "%{http_code}")
if [[ -f "$ETAG_FILE" && -f "$TAR_FILE" && "$FORCE" -eq 0 ]]; then
    ETAG=$(cat "$ETAG_FILE")
    CURL_OPTS+=(-H "If-None-Match: $ETAG")
fi

echo "Checking for Cedar corpus updates..."
HTTP_CODE=$(curl "${CURL_OPTS[@]}" -D "$CACHE_DIR/headers.txt" "$URL")

if [[ "$HTTP_CODE" == "304" ]]; then
    echo "Corpus is up to date (304 Not Modified)."
    exit 0
elif [[ "$HTTP_CODE" != "200" ]]; then
    echo "ERROR: Got HTTP $HTTP_CODE from GitHub" >&2
    exit 1
fi

# Save ETag for next conditional fetch
grep -i "^etag:" "$CACHE_DIR/headers.txt" | awk '{print $2}' | tr -d '\r' > "$ETAG_FILE" 2>/dev/null || true

echo "Downloaded new corpus. Unpacking..."

# Remove old files
find "$CORPUS_DIR" -name "*.cedar" -delete 2>/dev/null || true
find "$CORPUS_DIR" -name "*.cedarschema" -delete 2>/dev/null || true
find "$CORPUS_DIR" -name "*.json" -delete 2>/dev/null || true
find "$CORPUS_DIR" -name "*.entities.json" -delete 2>/dev/null || true

# Unpack tar, then copy all relevant files
rm -rf "$CACHE_DIR/corpus-tests"
tar xzf "$TAR_FILE" -C "$CACHE_DIR"
find "$CACHE_DIR/corpus-tests" -name "*.cedar" -exec cp {} "$CORPUS_DIR/" \;
find "$CACHE_DIR/corpus-tests" -name "*.cedarschema" -exec cp {} "$CORPUS_DIR/" \;
find "$CACHE_DIR/corpus-tests" -name "*.entities.json" -exec cp {} "$CORPUS_DIR/" \;
# Copy .json manifests (but not .entities.json which is already handled above)
find "$CACHE_DIR/corpus-tests" -name "*.json" ! -name "*.entities.json" -exec cp {} "$CORPUS_DIR/" \;

COUNT=$(find "$CORPUS_DIR" -name "*.cedar" | wc -l | tr -d ' ')
SCHEMA_COUNT=$(find "$CORPUS_DIR" -name "*.cedarschema" | wc -l | tr -d ' ')
ENTITIES_COUNT=$(find "$CORPUS_DIR" -name "*.entities.json" | wc -l | tr -d ' ')
echo "Done. $COUNT .cedar + $SCHEMA_COUNT .cedarschema + $ENTITIES_COUNT .entities.json"
echo ""
echo "Next steps:"
echo "  git add tests/passing/cedar_only/corpus_fuzz/"
echo "  git commit -m 'chore: update Cedar fuzz corpus ($COUNT policies)'"
