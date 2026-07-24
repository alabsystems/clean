#!/bin/bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0

# Download Lean 4 test files for compatibility testing
# Author: Andrew Yates <andrewyates.name@gmail.com>
#
# Downloads test corpus from a pinned Lean 4 commit specified in MANIFEST.json.
# Stores the corpus under tests/lean4_compat/.

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
DATA_DIR="$REPO_ROOT/tests/lean4_compat"
cd "$DATA_DIR"

# Read pinned version from manifest
MANIFEST="MANIFEST.json"
if [ ! -f "$MANIFEST" ]; then
    echo "ERROR: $MANIFEST not found."
    echo "Run: ./scripts/lean4_compat/generate_manifest.sh <version> <commit>"
    echo "Example: ./scripts/lean4_compat/generate_manifest.sh v4.27.0 db93fe1608548721853390a10cd40580fe7d22ae"
    exit 1
fi

LEAN4_COMMIT=$(python3 -c "import json; print(json.load(open('MANIFEST.json'))['lean4_commit'])")
LEAN4_VERSION=$(python3 -c "import json; print(json.load(open('MANIFEST.json'))['lean4_version'])")
echo "Pinned to Lean 4 $LEAN4_VERSION (commit: ${LEAN4_COMMIT:0:12})"

mkdir -p lean4_tests

echo "Fetching file list from Lean 4 repo..."

# Get list of .lean files from tests/lean directory at pinned commit
curl -sL "https://api.github.com/repos/leanprover/lean4/contents/tests/lean?ref=$LEAN4_COMMIT" \
    -H "Accept: application/vnd.github.v3+json" | \
    python3 -c "
import json, sys
commit = '$LEAN4_COMMIT'
data = json.load(sys.stdin)
for item in data:
    if item['name'].endswith('.lean') and item['type'] == 'file':
        # Use raw URL with pinned commit for reproducibility
        url = f'https://raw.githubusercontent.com/leanprover/lean4/{commit}/tests/lean/{item[\"name\"]}'
        print(url)
" > /tmp/lean4_test_urls.txt

TOTAL=$(wc -l < /tmp/lean4_test_urls.txt)
echo "Found $TOTAL test files"

# Download files (limit to first 100 for initial testing)
COUNT=0
MAX=100

while IFS= read -r url && [ $COUNT -lt $MAX ]; do
    FILENAME=$(basename "$url")
    if [ ! -f "lean4_tests/$FILENAME" ]; then
        echo -ne "\rDownloading [$COUNT/$MAX] $FILENAME"
        curl -sL "$url" -o "lean4_tests/$FILENAME"
    fi
    COUNT=$((COUNT + 1))
done < /tmp/lean4_test_urls.txt

echo ""
echo "Downloaded $COUNT test files to lean4_tests/"
ls lean4_tests/*.lean | wc -l | xargs -I{} echo "{} files ready for testing"
