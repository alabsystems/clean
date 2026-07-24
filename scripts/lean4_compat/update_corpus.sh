#!/bin/bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0

# Update corpus to a new Lean 4 version
# Author: Andrew Yates <andrewyates.name@gmail.com>
#
# Usage: ./scripts/lean4_compat/update_corpus.sh <lean4-version>
# Example: ./scripts/lean4_compat/update_corpus.sh v4.28.0
#
# This script:
# 1. Resolves the commit SHA for the given version tag
# 2. Clears the existing corpus
# 3. Downloads files from the new version
# 4. Generates a new manifest with checksums

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
DATA_DIR="$REPO_ROOT/tests/lean4_compat"
cd "$DATA_DIR"

NEW_VERSION="$1"
if [ -z "$NEW_VERSION" ]; then
    echo "Usage: $0 <lean4-version>"
    echo "Example: $0 v4.28.0"
    exit 1
fi

echo "Resolving commit for $NEW_VERSION..."

# Get commit SHA for version tag (handles both lightweight and annotated tags)
TAG_INFO=$(curl -sL "https://api.github.com/repos/leanprover/lean4/git/refs/tags/$NEW_VERSION" \
    -H "Accept: application/vnd.github.v3+json")

# Check if tag exists
if echo "$TAG_INFO" | grep -q '"message": "Not Found"'; then
    echo "ERROR: Tag $NEW_VERSION not found in leanprover/lean4"
    exit 1
fi

TAG_TYPE=$(echo "$TAG_INFO" | python3 -c "import json,sys; print(json.load(sys.stdin)['object']['type'])")
TAG_SHA=$(echo "$TAG_INFO" | python3 -c "import json,sys; print(json.load(sys.stdin)['object']['sha'])")

if [ "$TAG_TYPE" = "tag" ]; then
    # Annotated tag - need to dereference to get commit
    NEW_COMMIT=$(curl -sL "https://api.github.com/repos/leanprover/lean4/git/tags/$TAG_SHA" \
        -H "Accept: application/vnd.github.v3+json" | \
        python3 -c "import json,sys; print(json.load(sys.stdin)['object']['sha'])")
else
    # Lightweight tag - SHA is the commit directly
    NEW_COMMIT="$TAG_SHA"
fi

echo "Updating to $NEW_VERSION ($NEW_COMMIT)"

# Clear existing corpus
echo "Clearing existing corpus..."
rm -rf lean4_tests
mkdir -p lean4_tests

# Create temporary manifest for download
echo "Creating temporary manifest..."
cat > MANIFEST.json << EOF
{
  "lean4_version": "$NEW_VERSION",
  "lean4_commit": "$NEW_COMMIT",
  "tests_path": "tests/lean",
  "downloaded_at": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "file_count": 0,
  "checksums": {}
}
EOF

# Download new corpus
echo "Downloading new corpus..."
"$SCRIPT_DIR/download_tests.sh"

# Regenerate manifest with checksums
echo "Generating manifest with checksums..."
"$SCRIPT_DIR/generate_manifest.sh" "$NEW_VERSION" "$NEW_COMMIT"

# Verify the new corpus
echo ""
echo "Verifying new corpus..."
"$SCRIPT_DIR/verify_corpus.sh"

echo ""
echo "Update complete. Corpus pinned to $NEW_VERSION ($NEW_COMMIT)"
