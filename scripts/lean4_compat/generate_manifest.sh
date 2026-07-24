#!/bin/bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0

# Generate MANIFEST.json from current corpus
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Run after downloading files to create initial manifest.
#
# Usage: ./scripts/lean4_compat/generate_manifest.sh [version] [commit]
# Example: ./scripts/lean4_compat/generate_manifest.sh v4.27.0 db93fe1608548721853390a10cd40580fe7d22ae

set -e
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
DATA_DIR="$REPO_ROOT/tests/lean4_compat"
cd "$DATA_DIR"

VERSION="${1:-v4.27.0}"
COMMIT="${2:-db93fe1608548721853390a10cd40580fe7d22ae}"

if [ ! -d "lean4_tests" ] || [ -z "$(ls -A lean4_tests/*.lean 2>/dev/null)" ]; then
    echo "ERROR: lean4_tests/ directory is empty. Run ./scripts/lean4_compat/download_tests.sh first."
    exit 1
fi

python3 << EOF
import json
import hashlib
import sys
from pathlib import Path
from datetime import datetime, timezone

version = "$VERSION"
commit = "$COMMIT"

checksums = {}
for f in sorted(Path('lean4_tests').glob('*.lean')):
    sha = hashlib.sha256(f.read_bytes()).hexdigest()
    checksums[f.name] = f"sha256:{sha}"

manifest = {
    "lean4_version": version,
    "lean4_commit": commit,
    "tests_path": "tests/lean",
    "downloaded_at": datetime.now(timezone.utc).isoformat().replace('+00:00', 'Z'),
    "file_count": len(checksums),
    "checksums": checksums
}

with open('MANIFEST.json', 'w') as f:
    json.dump(manifest, f, indent=2)
    f.write('\n')

print(f"Generated MANIFEST.json with {len(checksums)} files pinned to {version} ({commit[:12]})")
EOF
