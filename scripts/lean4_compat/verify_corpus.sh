#!/bin/bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0

# Verify downloaded corpus matches manifest checksums
# Author: Andrew Yates <andrewyates.name@gmail.com>
#
# Exit 0 if valid, 1 if corrupted/missing files detected.
# Verifies the corpus stored under tests/lean4_compat/.

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
DATA_DIR="$REPO_ROOT/tests/lean4_compat"
cd "$DATA_DIR"

if [ ! -f "MANIFEST.json" ]; then
    echo "ERROR: MANIFEST.json not found."
    exit 1
fi

python3 << 'EOF'
import json
import hashlib
import sys
from pathlib import Path

manifest = json.load(open('MANIFEST.json'))
version = manifest.get('lean4_version', 'unknown')
commit = manifest.get('lean4_commit', 'unknown')[:12]
expected_count = manifest.get('file_count', 0)

print(f"Verifying corpus: Lean 4 {version} ({commit})")
print(f"Expected files: {expected_count}")

errors = 0
verified = 0

for filename, expected in manifest['checksums'].items():
    path = Path('lean4_tests') / filename
    if not path.exists():
        print(f'  MISSING: {filename}')
        errors += 1
        continue
    actual = 'sha256:' + hashlib.sha256(path.read_bytes()).hexdigest()
    if actual != expected:
        print(f'  MISMATCH: {filename}')
        errors += 1
    else:
        verified += 1

# Check for extra files not in manifest
corpus_files = set(f.name for f in Path('lean4_tests').glob('*.lean'))
manifest_files = set(manifest['checksums'].keys())
extra_files = corpus_files - manifest_files

if extra_files:
    print(f"\nExtra files not in manifest: {len(extra_files)}")
    for f in sorted(extra_files)[:5]:
        print(f'  EXTRA: {f}')
    if len(extra_files) > 5:
        print(f'  ... and {len(extra_files) - 5} more')

print(f"\nVerified: {verified}/{expected_count} files")
if errors:
    print(f"Errors: {errors}")
    sys.exit(1)
else:
    print("All checksums match.")
    sys.exit(0)
EOF
