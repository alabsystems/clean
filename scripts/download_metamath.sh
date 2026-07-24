#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Download Metamath databases (set.mm, iset.mm, nf.mm, ql.mm, demo0.mm, peano.mm).
# Target: data/raw/*.mm in the repo root.
#
# Usage:
#   ./scripts/download_metamath.sh           # downloads to data/raw/
#   ./scripts/download_metamath.sh /tmp/mm   # downloads to /tmp/mm/

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
DATA_DIR="${1:-$REPO_ROOT/data/raw}"
CLONE_DIR="/tmp/metamath-set.mm"

mkdir -p "$DATA_DIR"

echo "=== Downloading Metamath databases ==="
echo "  Target: $DATA_DIR"

# Clone the official set.mm repository (shallow, fast).
if [ -d "$CLONE_DIR" ]; then
    echo "  [SKIP] $CLONE_DIR already exists, pulling..."
    git -C "$CLONE_DIR" pull --ff-only 2>/dev/null || true
else
    echo "  [CLONE] https://github.com/metamath/set.mm -> $CLONE_DIR"
    git clone --depth 1 https://github.com/metamath/set.mm "$CLONE_DIR"
fi

# Copy .mm files to data/raw.
for mm_file in set.mm iset.mm nf.mm ql.mm demo0.mm peano.mm; do
    src="$CLONE_DIR/$mm_file"
    if [ -f "$src" ]; then
        cp -f "$src" "$DATA_DIR/$mm_file"
        echo "  [OK] $mm_file ($(wc -c < "$src" | tr -d ' ') bytes)"
    else
        echo "  [MISS] $mm_file not in repository"
    fi
done

echo ""
echo "=== Summary ==="
ls -lh "$DATA_DIR"/*.mm 2>/dev/null || echo "  No .mm files found"
echo ""
echo "Run verification with:"
echo "  CARGO_BUILD_JOBS=1 cargo test --locked --message-format=short -j 1 -p clean-mathverse --lib -- metamath"
echo "  CARGO_BUILD_JOBS=1 cargo run --locked --quiet --message-format=short -j 1 -p clean-mathverse --bin mathverse_convert -- metamath-dir $DATA_DIR"
