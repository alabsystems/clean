#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Package mathverse .mathverse shards into a versioned tar.zst archive with a blake3
# manifest for integrity verification.
#
# Usage:
#   ./scripts/package_mathverse_release.sh <shard-dir> [options]
#
# Arguments:
#   shard-dir             Directory containing .mathverse shard files
#
# Options:
#   --version=VERSION     Release version (default: from workspace Cargo.toml)
#   --output-dir=DIR      Where to write the archive (default: target/)
#   --dry-run             Generate manifest only, skip archive creation
#
# Output:
#   mathverse-library-vVERSION.tar.zst   Compressed archive of shards + manifest
#   mathverse-manifest.json               Written inside shard-dir before archiving
#
# Prerequisites:
#   - python3
#   - BLAKE3 hasher CLI named b3sum or blake3sum
#   - zstd CLI or tar with zstd support
#
# The manifest (mathverse-manifest.json) lists every .mathverse file with its byte
# size and blake3 checksum. download_mathverse_library.sh verifies against it.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"

format_size_mb() {
    local bytes="$1"
    if command -v awk >/dev/null 2>&1; then
        awk -v bytes="$bytes" 'BEGIN { printf "%.1f", bytes / 1048576 }'
    else
        local tenths
        tenths=$((bytes * 10 / 1048576))
        printf '%d.%d' "$((tenths / 10))" "$((tenths % 10))"
    fi
}

usage() {
    cat <<'USAGE'
Package mathverse .mathverse shards into a versioned tar.zst archive with a blake3 manifest.

Usage:
  ./scripts/package_mathverse_release.sh <shard-dir> [options]

Arguments:
  shard-dir             Directory containing .mathverse shard files

Options:
  --version=VERSION     Release version (default: from workspace Cargo.toml)
  --output-dir=DIR      Where to write the archive (default: target/)
  --dry-run             Generate manifest only, skip archive creation
  --help, -h            Show this help

Output:
  mathverse-library-vVERSION.tar.zst   Compressed archive of shards + manifest
  mathverse-manifest.json              Written inside shard-dir before archiving

Prerequisites:
  - python3
  - BLAKE3 hasher CLI named b3sum or blake3sum
  - zstd CLI or tar with zstd support
USAGE
}

# ---- Defaults ---------------------------------------------------------------
SHARD_DIR=""
VERSION=""
OUTPUT_DIR="target"
DRY_RUN=false

# ---- Parse args --------------------------------------------------------------
for arg in "$@"; do
    case "$arg" in
    --version=*) VERSION="${arg#--version=}" ;;
    --output-dir=*) OUTPUT_DIR="${arg#--output-dir=}" ;;
    --dry-run) DRY_RUN=true ;;
    --help | -h)
        usage
        exit 0
        ;;
    -*)
        echo "Unknown option: $arg" >&2
        exit 1
        ;;
    *)
        if [ -z "$SHARD_DIR" ]; then
            SHARD_DIR="$arg"
        else
            echo "Unexpected argument: $arg" >&2
            exit 1
        fi
        ;;
    esac
done

if [ -z "$SHARD_DIR" ]; then
    usage >&2
    exit 1
fi

if [ ! -d "$SHARD_DIR" ]; then
    echo "Error: shard directory not found: $SHARD_DIR" >&2
    exit 1
fi

# ---- Resolve version from workspace Cargo.toml if not given -----------------
if [ -z "$VERSION" ]; then
    VERSION=$(grep -m1 '^version' "$REPO_ROOT/Cargo.toml" | sed 's/.*"\(.*\)".*/\1/')
fi

ARCHIVE_NAME="mathverse-library-v${VERSION}.tar.zst"
MANIFEST_PATH="${SHARD_DIR}/mathverse-manifest.json"

echo "=== Package Mathverse Release ==="
echo "  Shard dir:  $SHARD_DIR"
echo "  Version:    $VERSION"
echo "  Archive:    ${OUTPUT_DIR}/${ARCHIVE_NAME}"
echo

# ---- Step 1: Compute blake3 checksums for all .mathverse files ------------------
echo "--- Generating manifest ---"

# Find a real blake3 hasher: prefer b3sum, then blake3sum.
HASHER=""
if command -v b3sum >/dev/null 2>&1; then
    HASHER="b3sum"
elif command -v blake3sum >/dev/null 2>&1; then
    HASHER="blake3sum"
fi

# Build manifest JSON
TOTAL_BYTES=0
TOTAL_SHARDS=0
SHARD_ENTRIES_PATH=$(mktemp)
trap 'rm -f "$SHARD_ENTRIES_PATH"' EXIT

while IFS= read -r -d '' shard_file; do
    rel_path="${shard_file#"${SHARD_DIR}/"}"
    file_size=$(stat -f%z "$shard_file" 2>/dev/null || stat -c%s "$shard_file" 2>/dev/null)

    if [ -z "$HASHER" ]; then
        echo "Error: no BLAKE3 hasher found; cannot generate mathverse-manifest.json blake3 fields" >&2
        echo "  Provide a b3sum or blake3sum executable on PATH" >&2
        exit 1
    fi

    file_hash=$($HASHER --no-names "$shard_file" 2>/dev/null || $HASHER "$shard_file" | awk '{print $1}')

    python3 - "$rel_path" "$file_size" "$file_hash" >>"$SHARD_ENTRIES_PATH" <<'PY'
import json
import sys

path, size, blake3 = sys.argv[1], int(sys.argv[2]), sys.argv[3]
print(json.dumps({"path": path, "size": size, "blake3": blake3}))
PY

    TOTAL_BYTES=$((TOTAL_BYTES + file_size))
    TOTAL_SHARDS=$((TOTAL_SHARDS + 1))
done < <(find "$SHARD_DIR" -name '*.mathverse' -type f -print0 | sort -z)

if [ "$TOTAL_SHARDS" -eq 0 ]; then
    echo "Error: shard directory contains no .mathverse shard files: $SHARD_DIR" >&2
    exit 1
fi

CREATED_AT=$(date -u +"%Y-%m-%dT%H:%M:%SZ")

python3 - "$MANIFEST_PATH" "$VERSION" "$CREATED_AT" "$TOTAL_BYTES" "$TOTAL_SHARDS" "$SHARD_ENTRIES_PATH" <<'PY'
import json
import sys
from pathlib import Path

manifest_path, version, created_at, total_bytes, total_shards, entries_path = sys.argv[1:]
shards = [
    json.loads(line)
    for line in Path(entries_path).read_text(encoding="utf-8").splitlines()
    if line
]
manifest = {
    "manifest_version": 1,
    "release_version": version,
    "created_at": created_at,
    "shards": shards,
    "total_bytes": int(total_bytes),
    "total_shards": int(total_shards),
}
Path(manifest_path).write_text(
    json.dumps(manifest, indent=2, sort_keys=True) + "\n",
    encoding="utf-8",
)
PY

echo "  Manifest: $MANIFEST_PATH"
echo "  Shards:   $TOTAL_SHARDS"
echo "  Size:     $(format_size_mb "$TOTAL_BYTES") MB"
echo

if [ "$DRY_RUN" = true ]; then
    echo "--- Dry run: skipping archive creation ---"
    echo "  Manifest written to: $MANIFEST_PATH"
    exit 0
fi

# ---- Step 2: Create tar.zst archive -----------------------------------------
echo "--- Creating archive ---"
mkdir -p "$OUTPUT_DIR"
ARCHIVE_PATH="${OUTPUT_DIR}/${ARCHIVE_NAME}"

SHARD_PARENT=$(dirname "$SHARD_DIR")
SHARD_BASE=$(basename "$SHARD_DIR")

if tar --zstd -cf /dev/null /dev/null 2>/dev/null; then
    tar --zstd -cf "$ARCHIVE_PATH" -C "$SHARD_PARENT" "$SHARD_BASE"
elif command -v zstd >/dev/null 2>&1; then
    tar -cf - -C "$SHARD_PARENT" "$SHARD_BASE" | zstd -o "$ARCHIVE_PATH"
else
    echo "Error: neither tar --zstd nor zstd CLI available" >&2
    echo "  Install zstd: brew install zstd" >&2
    exit 1
fi

ARCHIVE_SIZE=$(stat -f%z "$ARCHIVE_PATH" 2>/dev/null || stat -c%s "$ARCHIVE_PATH" 2>/dev/null)
echo "  Archive: $ARCHIVE_PATH ($(format_size_mb "$ARCHIVE_SIZE") MB)"
echo
echo "=== Packaging complete ==="
