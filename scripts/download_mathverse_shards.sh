#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Deprecated compatibility wrapper for the manifest-verifying Mathverse downloader.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
LIBRARY_DOWNLOADER="${REPO_ROOT}/scripts/download_mathverse_library.sh"

usage() {
    cat <<'USAGE'
Deprecated compatibility wrapper for Mathverse shard downloads.

Use ./scripts/download_mathverse_library.sh for new automation. This wrapper keeps
the legacy data/mathverse-shards default output directory, but delegates download,
archive selection, extraction, and manifest checksum verification to the
canonical downloader.

Usage:
  ./scripts/download_mathverse_shards.sh [options]

Options:
  --tag=TAG           Download specific mathverse-v* release tag
  --version=VERSION   Download specific Mathverse version
  --output-dir=DIR    Extract destination (default: data/mathverse-shards)
  --skip-verify       Skip manifest checksum verification after download
  --keep-archive      Keep the downloaded .tar.zst after extraction
  --help, -h          Show this help
USAGE
}

normalize_tag_to_version() {
    local tag="$1"

    case "$tag" in
    mathverse-v*)
        printf '%s\n' "${tag#mathverse-v}"
        ;;
    [0-9]*)
        printf '%s\n' "$tag"
        ;;
    *)
        echo "Error: legacy --tag only supports mathverse-v* tags; use download_mathverse_library.sh for other release selectors" >&2
        exit 1
        ;;
    esac
}

ARGS=()
OUTPUT_DIR_SET=false

for arg in "$@"; do
    case "$arg" in
    --tag=*)
        VERSION="$(normalize_tag_to_version "${arg#--tag=}")"
        if [ -z "$VERSION" ]; then
            echo "Error: empty Mathverse version from $arg" >&2
            exit 1
        fi
        ARGS+=("--version=${VERSION}")
        ;;
    --version=*)
        ARGS+=("$arg")
        ;;
    --output-dir=*)
        OUTPUT_DIR_SET=true
        ARGS+=("$arg")
        ;;
    --skip-verify | --keep-archive)
        ARGS+=("$arg")
        ;;
    --help | -h)
        usage
        exit 0
        ;;
    *)
        echo "Unknown option: $arg" >&2
        echo "Run ./scripts/download_mathverse_shards.sh --help for usage." >&2
        exit 1
        ;;
    esac
done

if [ "$OUTPUT_DIR_SET" = false ]; then
    ARGS+=("--output-dir=data/mathverse-shards")
fi

echo "Warning: scripts/download_mathverse_shards.sh is deprecated; delegating to scripts/download_mathverse_library.sh." >&2
echo "         Prefer ./scripts/download_mathverse_library.sh for manifest-verified Mathverse downloads." >&2

exec "$LIBRARY_DOWNLOADER" "${ARGS[@]}"
