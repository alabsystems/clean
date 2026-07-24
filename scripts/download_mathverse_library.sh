#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Download and verify Mathverse Library shard archives from GitHub Releases.
#
# Usage:
#   ./scripts/download_mathverse_library.sh [options]
#
# Options:
#   --version=VERSION   Download specific version (default: latest mathverse-v*)
#   --output-dir=DIR    Extract destination (default: data/mathverse-library/)
#   --skip-verify       Skip manifest checksum verification after download
#   --keep-archive      Keep the downloaded .tar.zst after extraction
#
# The script:
#   1. Resolves the release tag (latest or --version)
#   2. Downloads the mathverse-library-v*.tar.zst archive
#   3. Extracts to --output-dir
#   4. Verifies all .mathverse shards against mathverse-manifest.json checksums
#
# Prerequisites:
#   - gh CLI (authenticated) or curl (fallback)
#   - jq CLI for GitHub API and manifest JSON parsing
#   - zstd CLI or tar with zstd support
#   - b3sum or blake3sum CLI for checksum verification

set -euo pipefail

usage() {
    cat <<'USAGE'
Download and verify Mathverse Library shard archives from GitHub Releases.

Usage:
  ./scripts/download_mathverse_library.sh [options]

Options:
  --version=VERSION   Download specific version (default: latest mathverse-v*)
  --output-dir=DIR    Extract destination (default: data/mathverse-library/)
  --skip-verify       Skip manifest checksum verification after download
  --keep-archive      Keep the downloaded .tar.zst after extraction
  --help, -h          Show this help

Prerequisites:
  - gh CLI (authenticated) or curl fallback
  - jq CLI for GitHub API and manifest JSON parsing
  - zstd CLI or tar with zstd support
  - b3sum or blake3sum CLI for checksum verification
USAGE
}

# Mirror of the Rust CLI default (crates/clean-mathverse/src/release.rs:
# DEFAULT_CLEAN_RELEASE_REPO). Keep these in sync — the `clean mathverse download`
# command and this script must resolve the same GitHub Release source.
REPO="${MATHVERSE_RELEASE_REPO:-alabsystems/clean}"
ARCHIVE_PATTERN="mathverse-library-v*.tar.zst"

require_jq() {
    if ! command -v jq >/dev/null 2>&1; then
        echo "Error: jq is required for Mathverse release JSON parsing" >&2
        echo "  Install jq: brew install jq" >&2
        exit 1
    fi
}

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

# ---- Defaults ---------------------------------------------------------------
VERSION=""
OUTPUT_DIR="data/mathverse-library"
SKIP_VERIFY=false
KEEP_ARCHIVE=false

# ---- Parse args --------------------------------------------------------------
for arg in "$@"; do
    case "$arg" in
    --version=*) VERSION="${arg#--version=}" ;;
    --output-dir=*) OUTPUT_DIR="${arg#--output-dir=}" ;;
    --skip-verify) SKIP_VERIFY=true ;;
    --keep-archive) KEEP_ARCHIVE=true ;;
    --help | -h)
        usage
        exit 0
        ;;
    *)
        echo "Unknown option: $arg" >&2
        exit 1
        ;;
    esac
done

echo "=== Download Mathverse Library ==="

# ---- Step 1: Resolve release tag --------------------------------------------
TAG=""
if [ -n "$VERSION" ]; then
    # Tolerate either a bare version ("1.2.0") or a full tag ("mathverse-v1.2.0").
    VERSION="${VERSION#mathverse-v}"
    TAG="mathverse-v${VERSION}"
    echo "  Requested version: $VERSION (tag: $TAG)"
else
    echo "  Finding latest mathverse release..."
    if command -v gh >/dev/null 2>&1; then
        TAG=$(gh release list --repo "$REPO" --limit 20 --json tagName \
            --jq '[.[] | select(.tagName | startswith("mathverse-v"))][0].tagName // empty' 2>/dev/null || true)
    fi
    if [ -z "$TAG" ]; then
        # Fallback: use GitHub API directly
        require_jq
        TAG=$(curl -sL "https://api.github.com/repos/${REPO}/releases" |
            jq -r '[.[] | select(.tag_name | startswith("mathverse-v"))][0].tag_name // empty' 2>/dev/null || true)
    fi
    if [ -z "$TAG" ]; then
        echo "Error: no mathverse-v* release found for $REPO" >&2
        exit 1
    fi
    echo "  Latest release: $TAG"
fi

case "$TAG" in
mathverse-v*) EXPECTED_VERSION="${TAG#mathverse-v}" ;;
*)
    echo "Error: resolved release tag is not an mathverse-v* tag: $TAG" >&2
    exit 1
    ;;
esac
EXPECTED_ARCHIVE_NAME="mathverse-library-v${EXPECTED_VERSION}.tar.zst"

# ---- Step 2: Download archive ------------------------------------------------
TMPDIR=$(mktemp -d)
trap 'rm -rf "$TMPDIR"' EXIT

echo "  Downloading release assets..."
DOWNLOAD_OK=false

if command -v gh >/dev/null 2>&1; then
    if gh release download "$TAG" --repo "$REPO" --pattern "$ARCHIVE_PATTERN" --dir "$TMPDIR" 2>/dev/null; then
        DOWNLOAD_OK=true
    fi
fi

if [ "$DOWNLOAD_OK" = false ]; then
    echo "  gh download failed, trying curl fallback..."
    require_jq
    ASSET_URL=$(curl -sL "https://api.github.com/repos/${REPO}/releases/tags/${TAG}" |
        jq -r --arg asset_name "$EXPECTED_ARCHIVE_NAME" \
            '.assets[]? | select(.name == $asset_name) | .browser_download_url' 2>/dev/null |
        head -1 || true)
    if [ -z "$ASSET_URL" ]; then
        echo "Error: could not find compatible $ARCHIVE_PATTERN asset matching $EXPECTED_ARCHIVE_NAME for release $TAG" \
            >&2
        exit 1
    fi
    curl -L -o "${TMPDIR}/$(basename "$ASSET_URL")" "$ASSET_URL"
    DOWNLOAD_OK=true
fi

ARCHIVE=$(find "$TMPDIR" -name "$EXPECTED_ARCHIVE_NAME" -type f | head -1)
if [ -z "$ARCHIVE" ]; then
    echo "Error: release $TAG did not provide expected asset $EXPECTED_ARCHIVE_NAME after download" >&2
    echo "  Refusing to use a mismatched $ARCHIVE_PATTERN asset for version $EXPECTED_VERSION." >&2
    exit 1
fi

ARCHIVE_SIZE=$(stat -f%z "$ARCHIVE" 2>/dev/null || stat -c%s "$ARCHIVE" 2>/dev/null)
echo "  Downloaded: $(basename "$ARCHIVE") ($(format_size_mb "$ARCHIVE_SIZE") MB)"

# ---- Step 3: Extract ---------------------------------------------------------
echo "  Extracting to $OUTPUT_DIR ..."
EXTRACT_DIR="${TMPDIR}/extract"
mkdir -p "$EXTRACT_DIR"

if tar --zstd -xf "$ARCHIVE" -C "$EXTRACT_DIR" --strip-components=1 2>/dev/null; then
    : # tar --zstd worked
elif command -v zstd >/dev/null 2>&1; then
    zstd -d "$ARCHIVE" --stdout | tar -xf - -C "$EXTRACT_DIR" --strip-components=1
else
    echo "Error: neither tar --zstd nor zstd CLI available" >&2
    echo "  Install zstd: brew install zstd" >&2
    exit 1
fi

SHARD_COUNT=$(find "$EXTRACT_DIR" -name '*.mathverse' -type f | wc -l | tr -d ' ')
echo "  Extracted: $SHARD_COUNT shard files"
if [ "$SHARD_COUNT" -eq 0 ]; then
    echo "Error: extracted archive contains no .mathverse shard files" >&2
    echo "  Release $TAG may not include a compatible $ARCHIVE_PATTERN asset." >&2
    exit 1
fi

# ---- Step 4: Verify checksums against manifest --------------------------------
MANIFEST="${EXTRACT_DIR}/mathverse-manifest.json"

if [ "$SKIP_VERIFY" = true ]; then
    echo "  Skipping verification (--skip-verify)"
elif [ ! -f "$MANIFEST" ]; then
    echo "Error: mathverse-manifest.json not found; refusing to use unverified Mathverse shards" >&2
    echo "  Use --skip-verify to bypass manifest verification." >&2
    exit 1
else
    echo "  Verifying checksums against manifest..."

    HASHER=""
    if command -v b3sum >/dev/null 2>&1; then
        HASHER="b3sum"
    elif command -v blake3sum >/dev/null 2>&1; then
        HASHER="blake3sum"
    fi

    if [ -z "$HASHER" ]; then
        echo "Error: no BLAKE3 hasher found; refusing to use unverified Mathverse shards" >&2
        echo "  Install: brew install b3sum or cargo install --locked b3sum" >&2
        echo "  Use --skip-verify to bypass manifest verification explicitly." >&2
        exit 1
    else
        require_jq

        if ! jq -e --arg expected_version "$EXPECTED_VERSION" '
            .manifest_version == 1
            and .release_version == $expected_version
            and (.shards | type == "array" and length > 0)
            and all(
                .shards[];
                (.path | type == "string" and length > 0)
                and ((.size | type) == "number")
                and (.size >= 0)
                and ((.size | tostring) | test("^[0-9]+$"))
                and (.blake3 | type == "string" and length > 0)
            )
            and ((.total_shards | type) == "number")
            and (.total_shards >= 0)
            and ((.total_shards | tostring) | test("^[0-9]+$"))
            and (.total_shards == (.shards | length))
            and ((.total_bytes | type) == "number")
            and (.total_bytes >= 0)
            and ((.total_bytes | tostring) | test("^[0-9]+$"))
            and (.total_bytes == ([.shards[].size] | add))
        ' "$MANIFEST" >/dev/null; then
            manifest_version=$(
                jq -r '.manifest_version // "missing"' "$MANIFEST" 2>/dev/null ||
                    printf 'unreadable'
            )
            release_version=$(
                jq -r '.release_version // "missing"' "$MANIFEST" 2>/dev/null ||
                    printf 'unreadable'
            )
            echo "Error: mathverse-manifest.json is not compatible with release $TAG" >&2
            echo "  Expected manifest_version=1 and release_version=$EXPECTED_VERSION." >&2
            echo "  Shard entries and total_shards/total_bytes must match the extracted release manifest." >&2
            echo "  Found manifest_version=$manifest_version release_version=$release_version." >&2
            echo "  Refusing to use Mathverse shards from a mismatched or malformed manifest." >&2
            exit 1
        fi

        MANIFEST_SHARD_LIST="${TMPDIR}/manifest-shards.txt"
        EXTRACTED_SHARD_LIST="${TMPDIR}/extracted-shards.txt"

        jq -r '.shards[] | .path' "$MANIFEST" | LC_ALL=C sort >"$MANIFEST_SHARD_LIST"
        (cd "$EXTRACT_DIR" && find . -name '*.mathverse' -type f | sed 's#^\./##' | LC_ALL=C sort) >"$EXTRACTED_SHARD_LIST"

        if ! cmp -s "$MANIFEST_SHARD_LIST" "$EXTRACTED_SHARD_LIST"; then
            echo "Error: mathverse-manifest.json does not match extracted .mathverse shard set" >&2
            echo "  Refusing to publish unmanifested or missing Mathverse shards." >&2
            echo "  Manifest shard count: $(wc -l <"$MANIFEST_SHARD_LIST" | tr -d ' ')" >&2
            echo "  Extracted shard count: $SHARD_COUNT" >&2
            exit 1
        fi

        VERIFIED=0
        FAILED=0
        MISSING=0

        # Parse manifest and verify each shard
        while IFS=$'\t' read -r shard_path expected_size expected_hash; do
            abs_path="${EXTRACT_DIR}/${shard_path}"
            if [ ! -f "$abs_path" ]; then
                echo "    MISSING: $shard_path"
                MISSING=$((MISSING + 1))
                continue
            fi

            actual_size=$(stat -f%z "$abs_path" 2>/dev/null || stat -c%s "$abs_path" 2>/dev/null)
            actual_hash=$($HASHER --no-names "$abs_path" 2>/dev/null || $HASHER "$abs_path" | awk '{print $1}')

            if [ "$actual_size" != "$expected_size" ]; then
                echo "    FAILED: $shard_path"
                echo "      expected size: $expected_size"
                echo "      actual size:   $actual_size"
                FAILED=$((FAILED + 1))
            elif [ "$actual_hash" = "$expected_hash" ]; then
                VERIFIED=$((VERIFIED + 1))
            else
                echo "    FAILED: $shard_path"
                echo "      expected: $expected_hash"
                echo "      actual:   $actual_hash"
                FAILED=$((FAILED + 1))
            fi
        done < <(jq -r '.shards[] | [.path, .size, .blake3] | @tsv' "$MANIFEST")

        echo "  Verified: $VERIFIED  Failed: $FAILED  Missing: $MISSING"
        if [ "$FAILED" -gt 0 ] || [ "$MISSING" -gt 0 ]; then
            echo "Error: integrity verification failed" >&2
            exit 1
        fi
    fi
fi

# ---- Step 5: Publish clean shard set ----------------------------------------
mkdir -p "$OUTPUT_DIR"
find "$OUTPUT_DIR" -name '*.mathverse' -type f -delete
cp -R "$EXTRACT_DIR"/. "$OUTPUT_DIR"/

# ---- Step 6: Optionally keep archive ----------------------------------------
if [ "$KEEP_ARCHIVE" = true ]; then
    KEPT_PATH="${OUTPUT_DIR}/$(basename "$ARCHIVE")"
    cp "$ARCHIVE" "$KEPT_PATH"
    echo "  Archive kept at: $KEPT_PATH"
fi

echo
echo "=== Mathverse Library ready at: $OUTPUT_DIR ==="
