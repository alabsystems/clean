#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Build mathverse shards from Lean 4 .olean libraries, package them with a
# downloader-compatible manifest, and publish as a GitHub Release artifact.
#
# Usage:
#   ./scripts/release_mathverse_shards.sh <lean-lib-dir> [options]
#   ./scripts/release_mathverse_shards.sh --native-only [options]
#
# Options:
#   --tag=TAG             Release tag (default: mathverse-v<workspace-version>)
#   --output-dir=DIR      Shard build output (default: target/mathverse-shards)
#   --modules=Init,Std    Module prefixes passed to mathverse_shard build
#   --shard-size=N        Max constants per shard (default: 10000)
#   --native-only         Skip .olean scan; build only the Clean-Native shard
#                         from kernel-proved constructive theorems. Writes
#                         Clean-native.mathverse + sidecar into --output-dir.
#   --dry-run             Build and compress but skip GitHub release
#   --mirror              After release, mirror to alabsystems/clean
#   --mirror-repo=REPO    Override mirror target (default: alabsystems/clean)
#   --verbose             Pass --verbose to mathverse_shard build
#
# Prerequisites:
#   - Rust toolchain (cargo)
#   - zstd CLI or tar with zstd support
#   - gh CLI (authenticated) for release creation

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

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
Build mathverse shards from Lean 4 .olean libraries, package them with a downloader-compatible manifest, and publish as a GitHub Release artifact.

Usage:
  ./scripts/release_mathverse_shards.sh <lean-lib-dir> [options]
  ./scripts/release_mathverse_shards.sh --native-only [options]

Options:
  --tag=TAG             Release tag (default: mathverse-v<workspace-version>)
  --output-dir=DIR      Shard build output (default: target/mathverse-shards)
  --modules=Init,Std    Module prefixes passed to mathverse_shard build
  --shard-size=N        Max constants per shard (default: 10000)
  --native-only         Skip .olean scan; build only the Clean-Native shard
  --dry-run             Build and compress but skip GitHub release
  --mirror              After release, mirror to alabsystems/clean
  --mirror-repo=REPO    Override mirror target (default: alabsystems/clean)
  --verbose             Pass --verbose to mathverse_shard build
  --help, -h            Show this help

Prerequisites:
  - Rust toolchain (cargo)
  - zstd CLI or tar with zstd support
  - gh CLI (authenticated) for release creation
USAGE
}

# ---- Defaults ---------------------------------------------------------------
LEAN_LIB_DIR=""
OUTPUT_DIR="target/mathverse-shards"
TAG=""
MODULES=""
SHARD_SIZE=""
DRY_RUN=false
MIRROR=false
MIRROR_REPO="alabsystems/clean"
VERBOSE=""
NATIVE_ONLY=false
EXTRA_BUILD_ARGS=()
export CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-1}"

# ---- Parse args --------------------------------------------------------------
for arg in "$@"; do
    case "$arg" in
    --tag=*) TAG="${arg#--tag=}" ;;
    --output-dir=*) OUTPUT_DIR="${arg#--output-dir=}" ;;
    --modules=*) MODULES="${arg#--modules=}" ;;
    --shard-size=*) SHARD_SIZE="${arg#--shard-size=}" ;;
    --dry-run) DRY_RUN=true ;;
    --mirror) MIRROR=true ;;
    --mirror-repo=*)
        MIRROR=true
        MIRROR_REPO="${arg#--mirror-repo=}"
        ;;
    --verbose) VERBOSE="--verbose" ;;
    --native-only) NATIVE_ONLY=true ;;
    --help | -h)
        usage
        exit 0
        ;;
    -*)
        echo "Unknown option: $arg" >&2
        exit 1
        ;;
    *)
        if [ -z "$LEAN_LIB_DIR" ]; then
            LEAN_LIB_DIR="$arg"
        else
            echo "Unexpected argument: $arg" >&2
            exit 1
        fi
        ;;
    esac
done

if [ "$NATIVE_ONLY" = false ]; then
    if [ -z "$LEAN_LIB_DIR" ]; then
        usage >&2
        exit 1
    fi

    if [ ! -d "$LEAN_LIB_DIR" ]; then
        echo "Error: lean lib directory not found: $LEAN_LIB_DIR" >&2
        exit 1
    fi
fi

# ---- Derive version tag from workspace Cargo.toml ---------------------------
if [ -z "$TAG" ]; then
    VERSION=$(grep -m1 '^version' Cargo.toml | sed 's/.*"\(.*\)".*/\1/')
    if [ "$NATIVE_ONLY" = true ]; then
        TAG="Clean-native-v${VERSION}"
    else
        TAG="mathverse-v${VERSION}"
    fi
fi

case "$TAG" in
mathverse-v*) RELEASE_VERSION="${TAG#mathverse-v}" ;;
Clean-native-v*) RELEASE_VERSION="${TAG#Clean-native-v}" ;;
v*) RELEASE_VERSION="${TAG#v}" ;;
*) RELEASE_VERSION="$TAG" ;;
esac

ARCHIVE_NAME="mathverse-library-v${RELEASE_VERSION}.tar.zst"
ARCHIVE_PATH="target/${ARCHIVE_NAME}"

echo "=== Mathverse Shard Release ==="
if [ "$NATIVE_ONLY" = true ]; then
    echo "  Mode:          native-only (Clean-Native shard)"
else
    echo "  Lean lib dir:  $LEAN_LIB_DIR"
fi
echo "  Output dir:    $OUTPUT_DIR"
echo "  Release tag:   $TAG"
echo "  Archive:       $ARCHIVE_PATH"
echo

# ---- Step 1: Build mathverse_shard binary in release mode ------------------------
echo "--- Building mathverse_shard (release) ---"
cargo build --locked --release -p clean-mathverse --bin mathverse_shard --message-format=short -j "$CARGO_BUILD_JOBS"
# Cargo wrapper redirects release artifacts into target/user/release (#2380);
# fall back to the stock target/release path if the user-dir layout is absent.
MATHVERSE_SHARD=""
for candidate in "target/user/release/mathverse_shard" "target/release/mathverse_shard"; do
    if [ -x "$candidate" ]; then
        MATHVERSE_SHARD="$candidate"
        break
    fi
done

if [ -z "$MATHVERSE_SHARD" ]; then
    echo "Error: mathverse_shard binary not found in target/user/release or target/release" >&2
    exit 1
fi
echo "  Binary: $MATHVERSE_SHARD"
echo

# ---- Step 2: Build shards ---------------------------------------------------
echo "--- Building mathverse shards ---"
if [ -n "$MODULES" ]; then
    EXTRA_BUILD_ARGS+=("--modules=$MODULES")
fi
if [ -n "$SHARD_SIZE" ]; then
    EXTRA_BUILD_ARGS+=("--shard-size=$SHARD_SIZE")
fi

rm -rf "$OUTPUT_DIR"
mkdir -p "$OUTPUT_DIR"

if [ "$NATIVE_ONLY" = true ]; then
    "$MATHVERSE_SHARD" build-native "$OUTPUT_DIR"
    echo
    echo "--- Running native shard gate ---"
    "$MATHVERSE_SHARD" verify-kernel --native "$OUTPUT_DIR"
else
    BUILD_ARGS=("$LEAN_LIB_DIR" "$OUTPUT_DIR")
    if [ -n "$VERBOSE" ]; then
        BUILD_ARGS+=("$VERBOSE")
    fi
    BUILD_ARGS+=("${EXTRA_BUILD_ARGS[@]}")
    "$MATHVERSE_SHARD" build "${BUILD_ARGS[@]}"
fi
echo

# ---- Step 3: Verify shards before packaging ---------------------------------
echo "--- Verifying shards ---"
"$MATHVERSE_SHARD" verify "$OUTPUT_DIR"
echo

# ---- Step 4: Package shards with release manifest ---------------------------
echo "--- Packaging shards ---"
"${REPO_ROOT}/scripts/package_mathverse_release.sh" "$OUTPUT_DIR" \
    "--version=${RELEASE_VERSION}" \
    --output-dir=target

ARCHIVE_SIZE=$(stat -f%z "$ARCHIVE_PATH" 2>/dev/null || stat -c%s "$ARCHIVE_PATH" 2>/dev/null)
echo "  Archive: $ARCHIVE_PATH ($(format_size_mb "$ARCHIVE_SIZE") MB)"
echo

# ---- Step 5: Create GitHub release ------------------------------------------
if [ "$DRY_RUN" = true ]; then
    echo "--- Dry run: skipping GitHub release ---"
    echo "  Would create release: $TAG"
    echo "  Would upload: $ARCHIVE_PATH"
    echo
    echo "To create the release manually:"
    echo "  gh release create '$TAG' '$ARCHIVE_PATH' \\"
    echo "    --title 'Mathverse Library Shards $TAG' \\"
    echo "    --notes 'Pre-built mathverse shards for Clean.'"
    exit 0
fi

echo "--- Creating GitHub release ---"
if ! command -v gh >/dev/null 2>&1; then
    echo "Error: gh CLI not found. Install: brew install gh" >&2
    exit 1
fi

# Check if tag already exists
if gh release view "$TAG" >/dev/null 2>&1; then
    echo "  Release $TAG already exists. Uploading asset to existing release..."
    gh release upload "$TAG" "$ARCHIVE_PATH" --clobber
else
    COMMIT_SHA=$(git rev-parse HEAD)
    NOTES_FILE=$(mktemp)
    OUTPUT_BASE=$(basename "$OUTPUT_DIR")
    trap 'rm -f "$NOTES_FILE"' EXIT
    cat >"$NOTES_FILE" <<NOTES_EOF
Pre-built mathverse shards for Clean.

Built from commit ${COMMIT_SHA}.

## Usage

    ./scripts/download_mathverse_library.sh --version='${RELEASE_VERSION}'

Or manually:

    gh release download '${TAG}' --pattern '${ARCHIVE_NAME}'
    tar --zstd -xf ${ARCHIVE_NAME}
    mathverse_shard verify ${OUTPUT_BASE}/
NOTES_EOF
    gh release create "$TAG" "$ARCHIVE_PATH" \
        --title "Mathverse Library Shards $TAG" \
        --notes-file "$NOTES_FILE"
fi

echo

# ---- Step 6: Mirror to target repo (optional) --------------------------------
if [ "$MIRROR" = true ]; then
    echo "--- Mirroring release to $MIRROR_REPO ---"
    MIRROR_SCRIPT="${REPO_ROOT}/scripts/publish_mathverse_mirror.sh"
    if [ ! -x "$MIRROR_SCRIPT" ]; then
        echo "Error: mirror script not found at $MIRROR_SCRIPT" >&2
        exit 1
    fi
    MIRROR_ARGS=("--tag=$TAG" "--target-repo=$MIRROR_REPO")
    if [ "$DRY_RUN" = true ]; then
        MIRROR_ARGS+=("--dry-run")
    fi
    "$MIRROR_SCRIPT" "${MIRROR_ARGS[@]}"
    echo
fi

echo "=== Release complete: $TAG ==="
