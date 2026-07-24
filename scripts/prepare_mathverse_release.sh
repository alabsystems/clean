#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Prepare an Mathverse Library release for a given version.
#
# This script validates the codebase, runs tests, builds shards, runs shard
# verification, packages into tar.zst with manifest, runs a final locked cargo
# check, generates release notes from git log since the last tag, and outputs
# summary statistics.
#
# Usage:
#   ./scripts/prepare_mathverse_release.sh <version> [options]
#
# Arguments:
#   version              Target version (e.g., 1.1.0)
#
# Options:
#   --skip-tests         Skip running cargo test (for re-runs after tests pass)
#   --skip-build         Skip release build/check (for re-runs after build succeeds)
#   --skip-shards        Skip shard building (use existing shards)
#   --lean-lib-dir=DIR   Lean 4 library directory for .olean shard building
#   --shard-dir=DIR      Existing shard directory (default: data/mathverse-shards)
#   --data-dir=DIR       Data dir whose raw/ holds cloned upstream sources for
#                        the multi-system corpus build (default: /tmp/mathverse-data;
#                        populate via scripts/download_all_libraries.sh)
#   --output-dir=DIR     Output directory for changelog and archive (default: target/)
#   --dry-run            Show what would be done without executing
#
# Prerequisites:
#   - Rust toolchain (cargo)
#   - git (for changelog generation)
#   - b3sum (brew install b3sum) for shard verification
#   - zstd (brew install zstd) for archive compression
#
# After running this script:
#   1. Review the generated changelog at target/mathverse_v<version>_changelog.md
#   2. Run: ./scripts/release_mathverse_shards.sh <lean-lib-dir> --tag=mathverse-v<version>
#
# Examples:
#   ./scripts/prepare_mathverse_release.sh 1.1.0
#   ./scripts/prepare_mathverse_release.sh 1.1.0 --skip-tests --dry-run
#   ./scripts/prepare_mathverse_release.sh 1.1.0 --lean-lib-dir=~/.elan/toolchains/leanprover--lean4---v4.13.0/lib/lean

set -euo pipefail

export CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-1}"

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

usage() {
    cat <<'USAGE'
Prepare an Mathverse Library release for a given version.

Usage:
  ./scripts/prepare_mathverse_release.sh <version> [options]

Arguments:
  version              Target version (e.g., 1.1.0)

Options:
  --skip-tests         Skip running cargo test (for re-runs after tests pass)
  --skip-build         Skip release build/check (for re-runs after build succeeds)
  --skip-shards        Skip shard building (use existing shards)
  --lean-lib-dir=DIR   Lean 4 library directory for .olean shard building
  --shard-dir=DIR      Existing shard directory (default: data/mathverse-shards)
  --data-dir=DIR       Data dir whose raw/ holds cloned upstream sources
                       (default: /tmp/mathverse-data; populate via
                       scripts/download_all_libraries.sh)
  --output-dir=DIR     Output directory for changelog and archive (default: target/)
  --dry-run            Show what would be done without executing
  --help, -h           Show this help

Prerequisites:
  - Rust toolchain (cargo)
  - git (for changelog generation)
  - b3sum (brew install b3sum) for shard verification
  - zstd (brew install zstd) for archive compression

Examples:
  ./scripts/prepare_mathverse_release.sh 1.1.0
  ./scripts/prepare_mathverse_release.sh 1.1.0 --skip-tests --dry-run
  ./scripts/prepare_mathverse_release.sh 1.1.0 --lean-lib-dir=~/.elan/toolchains/leanprover--lean4---v4.13.0/lib/lean
USAGE
}

# ---- Defaults ---------------------------------------------------------------
TARGET_VERSION=""
SKIP_TESTS=false
SKIP_BUILD=false
SKIP_SHARDS=false
LEAN_LIB_DIR=""
SHARD_DIR="data/mathverse-shards"
# Data dir whose raw/ subtree holds the cloned upstream sources for the
# multi-system corpus build (mathverse_convert all reads <data-dir>/raw/).
# Populate it first with scripts/download_all_libraries.sh "$DATA_DIR".
DATA_DIR="/tmp/mathverse-data"
OUTPUT_DIR="target"
DRY_RUN=false

# ---- Parse args --------------------------------------------------------------
for arg in "$@"; do
    case "$arg" in
    --skip-tests) SKIP_TESTS=true ;;
    --skip-build) SKIP_BUILD=true ;;
    --skip-shards) SKIP_SHARDS=true ;;
    --lean-lib-dir=*) LEAN_LIB_DIR="${arg#--lean-lib-dir=}" ;;
    --shard-dir=*) SHARD_DIR="${arg#--shard-dir=}" ;;
    --data-dir=*) DATA_DIR="${arg#--data-dir=}" ;;
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
        if [ -z "$TARGET_VERSION" ]; then
            TARGET_VERSION="$arg"
        else
            echo "Unexpected argument: $arg" >&2
            exit 1
        fi
        ;;
    esac
done

if [ -z "$TARGET_VERSION" ]; then
    usage >&2
    exit 1
fi

CURRENT_VERSION=$(grep -m1 '^version' Cargo.toml | sed 's/.*"\(.*\)".*/\1/')
CHANGELOG_PATH="${OUTPUT_DIR}/mathverse_v${TARGET_VERSION}_changelog.md"
TAG="mathverse-v${TARGET_VERSION}"
ARCHIVE_NAME="mathverse-library-v${TARGET_VERSION}.tar.zst"
ARCHIVE_PATH="${OUTPUT_DIR}/${ARCHIVE_NAME}"

# Derive the previous tag for changelog generation
PREV_TAG=$(git tag --list 'mathverse-v*' --sort=-version:refname | head -1 || echo "")
if [ -z "$PREV_TAG" ]; then
    # Fall back to date-based log if no prior tags exist
    PREV_TAG=""
fi

TOTAL_STEPS=7
STEP=0
ERRORS=0

echo "=== Mathverse Library v${TARGET_VERSION} Release Preparation ==="
echo "  Current version: ${CURRENT_VERSION}"
echo "  Target version:  ${TARGET_VERSION}"
echo "  Previous tag:    ${PREV_TAG:-none (using date since 2026-04-01)}"
echo "  Changelog:       ${CHANGELOG_PATH}"
echo "  Archive:         ${ARCHIVE_PATH}"
echo

if [ "$DRY_RUN" = true ]; then
    echo "--- Dry run mode: showing steps without executing ---"
    echo
    echo "Would run:"
    echo "  1. cargo test --locked -p clean-mathverse --lib --message-format=short -j $CARGO_BUILD_JOBS"
    echo "  2. cargo build --locked -p clean-mathverse --release --message-format=short -j $CARGO_BUILD_JOBS"
    echo "  3. cargo check --locked -p clean-mathverse --message-format=short -j $CARGO_BUILD_JOBS"
    echo "  4. Build shards (lean4 .olean, Clean-native, structured importers)"
    echo "  5. Verify shards (blake3 checksums)"
    echo "  6. Package into tar.zst with manifest"
    echo "  7. Generate release notes at ${CHANGELOG_PATH}"
    exit 0
fi

# ---- Step 1: Run library tests ----------------------------------------------
STEP=$((STEP + 1))
if [ "$SKIP_TESTS" = true ]; then
    echo "--- Skipping tests (--skip-tests) ---"
    echo
else
    echo "--- Step ${STEP}/${TOTAL_STEPS}: Running clean-mathverse library tests ---"
    if cargo test --locked -p clean-mathverse --lib --message-format=short -j "$CARGO_BUILD_JOBS" 2>&1; then
        echo "  PASS: All clean-mathverse lib tests passed"
    else
        echo "  FAIL: Some clean-mathverse lib tests failed" >&2
        ERRORS=$((ERRORS + 1))
    fi
    echo
fi

# ---- Step 2-3: Release build and final cargo check --------------------------
STEP=$((STEP + 1))
if [ "$SKIP_BUILD" = true ]; then
    echo "--- Skipping build/check (--skip-build) ---"
    echo
else
    echo "--- Step ${STEP}/${TOTAL_STEPS}: Building clean-mathverse in release mode ---"
    if cargo build --locked -p clean-mathverse --release --message-format=short -j "$CARGO_BUILD_JOBS" 2>&1; then
        echo "  PASS: Release build succeeded"
    else
        echo "  FAIL: Release build failed" >&2
        ERRORS=$((ERRORS + 1))
    fi
    echo
    STEP=$((STEP + 1))
    echo "--- Step ${STEP}/${TOTAL_STEPS}: Final clean-mathverse cargo check ---"
    if cargo check --locked -p clean-mathverse --message-format=short -j "$CARGO_BUILD_JOBS" 2>&1; then
        echo "  PASS: cargo check succeeded"
    else
        echo "  FAIL: cargo check failed" >&2
        ERRORS=$((ERRORS + 1))
    fi
    echo
fi

# ---- Step 4: Build shards ---------------------------------------------------
STEP=$((STEP + 1))
if [ "$SKIP_SHARDS" = true ]; then
    echo "--- Skipping shard building (--skip-shards) ---"
    echo
else
    echo "--- Step ${STEP}/${TOTAL_STEPS}: Building mathverse shards ---"

    MATHVERSE_SHARD="target/release/mathverse_shard"
    if [ ! -x "$MATHVERSE_SHARD" ]; then
        echo "  Building mathverse_shard binary..."
        cargo build --locked --release -p clean-mathverse --bin mathverse_shard --message-format=short -j "$CARGO_BUILD_JOBS"
    fi

    # Build lean4 .olean shards if lean lib dir is specified
    if [ -n "$LEAN_LIB_DIR" ] && [ -d "$LEAN_LIB_DIR" ]; then
        SHARD_DIR="target/mathverse-shards-v${TARGET_VERSION}"
        rm -rf "$SHARD_DIR"
        mkdir -p "$SHARD_DIR"

        echo "  Building .olean shards from: $LEAN_LIB_DIR"
        "$MATHVERSE_SHARD" build "$LEAN_LIB_DIR" "$SHARD_DIR"
        echo "  PASS: Shard building complete"
    else
        echo "  No --lean-lib-dir specified; using existing shards at: $SHARD_DIR"
        if [ ! -d "$SHARD_DIR" ]; then
            echo "  WARNING: Shard directory not found: $SHARD_DIR" >&2
            echo "  Specify --lean-lib-dir=<dir> to build shards, or --shard-dir=<dir> for existing shards" >&2
        fi
    fi

    # Build the multi-system corpus (Lean4 olean + Metamath + OpenTheory +
    # structured importers). mathverse_convert all reads "$DATA_DIR/raw/" and
    # writes shards into "$DATA_DIR/raw/mathverse_shards" and
    # "$DATA_DIR/raw/mathverse_olean_shards" — NOT into "$SHARD_DIR" (the prior
    # version passed "$SHARD_DIR" here, so convert-all read a non-existent
    # "$SHARD_DIR/raw" and silently produced nothing).
    MATHVERSE_CONVERT="target/release/mathverse_convert"
    if [ ! -x "$MATHVERSE_CONVERT" ]; then
        cargo build --locked --release -p clean-mathverse --bin mathverse_convert --message-format=short -j "$CARGO_BUILD_JOBS" 2>/dev/null || true
    fi
    if [ -x "$MATHVERSE_CONVERT" ]; then
        if [ -d "$DATA_DIR/raw" ]; then
            echo "  Building corpus shards from raw sources at: $DATA_DIR/raw"
            "$MATHVERSE_CONVERT" all "$DATA_DIR" 2>&1 || echo "  WARNING: mathverse_convert all had non-zero exit" >&2
            # Collect produced shards into $SHARD_DIR for packaging.
            mkdir -p "$SHARD_DIR"
            for produced in "$DATA_DIR/raw/mathverse_shards" "$DATA_DIR/raw/mathverse_olean_shards"; do
                if [ -d "$produced" ]; then
                    find "$produced" -name '*.mathverse' -type f -exec cp -f {} "$SHARD_DIR/" \;
                fi
            done
        else
            echo "  WARNING: raw sources not found at $DATA_DIR/raw — skipping corpus build." >&2
            echo "           Run ./scripts/download_all_libraries.sh \"$DATA_DIR\" first," >&2
            echo "           or pass --data-dir=<dir> pointing at a populated raw/ tree." >&2
        fi
    else
        echo "  WARNING: mathverse_convert binary unavailable; skipping corpus build." >&2
    fi
    echo
fi

# ---- Step 5: Verify shards --------------------------------------------------
STEP=$((STEP + 1))
echo "--- Step ${STEP}/${TOTAL_STEPS}: Verifying shards (blake3 checksums) ---"
if [ -d "$SHARD_DIR" ]; then
    MATHVERSE_SHARD="${MATHVERSE_SHARD:-target/release/mathverse_shard}"
    if [ -x "$MATHVERSE_SHARD" ]; then
        if "$MATHVERSE_SHARD" verify "$SHARD_DIR" 2>&1; then
            echo "  PASS: All shards verified"
        else
            echo "  FAIL: Shard verification failed" >&2
            ERRORS=$((ERRORS + 1))
        fi
    else
        echo "  FAIL: mathverse_shard binary not available for verification" >&2
        ERRORS=$((ERRORS + 1))
    fi
else
    echo "  SKIP: No shard directory found at $SHARD_DIR"
fi
echo

# ---- Step 6: Package into tar.zst with manifest -----------------------------
STEP=$((STEP + 1))
echo "--- Step ${STEP}/${TOTAL_STEPS}: Packaging into tar.zst with manifest ---"
mkdir -p "$OUTPUT_DIR"

if [ -d "$SHARD_DIR" ]; then
    # Delegate to package_mathverse_release.sh
    PACKAGE_SCRIPT="${REPO_ROOT}/scripts/package_mathverse_release.sh"
    if [ -x "$PACKAGE_SCRIPT" ]; then
        "$PACKAGE_SCRIPT" "$SHARD_DIR" --version="$TARGET_VERSION" --output-dir="$OUTPUT_DIR"
        echo "  PASS: Archive created at ${ARCHIVE_PATH}"
    else
        echo "  SKIP: package_mathverse_release.sh not found"
    fi
else
    echo "  SKIP: No shards to package"
fi
echo

# ---- Step 7: Generate release notes from git log ----------------------------
STEP=$((STEP + 1))
echo "--- Step ${STEP}/${TOTAL_STEPS}: Generating release notes ---"

# Gather statistics
COMMIT_SHA=$(git rev-parse --short HEAD)
if [ -n "$PREV_TAG" ]; then
    COMMIT_COUNT=$(git log --oneline "${PREV_TAG}..HEAD" -- crates/clean-mathverse/ | wc -l | tr -d ' ')
else
    COMMIT_COUNT=$(git log --oneline --since="2026-04-01" -- crates/clean-mathverse/ | wc -l | tr -d ' ')
fi

SOURCE_SYSTEMS=$(grep -c '^\s\+\w\+ = [0-9]\+' crates/clean-mathverse/src/types.rs 2>/dev/null || echo "68")
TEST_FILE_COUNT=$(find crates/clean-mathverse/src -name '*test*' -o -name '*tests*' 2>/dev/null | wc -l | tr -d ' ')

# Count mathverse shard files if directory exists
SHARD_COUNT=0
if [ -d "$SHARD_DIR" ]; then
    SHARD_COUNT=$(find "$SHARD_DIR" -name '*.mathverse' -type f 2>/dev/null | wc -l | tr -d ' ')
fi

cat >"$CHANGELOG_PATH" <<CHANGELOG_EOF
# Mathverse Library v${TARGET_VERSION} Release Notes

**Release date:** $(date +%Y-%m-%d)
**Previous release:** ${PREV_TAG:-v1.0.0}
**Built from commit:** ${COMMIT_SHA}

---

## Highlights

CHANGELOG_EOF

# Append commit log
echo "### Commits since previous release" >>"$CHANGELOG_PATH"
echo "" >>"$CHANGELOG_PATH"
if [ -n "$PREV_TAG" ]; then
    git log --oneline "${PREV_TAG}..HEAD" -- crates/clean-mathverse/ >>"$CHANGELOG_PATH"
else
    git log --oneline --since="2026-04-01" -- crates/clean-mathverse/ >>"$CHANGELOG_PATH"
fi

cat >>"$CHANGELOG_PATH" <<CHANGELOG_EOF2

---

## Statistics

| Metric | Value |
|--------|-------|
| Commits since previous release | ${COMMIT_COUNT} |
| Source systems | ${SOURCE_SYSTEMS} |
| Mathverse shards | ${SHARD_COUNT} |
| Test files | ${TEST_FILE_COUNT} |
| Workspace version | ${CURRENT_VERSION} -> ${TARGET_VERSION} |

---

## Upgrade Guide

1. Download new shards: ./scripts/download_mathverse_library.sh --version=${TARGET_VERSION}
2. Verify integrity: CARGO_BUILD_JOBS=1 cargo run --locked --message-format=short -j 1 -p clean-mathverse --bin mathverse_shard -- verify data/mathverse-library/
3. Use the CLI: CARGO_BUILD_JOBS=1 cargo run --locked --message-format=short -j 1 -p clean-mathverse --bin mathverse -- stats

CHANGELOG_EOF2

echo "  Release notes written to: ${CHANGELOG_PATH}"
echo "  Commits since previous release: ${COMMIT_COUNT}"
echo

# ---- Summary -----------------------------------------------------------------
echo "=== Release Preparation Summary ==="
echo "  Version:  v${TARGET_VERSION}"
echo "  Tag:      ${TAG}"
echo "  Commit:   ${COMMIT_SHA}"
echo "  Shards:   ${SHARD_COUNT}"
echo

if [ "$ERRORS" -eq 0 ]; then
    echo "  Status: READY"
    echo "  All checks passed."
    echo
    echo "Next steps:"
    echo "  1. Review release notes: ${CHANGELOG_PATH}"
    echo "  2. Verify workspace version is ${TARGET_VERSION} in Cargo.toml"
    echo "  3. Build and release shards:"
    echo "     ./scripts/release_mathverse_shards.sh <lean-lib-dir> --tag=${TAG}"
    echo "  4. Or dry-run first:"
    echo "     ./scripts/release_mathverse_shards.sh <lean-lib-dir> --tag=${TAG} --dry-run"
else
    echo "  Status: NOT READY (${ERRORS} errors)"
    echo "  Fix the errors above before proceeding with the release."
    exit 1
fi
