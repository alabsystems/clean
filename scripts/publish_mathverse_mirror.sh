#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Mirror an mathverse GitHub Release from a source repository to a target
# repository, keeping the release title, notes, and assets in sync.
#
# Usage:
#   ./scripts/publish_mathverse_mirror.sh [options]
#
# Options:
#   --source-repo=REPO   Source repository (default: alabsystems/clean)
#   --target-repo=REPO   Target repository (default: alabsystems/clean)
#   --tag=TAG            Mirror a specific release tag (default: latest mathverse-v*)
#   --dry-run            Show what would happen without modifying the target repo
#   --help|-h            Show this help text
#
# Prerequisites:
#   - gh CLI (authenticated) with access to both repositories

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

# ---- Defaults ---------------------------------------------------------------
SOURCE_REPO="alabsystems/clean"
TARGET_REPO="alabsystems/clean"
TAG=""
DRY_RUN=false

# ---- Parse args --------------------------------------------------------------
for arg in "$@"; do
  case "$arg" in
    --source-repo=*) SOURCE_REPO="${arg#--source-repo=}" ;;
    --target-repo=*) TARGET_REPO="${arg#--target-repo=}" ;;
    --tag=*)         TAG="${arg#--tag=}" ;;
    --dry-run)       DRY_RUN=true ;;
    --help|-h)
      sed -n '2,/^$/{ s/^# //; s/^#$//; p }' "$0"
      exit 0
      ;;
    *)
      echo "Unknown option: $arg" >&2
      exit 1
      ;;
  esac
done

if ! command -v gh >/dev/null 2>&1; then
  echo "Error: gh CLI not found. Install: brew install gh" >&2
  exit 1
fi

WORK_DIR=$(mktemp -d)
ASSET_DIR="${WORK_DIR}/assets"
NOTES_FILE="${WORK_DIR}/release-notes.md"
mkdir -p "$ASSET_DIR"

cleanup() {
  rm -rf "$WORK_DIR"
}
trap cleanup EXIT

echo "=== Publish Mathverse Mirror ==="
echo "  Source repo:  $SOURCE_REPO"
echo "  Target repo:  $TARGET_REPO"
echo

# ---- Step 1: Resolve source release tag -------------------------------------
echo "--- Resolving source release tag ---"
if [ -z "$TAG" ]; then
  TAG=$(gh release list \
    --repo "$SOURCE_REPO" \
    --limit 100 \
    --exclude-drafts \
    --json tagName \
    --jq '[.[] | select(.tagName | startswith("mathverse-v"))][0].tagName // empty')
  if [ -z "$TAG" ]; then
    echo "Error: no mathverse-v* release found for $SOURCE_REPO" >&2
    exit 1
  fi
fi
echo "  Release tag:  $TAG"
echo

# ---- Step 2: Fetch source release metadata ----------------------------------
echo "--- Fetching source release metadata ---"
TITLE=$(gh release view "$TAG" --repo "$SOURCE_REPO" --json name --jq '.name // ""')
gh release view "$TAG" --repo "$SOURCE_REPO" --json body --jq '.body // ""' > "$NOTES_FILE"
SOURCE_ASSET_COUNT=$(gh release view "$TAG" --repo "$SOURCE_REPO" --json assets --jq '.assets | length')
echo "  Title:         ${TITLE:-<empty>}"
echo "  Source assets: $SOURCE_ASSET_COUNT"
echo

# ---- Step 3: Download source release assets ---------------------------------
echo "--- Downloading source release assets ---"
if [ "$SOURCE_ASSET_COUNT" -gt 0 ]; then
  gh release download "$TAG" --repo "$SOURCE_REPO" --dir "$ASSET_DIR"
else
  echo "  No source assets to download."
fi

ASSET_FILES=()
shopt -s nullglob
for asset_file in "$ASSET_DIR"/*; do
  if [ -f "$asset_file" ]; then
    ASSET_FILES+=("$asset_file")
  fi
done
shopt -u nullglob

DOWNLOADED_ASSET_COUNT="${#ASSET_FILES[@]}"
echo "  Downloaded assets: $DOWNLOADED_ASSET_COUNT"
if [ "$DOWNLOADED_ASSET_COUNT" -ne "$SOURCE_ASSET_COUNT" ]; then
  echo "Error: downloaded asset count ($DOWNLOADED_ASSET_COUNT) does not match source asset count ($SOURCE_ASSET_COUNT)" >&2
  exit 1
fi
echo

# ---- Step 4: Check target release state -------------------------------------
echo "--- Checking target release state ---"
TARGET_EXISTS=false
if gh release view "$TAG" --repo "$TARGET_REPO" >/dev/null 2>&1; then
  TARGET_EXISTS=true
  echo "  Target release exists and will be updated."
else
  echo "  Target release does not exist and will be created."
fi
echo

# ---- Step 5: Dry run --------------------------------------------------------
if [ "$DRY_RUN" = true ]; then
  echo "--- Dry run: no changes applied ---"
  if [ "$TARGET_EXISTS" = true ]; then
    echo "  Would update release: $TARGET_REPO@$TAG"
  else
    echo "  Would create release: $TARGET_REPO@$TAG"
  fi
  echo "  Would mirror title:   ${TITLE:-<empty>}"
  echo "  Would mirror notes:   $(basename "$NOTES_FILE")"
  echo "  Would upload assets:  $DOWNLOADED_ASSET_COUNT"
  for asset_file in "${ASSET_FILES[@]}"; do
    echo "    $(basename "$asset_file")"
  done
  exit 0
fi

# ---- Step 6: Create or update target release --------------------------------
echo "--- Creating or updating target release ---"
if [ "$TARGET_EXISTS" = true ]; then
  gh release edit "$TAG" \
    --repo "$TARGET_REPO" \
    --title "$TITLE" \
    --notes-file "$NOTES_FILE"
  echo "  Updated release metadata."
else
  gh release create "$TAG" \
    --repo "$TARGET_REPO" \
    --title "$TITLE" \
    --notes-file "$NOTES_FILE"
  echo "  Created release."
fi
echo

# ---- Step 7: Upload assets --------------------------------------------------
echo "--- Uploading assets to target release ---"
if [ "$DOWNLOADED_ASSET_COUNT" -gt 0 ]; then
  gh release upload "$TAG" --repo "$TARGET_REPO" --clobber "${ASSET_FILES[@]}"
  echo "  Uploaded assets: $DOWNLOADED_ASSET_COUNT"
else
  echo "  No assets to upload."
fi
echo

# ---- Step 8: Verify target asset count --------------------------------------
echo "--- Verifying mirrored release ---"
TARGET_ASSET_COUNT=$(gh release view "$TAG" --repo "$TARGET_REPO" --json assets --jq '.assets | length')
echo "  Source assets:     $SOURCE_ASSET_COUNT"
echo "  Downloaded assets: $DOWNLOADED_ASSET_COUNT"
echo "  Target assets:     $TARGET_ASSET_COUNT"

if [ "$TARGET_ASSET_COUNT" -ne "$SOURCE_ASSET_COUNT" ]; then
  echo "Error: target asset count ($TARGET_ASSET_COUNT) does not match source asset count ($SOURCE_ASSET_COUNT)" >&2
  exit 1
fi

echo
echo "=== Mirror complete: $TARGET_REPO@$TAG ==="
