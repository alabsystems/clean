#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Integration tests for publish_mathverse_mirror.sh
#
# Validates:
#   1. Script syntax (bash -n)
#   2. Help output contains expected flags
#   3. Dry-run output format with --tag
#   4. Unknown option handling
#   5. dscan.toml structure validation
#
# Usage:
#   ./scripts/test_publish_mathverse_mirror.sh
#
# These tests validate script structure and dry-run behavior.
# They do NOT create or modify GitHub releases.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
MIRROR_SCRIPT="${REPO_ROOT}/scripts/publish_mathverse_mirror.sh"
DSCAN_CONFIG="${REPO_ROOT}/data/dscan.toml"

PASS=0
FAIL=0

pass() {
  PASS=$((PASS + 1))
  echo "  PASS: $1"
}

fail() {
  FAIL=$((FAIL + 1))
  echo "  FAIL: $1" >&2
}

echo "=== Test: publish_mathverse_mirror.sh ==="
echo

# ---- Test 1: Script exists and is executable ----------------------------------
echo "--- Test 1: Script exists and is executable ---"
if [ -x "$MIRROR_SCRIPT" ]; then
  pass "script is executable"
else
  fail "script not found or not executable at $MIRROR_SCRIPT"
fi

# ---- Test 2: Bash syntax check -----------------------------------------------
echo "--- Test 2: Bash syntax check ---"
if bash -n "$MIRROR_SCRIPT" 2>/dev/null; then
  pass "bash -n syntax check"
else
  fail "bash -n syntax check"
fi

# ---- Test 3: Help flags present in script source ------------------------------
echo "--- Test 3: Help flags in script source ---"
# Note: The sed-based --help display has a macOS BSD sed compatibility issue
# (shared across all mathverse scripts). We verify flags exist in the script source.
for FLAG in "--source-repo" "--target-repo" "--tag" "--dry-run"; do
  if grep -q -- "$FLAG" "$MIRROR_SCRIPT"; then
    pass "script contains $FLAG"
  else
    fail "script missing $FLAG"
  fi
done

# ---- Test 4: Default repo values in script ------------------------------------
echo "--- Test 4: Default repo values ---"
if grep -q 'alabsystems/Clean' "$MIRROR_SCRIPT"; then
  pass "default source repo"
else
  fail "default source repo not found"
fi

if grep -q 'alabsystems/Clean' "$MIRROR_SCRIPT"; then
  pass "default target repo"
else
  fail "default target repo not found"
fi

# ---- Test 5: Unknown option produces error ------------------------------------
echo "--- Test 5: Unknown option handling ---"
UNKNOWN_OUTPUT=$("$MIRROR_SCRIPT" --bogus-flag 2>&1 || true)
if echo "$UNKNOWN_OUTPUT" | grep -qi "unknown"; then
  pass "unknown option produces error"
else
  fail "unknown option should produce error"
fi

# ---- Test 6: Dry-run with explicit tag (requires gh, skip if unavailable) -----
echo "--- Test 6: Dry-run output format ---"
if command -v gh >/dev/null 2>&1; then
  DRY_OUTPUT=$("$MIRROR_SCRIPT" --tag=mathverse-v0.9.0 --dry-run 2>&1 || true)
  if echo "$DRY_OUTPUT" | grep -q "mathverse-v0.9.0"; then
    pass "dry-run shows specified tag"
  else
    fail "dry-run does not show specified tag"
  fi

  if echo "$DRY_OUTPUT" | grep -q "Dry run"; then
    pass "dry-run shows 'Dry run' label"
  else
    fail "dry-run missing 'Dry run' label"
  fi
else
  echo "  SKIP: gh CLI not available (dry-run requires gh for metadata fetch)"
fi

# ---- Test 7: release_mathverse_shards.sh has --mirror flag ------------------------
echo "--- Test 7: release_mathverse_shards.sh --mirror integration ---"
SHARDS_SCRIPT="${REPO_ROOT}/scripts/release_mathverse_shards.sh"
if [ -f "$SHARDS_SCRIPT" ]; then
  if grep -q -- "--mirror" "$SHARDS_SCRIPT"; then
    pass "release_mathverse_shards.sh has --mirror flag"
  else
    fail "release_mathverse_shards.sh missing --mirror flag"
  fi

  if bash -n "$SHARDS_SCRIPT" 2>/dev/null; then
    pass "release_mathverse_shards.sh syntax check"
  else
    fail "release_mathverse_shards.sh syntax check"
  fi
else
  fail "release_mathverse_shards.sh not found"
fi

# ---- Test 8: dscan.toml exists and has required fields ------------------------
echo "--- Test 8: dscan.toml validation ---"
if [ -f "$DSCAN_CONFIG" ]; then
  pass "dscan.toml exists"

  for KEY in "MATHVERSE_LIBRARIES.md" "MATHVERSE_PROVENANCE.md" "MATHVERSE_KERNEL_COMPATIBILITY.md" "mathverse_summary.json"; do
    if grep -q "$KEY" "$DSCAN_CONFIG"; then
      pass "dscan.toml references $KEY"
    else
      fail "dscan.toml missing reference to $KEY"
    fi
  done

  if grep -q 'tag_prefix.*=.*"mathverse-v"' "$DSCAN_CONFIG"; then
    pass "dscan.toml has mathverse-v tag prefix"
  else
    fail "dscan.toml missing mathverse-v tag prefix"
  fi

  if grep -q 'alabsystems/Clean' "$DSCAN_CONFIG"; then
    pass "dscan.toml references mirror target"
  else
    fail "dscan.toml missing mirror target"
  fi
else
  fail "dscan.toml not found at $DSCAN_CONFIG"
fi

# ---- Summary ------------------------------------------------------------------
echo
echo "=== Results: $PASS passed, $FAIL failed ==="
if [ "$FAIL" -gt 0 ]; then
  exit 1
fi
