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
#   3. Dry-run output format with --tag, against a mock gh
#   4. Unknown option handling
#   5. dscan.toml structure validation
#
# Usage:
#   ./scripts/test_publish_mathverse_mirror.sh
#
# These tests validate script structure and dry-run behavior.
# They do NOT create or modify GitHub releases, and they do not reach the
# network: the dry run talks to a mock gh on PATH. (Until 2026-10-28 it ran the
# real gh against a release that does not exist, so it failed wherever gh was
# installed -- and, had the release existed, a "dry run" would have downloaded
# every release asset.)

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
MIRROR_SCRIPT="${REPO_ROOT}/scripts/publish_mathverse_mirror.sh"
DSCAN_CONFIG="${REPO_ROOT}/data/dscan.toml"
RELEASE_RS="${REPO_ROOT}/crates/clean-mathverse/src/release.rs"

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
# The canonical slug is the one the Mathverse release code downloads from,
# `DEFAULT_CLEAN_RELEASE_REPO` in crates/clean-mathverse/src/release.rs. The
# script's defaults were normalised to it (lowercase) in be06dd6f8; this test
# had kept the earlier `alabsystems/Clean` and so failed from that commit on.
# Each default is checked on its own assignment line, not by one grep that
# either line satisfies.
echo "--- Test 4: Default repo values ---"
CANON_REPO="$(sed -n 's/^pub const DEFAULT_CLEAN_RELEASE_REPO: &str = "\([^"]*\)";$/\1/p' "$RELEASE_RS" 2>/dev/null | head -1)"
if [ -n "$CANON_REPO" ]; then
  pass "canonical release repo read from release.rs ($CANON_REPO)"
else
  fail "could not read DEFAULT_CLEAN_RELEASE_REPO from $RELEASE_RS"
  CANON_REPO="<unreadable>"
fi

if grep -Fqx "SOURCE_REPO=\"$CANON_REPO\"" "$MIRROR_SCRIPT"; then
  pass "default source repo"
else
  fail "default source repo not found"
fi

if grep -Fqx "TARGET_REPO=\"$CANON_REPO\"" "$MIRROR_SCRIPT"; then
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

# ---- Test 6: Dry-run with explicit tag, against a mock gh ---------------------
# The mock answers the source release's metadata and download, reports that the
# target release does not exist, and logs every call, so the dry run is checked
# end to end without the network and without modifying anything.
echo "--- Test 6: Dry-run output format ---"
TMP_DIR="$(mktemp -d -t publish_mirror_test.XXXXXX)"
# macOS /bin/bash 3.2, which check_script_selftests.sh runs this under, exits 0
# when an expansion error (an unbound variable under `set -u`, or `${X:?}`)
# aborts a `set -e` script that has an EXIT trap, so a crash after this line
# would read as a pass with no summary. Any exit before the summary is 70.
SUITE_DONE=0
on_exit() {
  rm -rf "$TMP_DIR"
  if [ "$SUITE_DONE" != 1 ]; then
    echo "  FAIL: the suite stopped before its summary line (exit 70)" >&2
    exit 70
  fi
}
trap on_exit EXIT
MOCK_BIN="$TMP_DIR/bin"
GH_LOG="$TMP_DIR/gh.log"
mkdir -p "$MOCK_BIN"
: >"$GH_LOG"
cat >"$MOCK_BIN/gh" <<MOCK_GH
#!/usr/bin/env bash
set -euo pipefail
printf '%s\\n' "\$*" >> "$GH_LOG"
repo=""; json=""; dir=""; prev=""
for a in "\$@"; do
  case "\$prev" in
    --repo) repo="\$a" ;;
    --json) json="\$a" ;;
    --dir) dir="\$a" ;;
  esac
  prev="\$a"
done
case "\${1:-} \${2:-}" in
  'release view')
    if [ "\$repo" = example/src ]; then
      case "\$json" in
        name) echo 'Mathverse v0.9.0' ;;
        body) echo 'release notes' ;;
        assets) echo 1 ;;
        *) echo 'unexpected --json for the source' >&2; exit 1 ;;
      esac
      exit 0
    fi
    echo 'release not found' >&2; exit 1 ;;
  'release download')
    [ "\$repo" = example/src ] && [ -n "\$dir" ] || exit 1
    printf '{}' > "\$dir/mathverse_summary.json"; exit 0 ;;
esac
echo "unexpected gh call: \$*" >&2
exit 1
MOCK_GH
chmod +x "$MOCK_BIN/gh"

set +e
DRY_OUTPUT="$(PATH="$MOCK_BIN:$PATH" "$MIRROR_SCRIPT" --source-repo=example/src \
  --target-repo=example/dst --tag=mathverse-v0.9.0 --dry-run 2>&1)"
DRY_STATUS=$?
set -e

if [ "$DRY_STATUS" -eq 0 ]; then
  pass "dry-run exits 0"
else
  fail "dry-run exited $DRY_STATUS: $(printf '%s' "$DRY_OUTPUT" | tail -1)"
fi

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

if echo "$DRY_OUTPUT" | grep -Fq "Would create release: example/dst@mathverse-v0.9.0" &&
  echo "$DRY_OUTPUT" | grep -Fq "Would upload assets:  1"; then
  pass "dry-run names the target release and the asset count"
else
  fail "dry-run does not name the target release and the asset count"
fi

# Every call the mock logged must be a read (`release list`, `view` or
# `download`). A list of mutating verbs would miss `release delete-asset`,
# `gh api -X POST` or a verb added later, each passing with `|| true`; a count,
# not a captured list, so a logged call with no arguments (an empty line) counts.
NON_READS="$(grep -Evc '^release (list|view|download) ' "$GH_LOG" || true)"
if [ "$NON_READS" != 0 ]; then
  fail "dry-run made $NON_READS gh call(s) that are not a read: $(grep -Ev '^release (list|view|download) ' "$GH_LOG" | head -1)"
elif grep -Fqx 'release view mathverse-v0.9.0 --repo example/dst' "$GH_LOG"; then
  pass "dry-run only read: it probed the target and changed nothing"
else
  fail "dry-run never probed the target release (gh log: $(tr '\n' ';' <"$GH_LOG"))"
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

  # The [mirror] stanza's target, held to the same canonical slug as the
  # script's defaults (Test 4); `alabsystems/Clean` here was stale since
  # dscan.toml's slug went lowercase (8c89e9bcd, carried by 38b85b641).
  if grep -Fqx "target_repo = \"$CANON_REPO\"" "$DSCAN_CONFIG"; then
    pass "dscan.toml references mirror target"
  else
    fail "dscan.toml missing mirror target"
  fi
else
  fail "dscan.toml not found at $DSCAN_CONFIG"
fi

# ---- Summary ------------------------------------------------------------------
SUITE_DONE=1
echo
echo "=== Results: $PASS passed, $FAIL failed ==="
if [ "$FAIL" -gt 0 ]; then
  exit 1
fi
