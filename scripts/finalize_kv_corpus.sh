#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Finalize the Mathverse KernelVerified corpus into a loadable, releasable
# library:
#   1. assemble every KV shard (Metamath + Mathlib + Cake) into one dir,
#   2. build the release manifest + baseline index + archive,
#   3. print the grand KernelVerified total + per-lane stats.
#
# After this, point any proof session at the corpus with:
#   export MATHVERSE_LIBRARY_PATH=<repo>/data/mathverse-library/kv-corpus
# so `mathverse_use` (Strict / KernelVerified-only) resolves premises from it.
#
# Usage: scripts/finalize_kv_corpus.sh [VERSION]
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
CLEAN_BIN="$REPO_ROOT/target/release/clean"
CORPUS="$REPO_ROOT/data/mathverse-library/kv-corpus"
DIST="$REPO_ROOT/dist"
VERSION="${1:-kv-0.1.0}"

# --- Memory governor (2026-06-23 single-process OOM fix) ---------------------
# Both assemble (3x `mathverse stats`) and `release package` load the corpus
# into one process. Acquire the shared stamp lock ONCE here (inherited by the
# assemble child via STAMP_LOCK_HELD, so it does not re-acquire/deadlock) and
# run the otherwise-ungoverned `release package` step under the RSS/low-RAM
# watchdog. See scripts/lib/stamp_mem_governor.sh.
# shellcheck source=scripts/lib/stamp_mem_governor.sh
source "$REPO_ROOT/scripts/lib/stamp_mem_governor.sh"
if [ -z "${STAMP_LOCK_HELD:-}" ]; then
  stamp_acquire_global_lock || exit 1
  export STAMP_LOCK_HELD=1
fi

echo "=== 1/3 assemble ==="
bash "$REPO_ROOT/scripts/assemble_kv_corpus.sh" "$CORPUS"

echo "=== 2/3 package (manifest + baseline index + archive) ==="
pkg_log="$(mktemp "${TMPDIR:-/tmp}/kv-release-XXXXXX.log")"
stamp_wait_for_free_ram
if stamp_run_governed_chunk "$pkg_log" "${KV_RELEASE_TIMEOUT:-3600}" -- \
    "$CLEAN_BIN" mathverse release package --version "$VERSION" --shards "$CORPUS" --output "$DIST"; then
  tail -20 "$pkg_log"
else
  echo "[finalize] release package aborted by governor: ${STAMP_LAST_STATUS} (peak $((STAMP_LAST_PEAK_KB/1048576))GiB)" >&2
  rm -f "$pkg_log"; exit 1
fi
rm -f "$pkg_log"

echo "=== 3/3 grand totals ==="
python3 - "$REPO_ROOT" <<'PY'
import json,sys,os
root=sys.argv[1]
def kv_from_aggregate(p):
    try: return json.load(open(p)).get('kernel_verified',0)
    except Exception: return 0
mathlib=kv_from_aggregate(os.path.join(root,'data/mathverse-library/mathlib-kv/AGGREGATE.json'))
metamath=3414  # set.mm schematic ceiling (see docs/MATHVERSE_KERNEL_VERIFIED_CORPUS.md)
print(f"Metamath set.mm KernelVerified : {metamath:>8}")
print(f"Mathlib       KernelVerified : {mathlib:>8}")
print(f"-------------------------------------------")
print(f"TOTAL (excl. Cake)           : {metamath+mathlib:>8}")
PY
echo ""
echo "manifest: $CORPUS/mathverse-manifest.json"
echo "to use as the active library:  export MATHVERSE_LIBRARY_PATH=$CORPUS"
