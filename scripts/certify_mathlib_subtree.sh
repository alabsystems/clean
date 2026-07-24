#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# certify_mathlib_subtree.sh — reproducibly kernel-verify AND certify a Mathlib
# subtree, producing a P4 trust receipt (Merkle root + axiom basis) over the
# constants Clean's kernel accepted.
#
# This is the DURABLE reproduction of the receipts under designs/artifacts/: the
# root a receipt claims is a deterministic function of the kernel-verified
# content, so re-running this against the same Mathlib@<sha> reproduces the same
# root. The emitted leaves manifest lets anyone re-derive the root offline with
# only blake3 (`trust-receipt verify`) — no Mathlib, no kernel needed to CHECK.
#
# Usage:
#   scripts/certify_mathlib_subtree.sh <subtree> [out-dir] [source-id]
# e.g.
#   scripts/certify_mathlib_subtree.sh Logic /tmp/logic Mathlib.Logic@$(git -C <mathlib> rev-parse --short HEAD)
#
# Env:
#   MATHLIB_LIB  Mathlib .olean root (default: the crown-proofs vendored mathlib)
#   CLEAN_BIN    clean binary (default: target/debug/clean; use --release for scale)
set -euo pipefail

SUBTREE="${1:?usage: certify_mathlib_subtree.sh <subtree> [out-dir] [source-id]}"
OUT="${2:-./mathlib-${SUBTREE//\//-}-cert}"
SRC_ID="${3:-Mathlib.${SUBTREE//\//.}}"

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
MATHLIB_LIB="${MATHLIB_LIB:-$REPO_ROOT/crown-proofs/lean/.lake/packages/mathlib/.lake/build/lib/lean}"
CLEAN_BIN="${CLEAN_BIN:-$REPO_ROOT/target/debug/clean}"

MODS="$MATHLIB_LIB/Mathlib/$SUBTREE"
[ -d "$MODS" ] || { echo "no such subtree: $MODS" >&2; exit 1; }
mkdir -p "$OUT"

echo "== certify Mathlib/$SUBTREE  (source-id=$SRC_ID) =="
# Per-constant kernel-verify (add_decl on every proof term) each module, then
# union into ONE corpus receipt + provenance. Runs on a 1 GiB stack internally.
#
# RESUMABLE + WATCHDOG: a full-Mathlib run is long and a single pathological module
# can OOM / hang / crash and take the whole process down. We run under a per-attempt
# wall-clock `timeout` and RETRY, passing a JSONL --checkpoint: modules already
# verified replay instantly, and a module that KILLED the previous attempt (its last
# checkpoint line is `Attempting`) is SKIPPED and recorded errored — so every retry
# makes forward progress even past a module that cannot be verified in the available
# memory/time. Sound: the root is a Merkle over the canonical UNION of leaves,
# identical whether a module is replayed or freshly verified.
# Set ATTEMPT_TIMEOUT=0 to disable the watchdog (one straight pass).
CKPT="$OUT/checkpoint.jsonl"
ATTEMPT_TIMEOUT="${ATTEMPT_TIMEOUT:-0}"   # seconds per attempt; 0 = no limit
MAX_ATTEMPTS="${MAX_ATTEMPTS:-1}"
TIMEOUT_BIN="$(command -v timeout || command -v gtimeout || true)"

attempt=0
while :; do
  attempt=$((attempt + 1))
  echo "-- attempt $attempt (checkpoint: $(wc -l < "$CKPT" 2>/dev/null || echo 0) modules cached) --"
  set +e
  if [ "$ATTEMPT_TIMEOUT" != "0" ] && [ -n "$TIMEOUT_BIN" ]; then
    "$TIMEOUT_BIN" "$ATTEMPT_TIMEOUT" \
      "$CLEAN_BIN" mathverse trust-receipt corpus \
        --modules-dir "$MODS" --closure-root "$MATHLIB_LIB" --source-id "$SRC_ID" \
        --out "$OUT/receipt.json" --out-leaves "$OUT/leaves.json" \
        --out-provenance "$OUT/provenance.json" --checkpoint "$CKPT"
    rc=$?
  else
    "$CLEAN_BIN" mathverse trust-receipt corpus \
      --modules-dir "$MODS" --closure-root "$MATHLIB_LIB" --source-id "$SRC_ID" \
      --out "$OUT/receipt.json" --out-leaves "$OUT/leaves.json" \
      --out-provenance "$OUT/provenance.json" --checkpoint "$CKPT"
    rc=$?
  fi
  set -e
  # rc 0 = complete; 124 = attempt timed out (retry, resuming from checkpoint).
  [ "$rc" = 0 ] && break
  if [ "$attempt" -ge "$MAX_ATTEMPTS" ] && [ "$MAX_ATTEMPTS" != 0 ]; then
    echo "!! not complete after $attempt attempt(s) (rc=$rc); checkpoint has $(wc -l < "$CKPT") modules — re-run to continue" >&2
    exit "$rc"
  fi
  echo "-- attempt $attempt did not finish (rc=$rc); resuming from checkpoint --"
done

echo "== independent audit (re-derives the root from leaves; blake3 only) =="
"$CLEAN_BIN" mathverse trust-receipt verify --receipt "$OUT/receipt.json" --leaves "$OUT/leaves.json"

echo "== receipt =="
cat "$OUT/receipt.json"
