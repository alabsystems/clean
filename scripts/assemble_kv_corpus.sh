#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Assemble every genuinely KernelVerified .mathverse shard produced by the
# kernel re-verification pipelines into a single, loadable KV corpus directory:
#   - Metamath set.mm        : data/mathverse-shards/metamath-kv/set_mm_kv.mathverse
#                              (KernelVerified, AXIOMATIZED — axiom-relative to $a)
#   - Mathlib (full)         : data/mathverse-library/mathlib-kv/shards_*/**.mathverse
#                              (KernelVerified, re-checked via env.add_decl)
#   - Cake graduation        : canonical kernel-verified clean-native theorems
#
# Shard stems collide across Mathlib chunks (e.g. Basic.mathverse appears in
# many modules), so every shard is copied under a path-derived unique name.
# Prints `clean mathverse stats` over the assembled corpus.
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
CLEAN_BIN="$REPO_ROOT/target/release/clean"
OUT="${1:-$REPO_ROOT/data/mathverse-library/kv-corpus}"
MM_SHARD="$REPO_ROOT/data/mathverse-shards/metamath-kv/set_mm_kv.mathverse"
ML_BASE="$REPO_ROOT/data/mathverse-library/mathlib-kv"
# Isabelle/HOL: closure-replay KernelVerified shard (HOL-Proofs library), built by
# `cargo test -p clean-mathverse --release --test isabelle_scale_run
#  stream_run_if_env_set` with ISA_SHARD_OUT set. Released as an archive, not in git.
ISA_DIR="$REPO_ROOT/data/mathverse-shards/isabelle-hol-kv"

# --- Memory governor (2026-06-23 single-process OOM fix) ---------------------
# `clean mathverse stats` loads EVERY shard of a lane into ONE in-process
# MathverseLibrary; over the full corpus that single load can exhaust RAM — the
# 2026-06-23 19:18 watchdog panic was a lone `clean` proc (~78GB compressor,
# ~15MB free). The 2026-06-22 governor only guarded *concurrent* stamp runs, so
# it never engaged here. Run each load under the same RSS/low-RAM watchdog, and
# hold the shared single-instance lock so assembly never overlaps a stamp run.
# shellcheck source=scripts/lib/stamp_mem_governor.sh
source "$REPO_ROOT/scripts/lib/stamp_mem_governor.sh"
if [ -z "${STAMP_LOCK_HELD:-}" ]; then
  stamp_acquire_global_lock || exit 1
  export STAMP_LOCK_HELD=1   # inherited child scripts re-use this lock (re-entrant)
fi

# Run one `clean mathverse stats` under the governor's RSS/low-RAM watchdog.
governed_stats() {  # <label> <shard-dir>
  local label="$1" dir="$2" log
  log="$(mktemp "${TMPDIR:-/tmp}/kv-stats-XXXXXX.log")"
  echo "=== stats: $label ==="
  stamp_wait_for_free_ram
  if stamp_run_governed_chunk "$log" "${KV_STATS_TIMEOUT:-3600}" -- \
      "$CLEAN_BIN" mathverse stats --shard-dir "$dir"; then
    sed -n '1,20p' "$log"
  else
    echo "[assemble] stats for '$label' aborted by governor: ${STAMP_LAST_STATUS} (peak $((STAMP_LAST_PEAK_KB/1048576))GiB)" >&2
  fi
  rm -f "$log"
}

rm -rf "$OUT"; mkdir -p "$OUT/metamath" "$OUT/mathlib" "$OUT/cake" "$OUT/isabelle"

# --- Metamath ---
[ -f "$MM_SHARD" ] && cp "$MM_SHARD" "$OUT/metamath/set_mm_kv.mathverse"

# --- Isabelle/HOL: every KernelVerified closure-replay shard (HOL-Proofs library).
# Each entry was re-checked by Clean's kernel with axiom closure ⊆ the 3
# foundational axioms (propext, Quot.sound, Classical.choice); the library dedups
# by name, so multiple shard versions union safely. ---
if [ -d "$ISA_DIR" ]; then
  isa=0
  while IFS= read -r -d '' s; do
    cp "$s" "$OUT/isabelle/$(basename "$s")"; isa=$((isa+1))
  done < <(find "$ISA_DIR" -name '*.mathverse' -print0)
  echo "[assemble] copied $isa isabelle-hol KV shard file(s)"
fi

# --- Mathlib: collect ONLY KernelVerified-stamped shards. -------------------
# First-run chunk dirs shards_NN are KV iff chunk_NN.log carries a valid
# kernel_verified JSON summary (failed chunks left SourceVerified shards we must
# NOT include). All rerun/shards_r* are KV (governed re-run only stamps on add_decl
# success). Duplicate module shards across v1/v2 reruns are deduped by name when
# the library loads (a library is a name->constant map), so the union is safe.
ml=0
copy_shard() { rel="${1#"$ML_BASE"/}"; cp "$1" "$OUT/mathlib/$(echo "$rel" | tr '/' '_')"; ml=$((ml+1)); }
if [ -d "$ML_BASE" ]; then
  # KV-good first-run chunks (skip failed/unstamped ones).
  for d in "$ML_BASE"/shards_[0-9][0-9]; do
    [ -d "$d" ] || continue
    nn="$(basename "$d" | sed 's/shards_//')"
    if grep -q '"kernel_verified"' "$ML_BASE/chunk_$nn.log" 2>/dev/null; then
      while IFS= read -r -d '' s; do copy_shard "$s"; done < <(find "$d" -name '*.mathverse' -print0)
    else
      echo "[assemble] skip $d (no KV stamp — failed chunk, recovered via rerun)"
    fi
  done
  # All recovered rerun shards (KV by construction).
  if [ -d "$ML_BASE/rerun" ]; then
    while IFS= read -r -d '' s; do copy_shard "$s"; done < <(find "$ML_BASE/rerun" -path '*/shards_r*/*.mathverse' -print0)
  fi
fi
echo "[assemble] copied $ml mathlib KV shard files (pre-dedup; library dedups by name)"

# --- Cake graduation: canonical newest snapshots only (avoid wave duplicates). ---
for g in \
  "$REPO_ROOT/data/graduation/v7-cake-nn/v7-cake-nn-graduated.mathverse" \
  "$REPO_ROOT/data/graduation/v6-cake-core/v6-cake-core-graduated.mathverse" \
  "$REPO_ROOT/data/graduation/v3.3/crown-proofs-qcore/crown-proofs-qcore-graduated.mathverse"; do
  [ -f "$g" ] && cp "$g" "$OUT/cake/$(echo "${g#"$REPO_ROOT"/data/graduation/}" | tr '/' '_')"
done

echo "[assemble] corpus at $OUT"
find "$OUT" -name '*.mathverse' | wc -l | awk '{print "[assemble] total shards: "$1}'

if [ -x "$CLEAN_BIN" ]; then
  governed_stats "metamath" "$OUT/metamath"
  governed_stats "mathlib"  "$OUT/mathlib"
  governed_stats "cake"     "$OUT/cake"
  governed_stats "isabelle" "$OUT/isabelle"
fi
