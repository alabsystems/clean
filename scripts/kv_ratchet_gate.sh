#!/usr/bin/env bash
# Non-vacuous KernelVerified gate.
#
# RE-STAMPS the pinned, reproducible slice (data/kv_ratchet_slice.txt) with the
# clean kernel on every run and enforces, against committed baselines:
#   1. KV ratchet     — kernel_verified must not drop below the baseline in
#                       data/mathlib_kv_ratchet.json, and heuristic_kernel_verified
#                       must be 0 (soundness floor). [`clean mathverse ratchet check`]
#   2. Elision subset — every constant the statically-sound `--closure-elide opaque`
#                       run kernel-verified must still be verified under the
#                       production-default `opaque-and-theorem` run (eliding theorem
#                       values may only ADD KernelVerified, never drop one).
#                       [`clean mathverse elision-gate`]
#
# This is what makes the gate NON-VACUOUS: it re-measures a real (small, fixed,
# OOM-safe, deterministic) slice rather than reading a static committed summary.
# A baseline of N>0 over a re-stamped slice catches a refactor that silently drops
# a KernelVerified verdict; a static summary or a 0 baseline would catch nothing.
#
# SKIP-green (exit 0) when the `clean` binary or the Mathlib checkout is absent, so
# clones without the corpus still pass. bash-3.2 safe.
#
# ## The verdict line (why a green exit code is not evidence)
#
# There are SIX skip-green paths below, and at least two of them fire routinely on
# an ordinary dev machine: the corpus lives under data/raw/mathlib4 and is commonly
# a symlink into /tmp (deleted by tmp cleanup), and the RAM admission check defers
# whenever the box is under 8GiB free — which concurrent builds cause constantly.
# So `exit 0` alone means ANY of: verified; no binary; no corpus; partial corpus;
# empty slice; or simply that something else was using memory.
#
# Exit status therefore cannot distinguish a measurement from a deferral, and no
# automation (or release checklist, or blog post) should treat it as if it could.
# Every run now emits exactly one machine-readable verdict line on stdout:
#
#     KV_GATE=measured                 the slice was actually re-stamped and held
#     KV_GATE=skipped:<reason>         nothing was measured; <reason> says why
#     KV_GATE=failed:<reason>          a real regression (exit 1)
#
# Set KV_GATE_VERDICT_FILE=<path> to also write that line to a file.
#
# Set KV_GATE_REQUIRE_MEASURED=1 to make every skip a FAILURE instead. Any run
# whose result is going to be published — a release gate, a reproduction of the
# Mathlib KernelVerified numbers — must set it, so that "the gate was green"
# cannot silently mean "the gate measured nothing".
set -uo pipefail
cd "$(cd "$(dirname "$0")/.." && pwd)" || exit 1

SLICE=data/kv_ratchet_slice.txt
RATCHET=data/mathlib_kv_ratchet.json
ML=data/raw/mathlib4
MLLIB="$ML/.lake/build/lib/lean"
MLROOT="$MLLIB/Mathlib"

REQUIRE_MEASURED="${KV_GATE_REQUIRE_MEASURED:-0}"
case "$REQUIRE_MEASURED" in 1|true|TRUE|yes|YES) REQUIRE_MEASURED=1;; *) REQUIRE_MEASURED=0;; esac

# verdict <line>: emit the single machine-readable result line (stdout, and the
# optional KV_GATE_VERDICT_FILE). Called exactly once per run, on every path.
verdict() {
  echo "KV_GATE=$1"
  [ -n "${KV_GATE_VERDICT_FILE:-}" ] && printf 'KV_GATE=%s\n' "$1" > "$KV_GATE_VERDICT_FILE"
  return 0
}

# skip <reason-slug> <human text>: nothing was measured. Green by default so that
# clones without the corpus still pass; RED under KV_GATE_REQUIRE_MEASURED, because
# a publication run asserting a measurement must not accept a deferral.
skip() {
  if [ "$REQUIRE_MEASURED" = 1 ]; then
    echo "KV ratchet gate: FAIL — KV_GATE_REQUIRE_MEASURED is set but nothing was measured: $2." >&2
    verdict "skipped:$1"
    exit 1
  fi
  echo "SKIP: KV ratchet gate — $2."
  verdict "skipped:$1"
  exit 0
}

fail() { echo "KV ratchet gate: FAIL — $2" >&2; verdict "failed:$1"; exit 1; }

# Resolve a built `clean` binary. Prefer the LOCAL build (the binary under test)
# over any globally-installed `clean` on PATH: a stale PATH binary would re-stamp
# with the wrong kernel and yield a wrong count (false pass/fail). $CLEAN_BIN
# overrides for out-of-tree runs (e.g. a worktree whose target/ is redirected).
CLEAN_BIN="${CLEAN_BIN:-}"
[ -z "$CLEAN_BIN" ] && [ -x target/release/clean ] && CLEAN_BIN=target/release/clean
[ -z "$CLEAN_BIN" ] && [ -x target/debug/clean ] && CLEAN_BIN=target/debug/clean
[ -z "$CLEAN_BIN" ] && CLEAN_BIN="$(command -v clean 2>/dev/null || true)"
[ -z "$CLEAN_BIN" ] && skip no-binary "no clean binary (cargo build --release --bin clean to enable)"
[ -f "$SLICE" ]    || skip no-slice-manifest "no slice manifest at $SLICE"
[ -d "$MLLIB" ]    || skip no-corpus "no Mathlib checkout at $MLLIB"

# LEAN_PATH: Mathlib lib + the pinned toolchain core + every Lake package lib.
TC="$(tr -d ' \t\r\n' < "$ML/lean-toolchain" | sed 's#/#--#; s#:#---#')"
CORE="$HOME/.elan/toolchains/$TC/lib/lean"
LP="$MLLIB"
[ -d "$CORE" ] && LP="$LP:$CORE"
for p in "$ML"/.lake/packages/*/.lake/build/lib/lean; do
  [ -d "$p" ] && LP="$LP:$p"
done
export LEAN_PATH="$LP"

# Resolve the slice's relative module paths to absolute oleans.
TARGETS=""
while IFS= read -r line; do
  case "$line" in ''|\#*) continue;; esac
  f="$MLROOT/$line"
  [ -f "$f" ] || skip partial-corpus "slice module missing from checkout: $line"
  TARGETS="$TARGETS $f"
done < "$SLICE"
[ -n "$TARGETS" ] || skip empty-slice "slice manifest is empty"

# Lightweight OOM admission. Deliberately NOT the heavy-stamp global lock
# (scripts/lib/stamp_mem_governor.sh): that lock is held ~continuously by the
# corpus-stamp automation, so taking it would make this gate hang or perma-skip.
# A 2-module slice (~2GiB) needs no heavy-stamp mutual exclusion; we only refuse to
# pile on when the box is ALREADY under memory pressure (e.g. a corpus stamp is
# mid-run), turning a potential OOM into a clean skip. Sourcing the lib only sets
# var defaults + defines functions (no lock/trap at source time).
if [ -r scripts/lib/stamp_mem_governor.sh ]; then
  # shellcheck source=/dev/null
  . scripts/lib/stamp_mem_governor.sh
  _avail="$(stamp_available_gib 2>/dev/null || echo 999)"
  case "$_avail" in ''|*[!0-9]*) _avail=999;; esac
  [ "$_avail" -lt 8 ] && skip low-memory "only ${_avail}GiB free RAM (a corpus stamp may be running); deferring the slice stamp"
fi

OUT="$(mktemp -d "${TMPDIR:-/tmp}/kv_ratchet_gate.XXXXXX")"
trap 'rm -rf "$OUT"' EXIT

# A FRESH out-dir per stamp avoids stale-shard contamination (the cause of the
# 2026-06-24 false "provenance UnexpectedEnd" scare). --single-pass for the slice.
stamp() {  # <elision> <summary-out> <manifest-out>
  # shellcheck disable=SC2086
  "$CLEAN_BIN" mathverse stamp-verified $TARGETS \
    --out-dir "$OUT/shards_$1" \
    --closure-root "$MLLIB" \
    --closure-elide "$1" \
    --single-pass \
    --manifest "$3" \
    --json > "$2" 2> "$OUT/stamp_$1.err" \
    || { echo "stamp ($1) errored:" >&2; tail -5 "$OUT/stamp_$1.err" >&2; return 1; }
}

echo "  re-stamping pinned slice (opaque-and-theorem + opaque)..."
stamp opaque-and-theorem "$OUT/summary_oat.json" "$OUT/kv_oat.json" || fail stamp-oat "production-default stamp of the pinned slice"
stamp opaque             "$OUT/summary_op.json"  "$OUT/kv_op.json"  || fail stamp-opaque "statically-sound (opaque) stamp of the pinned slice"

# 1. KV ratchet (monotonic-UP + heuristic==0 soundness floor) on the oat summary.
"$CLEAN_BIN" mathverse ratchet check --summary "$OUT/summary_oat.json" --ratchet "$RATCHET" \
  || fail ratchet-regression "re-stamping the pinned slice dropped KernelVerified below the baseline (or heuristic_kernel_verified != 0); see $RATCHET + $SLICE"

# 2. Elision subset gate: KV(opaque) must be subset-of KV(opaque-and-theorem).
"$CLEAN_BIN" mathverse elision-gate "$OUT/kv_op.json" "$OUT/kv_oat.json" \
  || fail elision-subset "opaque-and-theorem dropped a KernelVerified constant that the statically-sound opaque run kept"

echo "  KV ratchet gate: PASS (slice re-stamped; ratchet + elision subset hold)."
verdict measured
