#!/usr/bin/env bash
# Phase-1 zero-copy loader soundness gate (corpus / full-stamp scale).
#
# Stamps a fixed TARGET against a fixed closure TWICE, with --closure-elide held
# FIXED, varying ONLY how the trusted closure is loaded:
#   - EAGER: CLEAN_LAZY_CLOSURE unset  -> closure deserialized from .olean (today's path)
#   - LAZY:  CLEAN_LAZY_CLOSURE=1       -> closure served on demand from mmap'd .mathverse
#            shards (ShardConstantSource installed via Environment::set_constant_source)
# and asserts the accepted NAME SET is IDENTICAL (symmetric difference empty); under
# P6 both are development tier, so the names are data here, never a label.
#
# This is the corpus-scale form of the integration test already PROVEN green on real
# data (closure_source::tests::lazy_closure_verdict_matches_eager: crown-proofs
# ok_eq=18/err_eq=43, metamath err_eq=61, DIVERGENCE=0). It is the hard gate that must
# pass before CLEAN_LAZY_CLOSURE is ever defaulted ON.
#
# A NAME PRESENT ONLY IN THE EAGER set is a regression (lazy lost a verdict) and fails.
# (lazy-only is in principle benign — lazy can't gain a verdict it didn't earn — but the
# gate requires EQUALITY on the validation target and reports either direction.)
#
# SKIP-green when the binary / target / closure shards are absent — the
# closure-as-shards prerequisite and the CLEAN_LAZY_CLOSURE loader are the remaining
# Phase-1 wiring; this gate is forward-declared so it activates the moment they land.
# bash-3.2 safe.
#
# ## The verdict line
#
# Like scripts/kv_ratchet_gate.sh, exit status alone cannot distinguish this gate
# having MEASURED something from it having deferred. Here the distinction is
# sharper than a bare skip, because the always-on seed below (the independent
# eager-vs-lazy parity unit tests over the committed Minimal.olean fixture) runs
# on EVERY invocation — so a green exit always means at least that much ran.
# Exactly one machine-readable verdict line is emitted on stdout:
#
#     KVINV_GATE=measured             both legs ran: seed AND the corpus-scale
#                                     eager-vs-lazy stamp comparison
#     KVINV_GATE=seed-only:<reason>   the seed unit tests passed, but the
#                                     corpus leg was not run; <reason> says why
#     KVINV_GATE=failed:<reason>      a real divergence or error (exit 1)
#
# "seed-only" is deliberately NOT called "skipped": real work ran, and saying
# otherwise would understate the gate as badly as calling it "measured" would
# overstate it.
#
# Set KVINV_GATE_VERDICT_FILE=<path> to also write the line to a file, and
# KVINV_GATE_REQUIRE_MEASURED=1 to make seed-only a FAILURE — which any run
# claiming corpus-scale lazy/eager invariance must set.
set -uo pipefail
cd "$(cd "$(dirname "$0")/.." && pwd)" || exit 1

ELIDE="${CLOSURE_ELIDE:-opaque-and-theorem}"
TARGET="${KV_GATE_TARGET:-}"                  # one (or more, space-sep) .olean to re-check
CLOSURE_ROOT="${KV_GATE_CLOSURE_ROOT:-}"      # the .olean closure root (eager leg)
CLOSURE_SHARDS="${KV_GATE_CLOSURE_SHARDS:-}"  # the closure as .mathverse shards (lazy leg)

REQUIRE_MEASURED="${KVINV_GATE_REQUIRE_MEASURED:-0}"
case "$REQUIRE_MEASURED" in 1|true|TRUE|yes|YES) REQUIRE_MEASURED=1;; *) REQUIRE_MEASURED=0;; esac

# verdict <line>: emit the single machine-readable result line. Once per run.
verdict() {
  echo "KVINV_GATE=$1"
  [ -n "${KVINV_GATE_VERDICT_FILE:-}" ] && printf 'KVINV_GATE=%s\n' "$1" > "$KVINV_GATE_VERDICT_FILE"
  return 0
}

# skip <reason-slug> <human text>: the corpus leg did not run. The always-on seed
# above already passed by the time we reach here, hence "seed-only", not "skipped".
skip() {
  if [ "$REQUIRE_MEASURED" = 1 ]; then
    echo "kv invariance gate: FAIL — KVINV_GATE_REQUIRE_MEASURED is set but the corpus leg did not run: $2." >&2
    verdict "seed-only:$1"
    exit 1
  fi
  echo "SKIP: kv invariance gate (corpus leg) — $2."
  verdict "seed-only:$1"
  exit 0
}

fail() { echo "kv invariance gate: FAIL — $2" >&2; verdict "failed:$1"; exit 1; }

# ALWAYS-ON SEED (no Mathlib checkout / built binary needed): the truly-independent
# eager-vs-lazy parity unit test, seeded by the committed
# tests/fixtures/olean/v4.13.0/custom/Minimal.olean. Its EAGER leg is clean-olean
# `convert_expr` (NOT derived from the lazy source), so it catches encoder
# divergence the old lazy_closure_verdict_matches_eager (both legs from the lazy
# source) cannot. This makes the gate run real work instead of SKIP-green.
# The corpus leg's comparison is self-tested first, on every run: two empty sets,
# a divergence and a schema-1 manifest must each be refused (equal non-empty sets
# pass), so the leg can never pass over sets a renamed or missing key emptied.
python3 scripts/acceptance_manifest.py --selftest \
  || fail comparison-selftest "the eager-vs-lazy comparison self-test FAILED (scripts/acceptance_manifest.py --selftest)"
echo "kv invariance gate: running always-on independent-parity unit tests (Minimal.olean seed)..."
# The output is KEPT, and the two failure modes are told apart.
#
# This used to be `>/dev/null 2>&1 || fail seed-unit-tests "... unit tests
# failed"`, which reports a test failure whenever CARGO could not run -- a build
# error, a poisoned toolchain, a full disk, or simply another lane holding the
# build-directory lock. Measured 2026-09-15: a concurrent demonstration made
# this line fail, the gate said "unit tests failed", and `--repin` refused the
# whole row on that basis; run alone minutes later the same command is
# `15 passed; 0 failed`. A gate that cannot say "I could not run" will eventually
# be believed when it says "it failed".
_seed_log="$(mktemp "${TMPDIR:-/tmp}/kv_invariance_seed.XXXXXX")"
if targo --unverified test -p clean-mathverse --lib v3_closure_binding_tests > "$_seed_log" 2>&1; then
  echo "kv invariance gate: always-on independent-parity unit tests PASS."
  rm -f "$_seed_log"
elif grep -q "^test result:" "$_seed_log"; then
  # libtest reported, so the tests genuinely ran and genuinely failed.
  _tail="$(tail -5 "$_seed_log")"; rm -f "$_seed_log"
  fail seed-unit-tests "always-on v3 closure-binding / independent-parity unit tests FAILED: $_tail"
else
  # No libtest verdict at all: cargo never got as far as running them.
  _tail="$(tail -5 "$_seed_log")"; rm -f "$_seed_log"
  fail seed-unit-tests-unrunnable "the seed unit tests could not be RUN (no libtest verdict in cargo's output -- a build error, a busy build-directory lock, or a toolchain problem; this is NOT a test failure): $_tail"
fi

[ -n "$TARGET" ]         || skip no-target "set KV_GATE_TARGET (prereq: Phase-1 CLEAN_LAZY_CLOSURE loader)"
[ -n "$CLOSURE_ROOT" ]   || skip no-closure-root "set KV_GATE_CLOSURE_ROOT (the .olean closure root)"
[ -d "$CLOSURE_SHARDS" ] || skip no-closure-shards "set KV_GATE_CLOSURE_SHARDS to the closure .mathverse shards (prereq: build closure-as-shards)"

# Resolve the `clean` binary this gate judges the loader with, and REFUSE one
# that cannot be shown to be built from this checkout. This row claims soundness
# and is already DEMONSTRATED, which is exactly why the old resolution mattered:
# the three lines that used to sit here (release, then debug, then
# `command -v clean`) had no freshness check, so a signed-off soundness row
# could have been measuring a property of a different kernel. Shared with
# scripts/kv_ratchet_gate.sh, which carried the identical three lines.
# Placed AFTER the no-target / no-closure-root / no-closure-shards checks and
# BEFORE any real work, for the reason spelled out at length in the sibling
# scripts/kv_ratchet_gate.sh: a refusal must not fire on a tree where the gate
# was never going to run the binary, and must outrank any later deferral.
#
# Sourced by the relative path: this script cd's to the repo root at the top.
# shellcheck source=scripts/lib/clean_binary_under_test.sh
. scripts/lib/clean_binary_under_test.sh
resolve_clean_binary_under_test
case "$?" in
  0) CLEAN_BIN="$CLEAN_BIN_UNDER_TEST" ;;
  2) skip no-binary "$CLEAN_BIN_REASON" ;;
  3) fail stale-binary "$CLEAN_BIN_REASON" ;;
  *) fail stale-binary "the binary-under-test resolver returned an unexpected status" ;;
esac

OUT="$(mktemp -d "${TMPDIR:-/tmp}/kv_invariance_gate.XXXXXX")"
trap 'rm -rf "$OUT"' EXIT

# shellcheck disable=SC2086
"$CLEAN_BIN" mathverse stamp-verified $TARGET \
  --out-dir "$OUT/shards_eager" --closure-root "$CLOSURE_ROOT" --closure-elide "$ELIDE" \
  --manifest "$OUT/eager.json" --json > "$OUT/eager.out" 2>&1 \
  || fail eager-stamp "eager stamp errored: $(tail -3 "$OUT/eager.out")"

# shellcheck disable=SC2086
CLEAN_LAZY_CLOSURE=1 CLEAN_CLOSURE_SHARDS="$CLOSURE_SHARDS" "$CLEAN_BIN" mathverse stamp-verified $TARGET \
  --out-dir "$OUT/shards_lazy" --closure-root "$CLOSURE_ROOT" --closure-elide "$ELIDE" \
  --manifest "$OUT/lazy.json" --json > "$OUT/lazy.out" 2>&1 \
  || fail lazy-stamp "lazy stamp errored: $(tail -3 "$OUT/lazy.out")"

# P6 reader R15: scripts/acceptance_manifest.py refuses a schema-1, identity-less
# or reference-tier manifest (never reading a missing list as empty) and two EMPTY
# sets, since "identical" over nothing measures nothing.
python3 scripts/acceptance_manifest.py invariance "$OUT/eager.json" "$OUT/lazy.json" \
  || fail verdict-divergence "accepted set differs eager-vs-lazy, or a manifest was refused (lazy loading changed a verdict, or the comparison measured nothing)"
echo "kv invariance gate: PASS (lazy closure loading is verdict-identical to eager)."
verdict measured
