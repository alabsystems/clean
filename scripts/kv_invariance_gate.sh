#!/usr/bin/env bash
# Phase-1 zero-copy loader soundness gate (corpus / full-stamp scale).
#
# Stamps a fixed TARGET against a fixed closure TWICE, with --closure-elide held
# FIXED, varying ONLY how the trusted closure is loaded:
#   - EAGER: CLEAN_LAZY_CLOSURE unset  -> closure deserialized from .olean (today's path)
#   - LAZY:  CLEAN_LAZY_CLOSURE=1       -> closure served on demand from mmap'd .mathverse
#            shards (ShardConstantSource installed via Environment::set_constant_source)
# and asserts the KernelVerified NAME SET is IDENTICAL (symmetric difference empty).
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
echo "kv invariance gate: running always-on independent-parity unit tests (Minimal.olean seed)..."
cargo test -p clean-mathverse --lib v3_closure_binding_tests >/dev/null 2>&1 \
  || fail seed-unit-tests "always-on v3 closure-binding / independent-parity unit tests failed"
echo "kv invariance gate: always-on independent-parity unit tests PASS."

CLEAN_BIN="${CLEAN_BIN:-}"
[ -z "$CLEAN_BIN" ] && [ -x target/release/clean ] && CLEAN_BIN=target/release/clean
[ -z "$CLEAN_BIN" ] && [ -x target/debug/clean ] && CLEAN_BIN=target/debug/clean
[ -z "$CLEAN_BIN" ] && CLEAN_BIN="$(command -v clean 2>/dev/null || true)"
[ -n "$CLEAN_BIN" ]      || skip no-binary "no clean binary (cargo build --release --bin clean)"
[ -n "$TARGET" ]         || skip no-target "set KV_GATE_TARGET (prereq: Phase-1 CLEAN_LAZY_CLOSURE loader)"
[ -n "$CLOSURE_ROOT" ]   || skip no-closure-root "set KV_GATE_CLOSURE_ROOT (the .olean closure root)"
[ -d "$CLOSURE_SHARDS" ] || skip no-closure-shards "set KV_GATE_CLOSURE_SHARDS to the closure .mathverse shards (prereq: build closure-as-shards)"

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

python3 - "$OUT/eager.json" "$OUT/lazy.json" <<'PY' || fail verdict-divergence "KernelVerified set differs eager-vs-lazy (lazy loading changed a verdict)"
import json, sys
def kv(p):
    d = json.load(open(p))
    return set(d.get("kernel_verified_names", []))
e, l = kv(sys.argv[1]), kv(sys.argv[2])
only_e, only_l = e - l, l - e
if only_e or only_l:
    print(f"DIVERGENCE: eager-only={len(only_e)} lazy-only={len(only_l)} (eager={len(e)} lazy={len(l)})")
    for n in list(only_e)[:10]: print("  eager-only:", n)
    for n in list(only_l)[:10]: print("  lazy-only:", n)
    sys.exit(1)
print(f"OK: KernelVerified set IDENTICAL eager-vs-lazy ({len(e)} names)")
PY
echo "kv invariance gate: PASS (lazy closure loading is verdict-identical to eager)."
verdict measured
