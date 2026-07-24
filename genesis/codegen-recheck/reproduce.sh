#!/usr/bin/env bash
#
# UNIFIED reproducible artifact — the durable-seed -> compiler-recheck path.
#
# From the checksum-pinned source in MANIFEST.txt, this builds and runs the
# kernel independently re-checking a REAL trust-cg compiler lowering (the
# trust_cg_opt::gvn commutative-canonicalization pass's identity) to
# trust_count == 0, NON-VACUOUSLY (a tampered lowering makes the proof FAIL).
# This is criterion 2 (compiler out of the TCB) made reproducible from a durable,
# checksum-pinned seed (criterion 3) in one flow.
#
# Usage:  genesis/codegen-recheck/reproduce.sh
#
set -euo pipefail
cd "$(git rev-parse --show-toplevel 2>/dev/null || pwd)"

MAN="genesis/codegen-recheck/MANIFEST.txt"
[ -f "$MAN" ] || { echo "FATAL: $MAN not found"; exit 2; }
if command -v sha256sum >/dev/null 2>&1; then SHA_C() { sha256sum -c -; }; else SHA_C() { shasum -a 256 -c -; }; fi

echo "== UNIFIED codegen-recheck reproduction =="
echo "clean    pinned : $(awk -F'= ' '/^clean_commit/{print $2}' "$MAN")"
echo "trust-cg pinned : $(awk -F'= ' '/^trustcg_commit/{print $2}' "$MAN")"
echo "rustc           : $(awk -F'= ' '/^rustc /{print $2}' "$MAN")"

# 1) checksum integrity of the load-bearing codegen-recheck source.
echo "-- [1/2] checksum integrity of the pinned codegen-recheck source --"
awk '/^# --- checksums/{p=1;next} p' "$MAN" | SHA_C
echo "   checksums OK"

# 2) the kernel re-checks the REAL trust-cg lowerings to trust_count == 0.
#    Re-checks BOTH real GVN commutative-canonicalization kinds (ADD ripple-carry +
#    XOR bitwise gate-fidelity). The `ay-bv-blast` feature is passed EXPLICITLY (the
#    criterion-2 module is gated on it) so the re-check never silently no-ops on a
#    feature-unification quirk. We ASSERT >= 4 tests ran and 0 failed — a filter that
#    matches 0 tests would still exit 0, so we must verify the tests actually executed.
echo "-- [2/2] kernel independently re-checks the real trust_cg_opt::gvn lowerings (ADD + XOR/AND/OR) --"
TEST_LOG="$(mktemp)"
# All four test-name filters go AFTER `--` (libtest OR-matches multiple filters; cargo
# itself accepts only one positional TESTNAME). ADD = ripple-carry gate-fidelity;
# XOR/AND/OR = the three bitwise gate-fidelities the real GVN canonicalizer also covers.
cargo test --locked -p clean-auto --lib --features ay-bv-blast \
  -- --nocapture \
  criterion2_gvn_commute_lowering_is_nonvacuously_certified_trust_count_zero \
  criterion2_gvn_xor_commute_lowering_certified_trust_count_zero \
  criterion2_gvn_and_commute_lowering_certified_trust_count_zero \
  criterion2_gvn_or_commute_lowering_certified_trust_count_zero \
  2>&1 | tee "$TEST_LOG"
RES_LINE="$(grep -E '^test result:' "$TEST_LOG" | tail -1)"
PASSED="$(printf '%s' "$RES_LINE" | sed -nE 's/.*ok\. ([0-9]+) passed.*/\1/p')"
FAILED="$(printf '%s' "$RES_LINE" | sed -nE 's/.* ([0-9]+) failed.*/\1/p')"
rm -f "$TEST_LOG"
if [ "${PASSED:-0}" -lt 4 ] || [ "${FAILED:-1}" -ne 0 ]; then
  echo "FATAL: the criterion-2 re-checks did NOT all run+pass (passed=${PASSED:-0} failed=${FAILED:-?}) — NOT reproduced."
  exit 1
fi
echo "   all four re-checks ran and PASSED ($PASSED passed, $FAILED failed)"

echo
echo "== UNIFIED REPRODUCED =="
echo "From the checksum-pinned seed, the kernel independently re-checked TWO REAL trust-cg GVN"
echo "lowering kinds — ADD commutativity (bvAdd a b == bvAdd b a, ripple-carry gate-fidelity) and"
echo "XOR commutativity (bvXor a b == bvXor b a, per-bit Bool.xor gate-fidelity, no carry) — both to"
echo "trust_count == 0, non-vacuously (tampered lowerings FAIL). rustc/LLVM are NOT trusted for these"
echo "lowerings' correctness; the kernel re-checked them. (ADD scale through width-16; the minimal-ck0"
echo "codegen port + wider widths + more lowering kinds are the named remaining scale-out.)"
