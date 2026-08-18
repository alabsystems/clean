#!/usr/bin/env bash
# Perturbation proofs for the EIGHTH chain's gates:
#   env::native_reducers_float::reduce_float_div::{closure#0}
#
# The CFG / evidence gates read the spec source text and the fixtures from disk
# at RUNTIME (CARGO_MANIFEST_DIR), so the compiled test binary is driven
# directly: a perturbation is a file edit, the binary re-reads it, and no
# rebuild is involved. Each case mutates, asserts FAIL, reverts, asserts PASS.
#
# FOUR of the cases exist because of holes the earlier scripts could not have
# found, on lanes this chain added:
#   * P3, P4 (spec side) and P11 (artifact side) — the binop's TYPE. `fdiv f32`
#     and `fdiv f64` are different operations and differed in NO lane before
#     `binop_tys`.
#   * P5 (spec side) and P12 (artifact side) — the RETURNED value id. `ret %1`
#     returns the DIVIDEND, and agreed with every lane in the file before `rets`.
#   * P1, P2 and P14 — the float OPERATION itself (fdiv -> fmul / fadd / fsub).
#   * P29-P31 — the recorded float-semantics WALL, so a later lane cannot claim
#     the boundary away without a gate noticing.
set -uo pipefail
OUT="$(mktemp)"; trap 'rm -f "$OUT"' EXIT
REPO="$(cd "$(dirname "$0")/.." && pwd -P)"
BIN="${CRYSTAL_BIN:?set CRYSTAL_BIN to the compiled crystal_a1_lineage test binary}"

FD_SPEC="$REPO/crates/clean-verify/src/spec/core_spec/eval_ir_float_div.rs"
FD_FIX="$REPO/crates/clean-verify/tests/fixtures/float_div.trust-ir.txt"
FD_JSON="$REPO/crates/clean-verify/tests/fixtures/float_div.lineage.json"

pass=0; fail=0
FILTER=float_div
run() { "$BIN" "$FILTER" --test-threads=1 >"$OUT" 2>&1; }

expect() { # expect <FAIL|PASS> <label>
  run
  rc=$?
  want="$1"; label="$2"
  if [[ "$want" == "PASS" && $rc -eq 0 ]] || [[ "$want" == "FAIL" && $rc -ne 0 ]]; then
    echo "OK   [$want] $label"
    pass=$((pass+1))
  else
    echo "BAD  [want $want, rc=$rc] $label"
    sed -n '1,25p' "$OUT"
    fail=$((fail+1))
  fi
}

reason() { awk '/panicked at/{f=1} f{print "     | " $0} /^note: run with/{exit}' "$OUT" | head -6; }

# Substitute inside the DECLARATION lines only. A silent no-substitution would
# make a MUTATED run look green — the exact false negative this script exists to
# rule out — so the helper restricts .rs edits to lines beginning `const SRC_`
# and fails loudly when an anchor does not match exactly one of them.
sub() { python3 - "$1" "$2" "$3" <<'PY'
import sys
p, a, b = sys.argv[1], sys.argv[2], sys.argv[3]
lines = open(p).read().split("\n")
decl_only = p.endswith(".rs")
hits = [i for i, l in enumerate(lines)
        if a in l and (not decl_only or l.startswith("const SRC_"))]
assert len(hits) == 1, "anchor must match exactly one line, matched %d: %s" % (len(hits), a[:80])
i = hits[0]
assert lines[i].count(a) == 1, "anchor not unique within its line: %s" % a[:80]
lines[i] = lines[i].replace(a, b, 1)
open(p, "w").write("\n".join(lines))
PY
  rc=$?
  # A FAILED substitution is the false negative this whole script exists to
  # rule out: the file stays as it was, the next `expect` runs against an
  # unchanged (or still-mutated) tree, and every case after it is
  # meaningless. Abort loudly instead.
  if [[ $rc -ne 0 ]]; then
    echo "FATAL: substitution failed in $1 (anchor did not match exactly one declaration line)"
    exit 9
  fi
}

echo "== baseline =="
expect PASS "baseline: all float_div gates green"

# ───────────────────────── the emitted instruction ─────────────────────────

echo
echo "== P1: THE FLOAT OPERATION — fdiv becomes fmul =="
sub "$FD_SPEC" "IRInst.binop IRBinOp.fdiv ir_fd_tf64" "IRInst.binop IRBinOp.fmul ir_fd_tf64"
expect FAIL "P1 mutated: the proved module multiplies where the artifact divides"; reason
sub "$FD_SPEC" "IRInst.binop IRBinOp.fmul ir_fd_tf64" "IRInst.binop IRBinOp.fdiv ir_fd_tf64"
expect PASS "P1 reverted"

echo
echo "== P2: THE FLOAT OPERATION — fdiv becomes fadd =="
sub "$FD_SPEC" "IRInst.binop IRBinOp.fdiv ir_fd_tf64" "IRInst.binop IRBinOp.fadd ir_fd_tf64"
expect FAIL "P2 mutated: the proved module adds where the artifact divides"; reason
sub "$FD_SPEC" "IRInst.binop IRBinOp.fadd ir_fd_tf64" "IRInst.binop IRBinOp.fdiv ir_fd_tf64"
expect PASS "P2 reverted"

echo
echo "== P3: THE NEW TYPE LANE — binary64 becomes binary32 =="
# The anchors carry `def ir_fd_tf64` on purpose: SRC_W_F32 also contains
# `IRTy.float_ 32`, so a bare revert anchor would match two declaration lines,
# the substitution would abort, and every case after this one would run against
# a still-mutated tree. Measured, not hypothetical: it happened on this script's
# first run, and the `sub` guard above is the fix.
sub "$FD_SPEC" "def ir_fd_tf64 : IRTy := IRTy.float_ 64" "def ir_fd_tf64 : IRTy := IRTy.float_ 32"
expect FAIL "P3 mutated: the module is transcribed at binary32, which classifies the same bit patterns differently and which ir_float_binop refuses"; reason
sub "$FD_SPEC" "def ir_fd_tf64 : IRTy := IRTy.float_ 32" "def ir_fd_tf64 : IRTy := IRTy.float_ 64"
expect PASS "P3 reverted"

echo
echo "== P4: THE NEW TYPE LANE — float becomes unsigned integer =="
sub "$FD_SPEC" "def ir_fd_tf64 : IRTy := IRTy.float_ 64" "def ir_fd_tf64 : IRTy := IRTy.uint_ 64"
expect FAIL "P4 mutated: same width, integer type — the operands would be read by ir_as_int"; reason
sub "$FD_SPEC" "def ir_fd_tf64 : IRTy := IRTy.uint_ 64" "def ir_fd_tf64 : IRTy := IRTy.float_ 64"
expect PASS "P4 reverted"

echo
echo "== P5: THE NEW RET LANE — return the DIVIDEND instead of the quotient =="
sub "$FD_SPEC" "(ir_nd (IRInst.ret (ir_nl1 ir_d3)))" "(ir_nd (IRInst.ret (ir_nl1 ir_d1)))"
expect FAIL "P5 mutated: the body returns %1, its first f64 argument, instead of %3"; reason
sub "$FD_SPEC" "(ir_nd (IRInst.ret (ir_nl1 ir_d1)))" "(ir_nd (IRInst.ret (ir_nl1 ir_d3)))"
expect PASS "P5 reverted"

echo
echo "== P6: OPERAND ORDER — division is not commutative =="
sub "$FD_SPEC" "IRBinOp.fdiv ir_fd_tf64 ir_d1 ir_d2" "IRBinOp.fdiv ir_fd_tf64 ir_d2 ir_d1"
expect FAIL "P6 mutated: b / a instead of a / b"; reason
sub "$FD_SPEC" "IRBinOp.fdiv ir_fd_tf64 ir_d2 ir_d1" "IRBinOp.fdiv ir_fd_tf64 ir_d1 ir_d2"
expect PASS "P6 reverted"

echo
echo "== P7: THE RESULT ID the binop binds =="
sub "$FD_SPEC" "ir_fd_tf64 ir_d1 ir_d2) ir_d3)" "ir_fd_tf64 ir_d1 ir_d2) ir_d4)"
expect FAIL "P7 mutated: the quotient is bound at %4 while the ret still reads %3"; reason
sub "$FD_SPEC" "ir_fd_tf64 ir_d1 ir_d2) ir_d4)" "ir_fd_tf64 ir_d1 ir_d2) ir_d3)"
expect PASS "P7 reverted"

echo
echo "== P8: THE BLOCK ID =="
sub "$FD_SPEC" "IRBlock.mk ir_d0 ir_nl0" "IRBlock.mk ir_d1 ir_nl0"
expect FAIL "P8 mutated: the only block is bb1, and the function still enters at bb0"; reason
sub "$FD_SPEC" "IRBlock.mk ir_d1 ir_nl0" "IRBlock.mk ir_d0 ir_nl0"
expect PASS "P8 reverted"

echo
echo "== P9: THE PARAMETER LIST — the closure environment pointer dropped =="
sub "$FD_SPEC" "IRFunc.mk ir_d0 (ir_nl3 ir_d0 ir_d1 ir_d2) ir_d0" "IRFunc.mk ir_d0 (ir_nl2 ir_d1 ir_d2) ir_d0"
expect FAIL "P9 mutated: two parameters where the artifact takes three, so every operand id shifts"; reason
sub "$FD_SPEC" "IRFunc.mk ir_d0 (ir_nl2 ir_d1 ir_d2) ir_d0" "IRFunc.mk ir_d0 (ir_nl3 ir_d0 ir_d1 ir_d2) ir_d0"
expect PASS "P9 reverted"

echo
echo "== P10: THE ENTRY BLOCK the function starts at =="
sub "$FD_SPEC" "(ir_nl3 ir_d0 ir_d1 ir_d2) ir_d0 (ir_blk" "(ir_nl3 ir_d0 ir_d1 ir_d2) ir_d1 (ir_blk"
expect FAIL "P10 mutated: the function enters at bb1, which does not exist"; reason
sub "$FD_SPEC" "(ir_nl3 ir_d0 ir_d1 ir_d2) ir_d1 (ir_blk" "(ir_nl3 ir_d0 ir_d1 ir_d2) ir_d0 (ir_blk"
expect PASS "P10 reverted"

# NOT A CASE, and recorded rather than omitted: giving bb0 a BLOCK PARAMETER
# (`IRBlock.mk ir_d0 (ir_nl1 ir_d9)`) is NOT caught, and should not be. The
# `param_blocks` lane excludes the entry block on BOTH sides by construction,
# because on the emitted side bb0's parameter list IS the function signature
# (`bb0(%0: ptr, %1: f64, %2: f64)`) while on the Clean side those ids live in
# `IRFunc`. The signature is compared instead, explicitly, by the gate's
# `IRFunc.mk ir_d0 (ir_nl3 ir_d0 ir_d1 ir_d2) ir_d0` assertion and by P9/P10.
# Measured: the mutation above ran green before it was replaced.

# ────────────────────────── the emitted FIXTURE ────────────────────────────

echo
echo "== P11: THE ARTIFACT SIDE at binary32 =="
sub "$FD_FIX" "fdiv f64 %1, %2" "fdiv f32 %1, %2"
expect FAIL "P11 mutated: the emitted instruction is at binary32 and the proved module at binary64"; reason
sub "$FD_FIX" "fdiv f32 %1, %2" "fdiv f64 %1, %2"
expect PASS "P11 reverted"

echo
echo "== P12: THE ARTIFACT SIDE returns its argument =="
sub "$FD_FIX" "ret %3" "ret %1"
expect FAIL "P12 mutated: the emitted body returns %1"; reason
sub "$FD_FIX" "ret %1" "ret %3"
expect PASS "P12 reverted"

echo
echo "== P13: THE ARTIFACT SIDE's parameter list =="
sub "$FD_FIX" "bb0(%0: ptr, %1: f64, %2: f64):" "bb0(%1: f64, %2: f64):"
expect FAIL "P13 mutated: the emitted signature loses the closure environment pointer"; reason
sub "$FD_FIX" "bb0(%1: f64, %2: f64):" "bb0(%0: ptr, %1: f64, %2: f64):"
expect PASS "P13 reverted"

echo
echo "== P14: THE ARTIFACT SIDE's operator =="
sub "$FD_FIX" "%3 = fdiv f64" "%3 = fsub f64"
expect FAIL "P14 mutated: the emitted instruction is a subtraction"; reason
sub "$FD_FIX" "%3 = fsub f64" "%3 = fdiv f64"
expect PASS "P14 reverted"

echo
echo "== P15: FIXTURE DELETED — the gate must fail CLOSED, not vacuously pass =="
mv "$FD_FIX" "$FD_FIX.bak"
expect FAIL "P15 mutated: emitted trust-ir fixture absent"; reason
mv "$FD_FIX.bak" "$FD_FIX"
expect PASS "P15 reverted"

echo
echo "== P16: FIXTURE EMPTIED =="
cp "$FD_FIX" "$FD_FIX.bak"; : > "$FD_FIX"
expect FAIL "P16 mutated: emitted fixture is zero bytes"; reason
mv "$FD_FIX.bak" "$FD_FIX"
expect PASS "P16 reverted"

echo
echo "== P17: EVIDENCE FILE DELETED — fail closed as well =="
mv "$FD_JSON" "$FD_JSON.bak"
expect FAIL "P17 mutated: the A0/A6 evidence is absent"; reason
mv "$FD_JSON.bak" "$FD_JSON"
expect PASS "P17 reverted"

# ──────────────────────────── the A0/A6 evidence ───────────────────────────

echo
echo "== P18: markers_exact NON-VACUITY (the four real marker lines) =="
sub "$FD_JSON" '"markers_detail": "4 marker line(s) identical"' '"markers_detail": "0 marker line(s) identical"'
expect FAIL "P18 mutated: the 4-line marker sequence becomes empty, i.e. markers_exact goes vacuous"; reason
sub "$FD_JSON" '"markers_detail": "0 marker line(s) identical"' '"markers_detail": "4 marker line(s) identical"'
expect PASS "P18 reverted"

echo
echo "== P19: markers_exact itself =="
sub "$FD_JSON" '"markers_exact": true' '"markers_exact": false'
expect FAIL "P19 mutated: the -O marker gate did not hold"; reason
sub "$FD_JSON" '"markers_exact": false' '"markers_exact": true'
expect PASS "P19 reverted"

echo
echo "== P20: the FLIP EVENT's lineage digest, by one nibble =="
# TWO leading spaces: the FLIP EVENT's lineage is nested one level deeper than
# the coverage row's, so this anchor reaches the event and not the artifact.
# Changing the event's digest alone is exactly the A6 failure — the artifact
# inspected is not the artifact compiled.
sub "$FD_JSON" '  "lineage": "sha256:a457b9c0197a8edba9e8ade5749f0f78a263feccd13bd190f52c23399f21f238"' '  "lineage": "sha256:a457b9c0197a8edba9e8ade5749f0f78a263feccd13bd190f52c23399f21f239"'
expect FAIL "P20 mutated: the artifact inspected is not the artifact compiled"; reason
sub "$FD_JSON" '  "lineage": "sha256:a457b9c0197a8edba9e8ade5749f0f78a263feccd13bd190f52c23399f21f239"' '  "lineage": "sha256:a457b9c0197a8edba9e8ade5749f0f78a263feccd13bd190f52c23399f21f238"'
expect PASS "P20 reverted"

echo
echo "== P21: the flip event FIRED =="
sub "$FD_JSON" '"fired": true' '"fired": false'
expect FAIL "P21 mutated: no codegen flip, so the derived IR is a side model"; reason
sub "$FD_JSON" '"fired": false' '"fired": true'
expect PASS "P21 reverted"

echo
echo "== P22: the flip SEAM =="
sub "$FD_JSON" '"seam": "codegen"' '"seam": "ctfe"'
expect FAIL "P22 mutated: a CTFE flip is not the shipped object code"; reason
sub "$FD_JSON" '"seam": "ctfe"' '"seam": "codegen"'
expect PASS "P22 reverted"

echo
echo "== P23: the NEGATIVE CONTROL =="
sub "$FD_JSON" '"flip_events_crate_wide": 0' '"flip_events_crate_wide": 1'
expect FAIL "P23 mutated: -Ztrust-ir-flip=no produced an event, so the flag proves nothing"; reason
sub "$FD_JSON" '"flip_events_crate_wide": 1' '"flip_events_crate_wide": 0'
expect PASS "P23 reverted"

echo
echo "== P24: the INTERPRETER differential's sample count =="
sub "$FD_JSON" '"samples": 64' '"samples": 0'
expect FAIL "P24 mutated: \`agreed\` on zero samples is a vacuous agreement"; reason
sub "$FD_JSON" '"samples": 0' '"samples": 64'
expect PASS "P24 reverted"

echo
echo "== P25: the CALL COUNT — bodyful reachable closure =="
sub "$FD_JSON" '  "resolved": 0,' '  "resolved": 1,'
expect FAIL "P25 mutated: a resolved call reopens the closure question"; reason
sub "$FD_JSON" '  "resolved": 1,' '  "resolved": 0,'
expect PASS "P25 reverted"

echo
echo "== P26: the LINEAGE DOMAIN version =="
sub "$FD_JSON" '"lineage_domain": "trust_thir_lower.body_lineage.v2"' '"lineage_domain": "trust_thir_lower.body_lineage.v3"'
expect FAIL "P26 mutated: a digest and its domain travel together or neither means anything"; reason
sub "$FD_JSON" '"lineage_domain": "trust_thir_lower.body_lineage.v3"' '"lineage_domain": "trust_thir_lower.body_lineage.v2"'
expect PASS "P26 reverted"

echo
echo "== P27: the REPRODUCTION claim =="
sub "$FD_JSON" '"coverage_json_byte_identical_across_all_three": true' '"coverage_json_byte_identical_across_all_three": false'
expect FAIL "P27 mutated: one observation is not a measurement"; reason
sub "$FD_JSON" '"coverage_json_byte_identical_across_all_three": false' '"coverage_json_byte_identical_across_all_three": true'
expect PASS "P27 reverted"

echo
echo "== P28: the PROVEN-NEVER-READ environment pointer =="
sub "$FD_JSON" 'proven-never-read opaque param(s) as placeholders' 'opaque param(s) as placeholders'
expect FAIL "P28 mutated: without the producer's own never-read record, quantifying over the environment pointer with no premise is an assumption"; reason
sub "$FD_JSON" 'opaque param(s) as placeholders' 'proven-never-read opaque param(s) as placeholders'
expect PASS "P28 reverted"

# ─────────────────────── the float-semantics wall itself ───────────────────

echo
echo "== P29: THE SEMANTICS WALL's answer =="
sub "$FD_JSON" '"answer": "PARTLY' '"answer": "YES, fully'
expect FAIL "P29 mutated: the boundary is claimed away"; reason
sub "$FD_JSON" '"answer": "YES, fully' '"answer": "PARTLY'
expect PASS "P29 reverted"

echo
echo "== P30: THE SEMANTICS WALL's trust cost =="
sub "$FD_JSON" '"accelerated_constants_added": 0' '"accelerated_constants_added": 1'
expect FAIL "P30 mutated: the classification would have been bought with a new accelerated constant"; reason
sub "$FD_JSON" '"accelerated_constants_added": 1' '"accelerated_constants_added": 0'
expect PASS "P30 reverted"

echo
echo "== P31: the NaN refusal's REASON =="
sub "$FD_JSON" 'is implementation-defined (IEEE 754-2019 6.2.3 says `should`)' 'is not modelled here'
expect FAIL "P31 mutated: a wall in the STANDARD is recorded as a gap in the model"; reason
sub "$FD_JSON" 'is not modelled here' 'is implementation-defined (IEEE 754-2019 6.2.3 says `should`)'
expect PASS "P31 reverted"

echo
echo "== P32: a SIBLING closure's recorded lineage =="
sub "$FD_JSON" '"lineage": "sha256:21501d78053d7cc053554ffa9aa1d83770c3610fccf394aed4da3caffb2b5421"' '"lineage": "sha256:21501d78053d7cc053554ffa9aa1d83770c3610fccf394aed4da3caffb2b5422"'
expect FAIL "P32 mutated: reduce_float_add's recorded digest is wrong, so the next lane would chain against a body that is not the one measured"; reason
sub "$FD_JSON" '"lineage": "sha256:21501d78053d7cc053554ffa9aa1d83770c3610fccf394aed4da3caffb2b5422"' '"lineage": "sha256:21501d78053d7cc053554ffa9aa1d83770c3610fccf394aed4da3caffb2b5421"'
expect PASS "P32 reverted"

echo
echo "== P33: the FCmp closures' recorded non-chainability =="
sub "$FD_JSON" '"env::native_reducers_float::reduce_float_beq::{closure#0}": "derived_mir unsupported: `shim: Inst::FCmp`"' '"env::native_reducers_float::reduce_float_beq::{closure#0}": "chainable"'
expect FAIL "P33 mutated: an unsupported body is recorded as available"; reason
sub "$FD_JSON" '"env::native_reducers_float::reduce_float_beq::{closure#0}": "chainable"' '"env::native_reducers_float::reduce_float_beq::{closure#0}": "derived_mir unsupported: `shim: Inst::FCmp`"'
expect PASS "P33 reverted"

echo
echo "== P34: the VACUITY figure this lane re-derived =="
sub "$FD_JSON" '"markers_exact_rows_that_are_NON_vacuous": 27' '"markers_exact_rows_that_are_NON_vacuous": 1084'
expect FAIL "P34 mutated: 1084 markers_exact rows read as 1084 checked bodies"; reason
sub "$FD_JSON" '"markers_exact_rows_that_are_NON_vacuous": 1084' '"markers_exact_rows_that_are_NON_vacuous": 27'
expect PASS "P34 reverted"

echo
echo "PERTURBATIONS: $pass expected outcomes, $fail unexpected"
[[ $fail -eq 0 ]]
