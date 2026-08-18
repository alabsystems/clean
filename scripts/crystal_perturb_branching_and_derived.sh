#!/usr/bin/env bash
# Perturbation proofs for the SIXTH and SEVENTH chains' gates:
#   env::native_reducers_char::is_valid_char                 (2 condbrs, 3 icmps, width 64)
#   <tc::expr_location::ExprPathStep as Clone>::clone        (13 blocks, 10 cases + default)
#
# Same contract as scripts/crystal_perturb_computing_chains.sh: the CFG and
# evidence gates read the spec source text and the fixtures from disk at RUNTIME
# (CARGO_MANIFEST_DIR), so the compiled test binary is driven directly. A
# perturbation is a file edit, the binary re-reads it, and no rebuild is
# involved. Each case mutates, asserts FAIL, reverts, asserts PASS.
#
# Four cases here could not have been written before this lane, because the two
# bodies contain constructs no earlier chained body has:
#
#   Q3  exchanges the entry condbr's targets. is_valid_char branches to the
#       HIGHER block on the true edge; bvar_in_range branches to the lower one.
#       Copying the fifth chain's polarity computes the NEGATION of this body and
#       leaves every other lane bit-identical.
#   Q4  exchanges the operands of the one icmp whose constant is on the LEFT.
#       `0xDFFF < n` becomes `n < 0xDFFF`; same op, same result id, same blocks.
#   Q11 drops the default edge's arm to a duplicate of another variant's — a
#       clone that answers the wrong variant for ProjExpr and no other.
#   Q12 renumbers one switch case, which is what a case table transcribed as
#       0..10 instead of 0..9-plus-default looks like.
#
# Usage:
#   CRYSTAL_BIN=<path to the compiled crystal_a1_lineage test binary> \
#     scripts/crystal_perturb_branching_and_derived.sh
set -uo pipefail
OUT="$(mktemp)"; trap 'rm -f "$OUT"' EXIT
REPO="$(cd "$(dirname "$0")/.." && pwd -P)"
BIN="${CRYSTAL_BIN:?set CRYSTAL_BIN to the compiled crystal_a1_lineage test binary}"

VC_SPEC="$REPO/crates/clean-verify/src/spec/core_spec/eval_ir_valid_char.rs"
VC_FIX="$REPO/crates/clean-verify/tests/fixtures/is_valid_char.trust-ir.txt"
VC_JSON="$REPO/crates/clean-verify/tests/fixtures/is_valid_char.lineage.json"
EP_SPEC="$REPO/crates/clean-verify/src/spec/core_spec/eval_ir_path_step.rs"
EP_FIX="$REPO/crates/clean-verify/tests/fixtures/expr_path_step_clone.trust-ir.txt"
EP_JSON="$REPO/crates/clean-verify/tests/fixtures/expr_path_step_clone.lineage.json"

pass=0; fail=0
run() { "$BIN" "${FILTER:-}" --test-threads=1 >"$OUT" 2>&1; }

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

# Substitute inside the DECLARATION lines only. The spec modules also carry unit
# tests that quote the same block sources verbatim, so a whole-file anchor is not
# unique; a silent no-substitution would make a MUTATED run look green, which is
# the exact false negative this script exists to rule out.
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
} || exit 9

echo "== baseline =="
expect PASS "baseline: all crystal_a1_lineage gates green"

# ───────────────────────────── is_valid_char ─────────────────────────────
FILTER=is_valid_char

echo
echo "== Q1: the surrogate-block LOWER boundary =="
sub "$VC_SPEC" "(IRConst.int_ 55296)" "(IRConst.int_ 55295)"
expect FAIL "Q1 mutated: 0xD800 becomes 0xD7FF — one code point of the Unicode range"; reason
sub "$VC_SPEC" "(IRConst.int_ 55295)" "(IRConst.int_ 55296)"
expect PASS "Q1 reverted"

echo
echo "== Q2: the MAXIMUM code point =="
sub "$VC_SPEC" "(IRConst.int_ 1114112)" "(IRConst.int_ 1114111)"
expect FAIL "Q2 mutated: 0x110000 becomes 0x10FFFF — an off-by-one at the top of the range"; reason
sub "$VC_SPEC" "(IRConst.int_ 1114111)" "(IRConst.int_ 1114112)"
expect PASS "Q2 reverted"

echo
echo "== Q3: the entry CONDBR's two targets =="
sub "$VC_SPEC" "(IRInst.condbr ir_d4 ir_d2 ir_nl0 ir_d1 ir_nl0)" "(IRInst.condbr ir_d4 ir_d1 ir_nl0 ir_d2 ir_nl0)"
expect FAIL "Q3 mutated: the true and false edges exchanged — the body now computes its NEGATION, and every other lane is bit-identical"; reason
sub "$VC_SPEC" "(IRInst.condbr ir_d4 ir_d1 ir_nl0 ir_d2 ir_nl0)" "(IRInst.condbr ir_d4 ir_d2 ir_nl0 ir_d1 ir_nl0)"
expect PASS "Q3 reverted"

echo
echo "== Q4: the LEFT-OPERAND comparison's operand order =="
sub "$VC_SPEC" "(IRInst.icmp IRICmpOp.ult ir_vc_tu64 ir_d5 ir_d0) ir_d6" "(IRInst.icmp IRICmpOp.ult ir_vc_tu64 ir_d0 ir_d5) ir_d6"
expect FAIL "Q4 mutated: 0xDFFF < n becomes n < 0xDFFF — same op, same result id, same graph"; reason
sub "$VC_SPEC" "(IRInst.icmp IRICmpOp.ult ir_vc_tu64 ir_d0 ir_d5) ir_d6" "(IRInst.icmp IRICmpOp.ult ir_vc_tu64 ir_d5 ir_d0) ir_d6"
expect PASS "Q4 reverted"

echo
echo "== Q5: the COMPARISON OPERATOR =="
sub "$VC_SPEC" "(IRInst.icmp IRICmpOp.ult ir_vc_tu64 ir_d0 ir_d8) ir_d9" "(IRInst.icmp IRICmpOp.ule ir_vc_tu64 ir_d0 ir_d8) ir_d9"
expect FAIL "Q5 mutated: ult becomes ule at the upper bound — the two differ at exactly one input"; reason
sub "$VC_SPEC" "(IRInst.icmp IRICmpOp.ule ir_vc_tu64 ir_d0 ir_d8) ir_d9" "(IRInst.icmp IRICmpOp.ult ir_vc_tu64 ir_d0 ir_d8) ir_d9"
expect PASS "Q5 reverted"

echo
echo "== Q6: the SHORT CIRCUIT's constant =="
sub "$VC_SPEC" "(IRConst.bool_ Bool.false)) ir_d10" "(IRConst.bool_ Bool.true)) ir_d10"
expect FAIL "Q6 mutated: the &&'s untaken side answers true — every surrogate becomes valid"; reason
sub "$VC_SPEC" "(IRConst.bool_ Bool.true)) ir_d10" "(IRConst.bool_ Bool.false)) ir_d10"
expect PASS "Q6 reverted"

echo
echo "== Q7: the INNER join's forwarding edge =="
sub "$VC_SPEC" "def ir_vc_b6 : IRBlock := IRBlock.mk ir_d6 (ir_nl1 ir_d2) (ir_bd1 (ir_nd (IRInst.br ir_d3 (ir_nl1 ir_d2))))" "def ir_vc_b6 : IRBlock := IRBlock.mk ir_d6 (ir_nl1 ir_d2) (ir_bd1 (ir_nd (IRInst.br ir_d2 (ir_nl1 ir_d2))))"
expect FAIL "Q7 mutated: the inner join forwards to bb2 instead of the outer join bb3"; reason
sub "$VC_SPEC" "def ir_vc_b6 : IRBlock := IRBlock.mk ir_d6 (ir_nl1 ir_d2) (ir_bd1 (ir_nd (IRInst.br ir_d2 (ir_nl1 ir_d2))))" "def ir_vc_b6 : IRBlock := IRBlock.mk ir_d6 (ir_nl1 ir_d2) (ir_bd1 (ir_nd (IRInst.br ir_d3 (ir_nl1 ir_d2))))"
expect PASS "Q7 reverted"

echo
echo "== Q8: markers_exact NON-VACUITY =="
sub "$VC_JSON" '"markers_detail": "12 marker line(s) identical"' '"markers_detail": "0 marker line(s) identical"'
expect FAIL "Q8 mutated: the 12-line marker sequence becomes empty"; reason
sub "$VC_JSON" '"markers_detail": "0 marker line(s) identical"' '"markers_detail": "12 marker line(s) identical"'
expect PASS "Q8 reverted"

echo
echo "== Q9: the flip-event lineage digest =="
sub "$VC_JSON" '  "lineage": "sha256:2f956ee9513cd6245a388d58176dd87f0a19ad6d70b00fae4d464e0e0875ce7b",' '  "lineage": "sha256:2f956ee9513cd6245a388d58176dd87f0a19ad6d70b00fae4d464e0e0875ce7c",'
expect FAIL "Q9 mutated: the FLIP EVENT's lineage differs from the coverage row's by one nibble"; reason
sub "$VC_JSON" '  "lineage": "sha256:2f956ee9513cd6245a388d58176dd87f0a19ad6d70b00fae4d464e0e0875ce7c",' '  "lineage": "sha256:2f956ee9513cd6245a388d58176dd87f0a19ad6d70b00fae4d464e0e0875ce7b",'
expect PASS "Q9 reverted"

echo
echo "== Q10: the RESIDUE COST LAW's own measurements =="
sub "$VC_JSON" '"w8_n7000": 1.356' '"w8_n7000": 12.9'
expect FAIL "Q10 mutated: the width-8 point is made 10x the width-64 point, i.e. the law becomes width-dependent again"; reason
sub "$VC_JSON" '"w8_n7000": 12.9' '"w8_n7000": 1.356'
expect PASS "Q10 reverted"

# ─────────────────────────── expr_path_step_clone ─────────────────────────
FILTER=expr_path_step_clone

echo
echo "== Q11: the DEFAULT edge's answer =="
sub "$EP_SPEC" "(IRInst.const_ ir_ep_tstep (ir_cvar ir_d10)) ir_d14" "(IRInst.const_ ir_ep_tstep (ir_cvar ir_d9)) ir_d14"
expect FAIL "Q11 mutated: cloning a ProjExpr yields an MDataExpr — wrong for exactly one variant, the one with no explicit case"; reason
sub "$EP_SPEC" "(IRInst.const_ ir_ep_tstep (ir_cvar ir_d9)) ir_d14" "(IRInst.const_ ir_ep_tstep (ir_cvar ir_d10)) ir_d14"
expect PASS "Q11 reverted"

echo
echo "== Q12: a SWITCH CASE's selector =="
sub "$EP_SPEC" "(ir_sc ir_d9 ir_d10 ir_sc0)" "(ir_sc ir_d10 ir_d10 ir_sc0)"
expect FAIL "Q12 mutated: case 9 becomes case 10 — the table a transcription reading 0..10 would produce"; reason
sub "$EP_SPEC" "(ir_sc ir_d10 ir_d10 ir_sc0)" "(ir_sc ir_d9 ir_d10 ir_sc0)"
expect PASS "Q12 reverted"

echo
echo "== Q13: the SWITCH DEFAULT's target =="
sub "$EP_SPEC" "(IRInst.switch ir_d3 ir_d11 ir_nl0" "(IRInst.switch ir_d3 ir_d12 ir_nl0"
expect FAIL "Q13 mutated: the default edge goes to the JOIN block instead of the ProjExpr arm"; reason
sub "$EP_SPEC" "(IRInst.switch ir_d3 ir_d12 ir_nl0" "(IRInst.switch ir_d3 ir_d11 ir_nl0"
expect PASS "Q13 reverted"

echo
echo "== Q14: the LOAD's pointer operand =="
sub "$EP_SPEC" "(IRInst.load ir_ep_tstep ir_d0 Bool.false) ir_d2" "(IRInst.load ir_ep_tstep ir_d1 Bool.false) ir_d2"
expect FAIL "Q14 mutated: the body loads through %1 instead of through its own &self parameter"; reason
sub "$EP_SPEC" "(IRInst.load ir_ep_tstep ir_d1 Bool.false) ir_d2" "(IRInst.load ir_ep_tstep ir_d0 Bool.false) ir_d2"
expect PASS "Q14 reverted"

echo
echo "== Q15: the EXTRACTFIELD's field index =="
sub "$EP_SPEC" "(IRInst.extractfield ir_tU8 ir_d2 ir_d0) ir_d3" "(IRInst.extractfield ir_tU8 ir_d2 ir_d1) ir_d3"
expect FAIL "Q15 mutated: the discriminant is read from field 1 instead of field 0"; reason
sub "$EP_SPEC" "(IRInst.extractfield ir_tU8 ir_d2 ir_d1) ir_d3" "(IRInst.extractfield ir_tU8 ir_d2 ir_d0) ir_d3"
expect PASS "Q15 reverted"

echo
echo "== Q16: an ARM's branch target =="
sub "$EP_SPEC" "(IRInst.br ir_d12 (ir_nl1 ir_d7))" "(IRInst.br ir_d11 (ir_nl1 ir_d7))"
expect FAIL "Q16 mutated: the LamType arm falls into the ProjExpr arm instead of the join"; reason
sub "$EP_SPEC" "(IRInst.br ir_d11 (ir_nl1 ir_d7))" "(IRInst.br ir_d12 (ir_nl1 ir_d7))"
expect PASS "Q16 reverted"

echo
echo "== Q17: the recorded VACUITY of markers_exact =="
sub "$EP_JSON" '"markers_detail": "0 marker line(s) identical"' '"markers_detail": "9 marker line(s) identical"'
expect FAIL "Q17 mutated: the fixture claims marker content this body does not have — the gate asserts the vacuity in BOTH directions, so an overclaim fails too"; reason
sub "$EP_JSON" '"markers_detail": "9 marker line(s) identical"' '"markers_detail": "0 marker line(s) identical"'
expect PASS "Q17 reverted"

echo
echo "== Q18: the CANONICAL-line count this chain actually rests on =="
sub "$EP_JSON" '"detail": "16 canonical line(s) identical"' '"detail": "3 canonical line(s) identical"'
expect FAIL "Q18 mutated: with the marker channel vacuous here, the canonical count IS the evidence"; reason
sub "$EP_JSON" '"detail": "3 canonical line(s) identical"' '"detail": "16 canonical line(s) identical"'
expect PASS "Q18 reverted"

echo
echo "== Q19: the interpreter differential's honesty =="
sub "$EP_JSON" '"samples": 0,' '"samples": 125,'
expect FAIL "Q19 mutated: the fixture claims 125 interpreter samples for a differential the producer refused to run"; reason
sub "$EP_JSON" '"samples": 125,' '"samples": 0,'
expect PASS "Q19 reverted"

# ───────────────────────── fail-closed, both chains ───────────────────────
echo
echo "== Q20: is_valid_char FIXTURE DELETED — the gate must fail CLOSED =="
FILTER=is_valid_char
mv "$VC_FIX" "$VC_FIX.bak"
expect FAIL "Q20 mutated: emitted trust-ir fixture absent"; reason
mv "$VC_FIX.bak" "$VC_FIX"
expect PASS "Q20 reverted"

echo
echo "== Q21: is_valid_char FIXTURE EMPTIED =="
cp "$VC_FIX" "$VC_FIX.bak"; : > "$VC_FIX"
expect FAIL "Q21 mutated: emitted fixture is zero bytes"; reason
mv "$VC_FIX.bak" "$VC_FIX"
expect PASS "Q21 reverted"

echo
echo "== Q22: expr_path_step_clone FIXTURE DELETED =="
FILTER=expr_path_step_clone
mv "$EP_FIX" "$EP_FIX.bak"
expect FAIL "Q22 mutated: emitted trust-ir fixture absent"; reason
mv "$EP_FIX.bak" "$EP_FIX"
expect PASS "Q22 reverted"

echo
echo "== Q23: expr_path_step_clone FIXTURE EMPTIED =="
cp "$EP_FIX" "$EP_FIX.bak"; : > "$EP_FIX"
expect FAIL "Q23 mutated: emitted fixture is zero bytes"; reason
mv "$EP_FIX.bak" "$EP_FIX"
expect PASS "Q23 reverted"

echo
echo "== Q24: markers_detail ZEROED on the NON-vacuous chain (the non-vacuity check) =="
FILTER=is_valid_char
sub "$VC_JSON" '"markers_exact_rows_that_are_NON_vacuous": 27' '"markers_exact_rows_that_are_NON_vacuous": 0'
expect FAIL "Q24 mutated: the whole-crate non-vacuous denominator becomes zero, which would make this chain's distinguishing claim unstatable"; reason
sub "$VC_JSON" '"markers_exact_rows_that_are_NON_vacuous": 0' '"markers_exact_rows_that_are_NON_vacuous": 27'
expect PASS "Q24 reverted"

echo
echo "PERTURBATIONS: $pass expected outcomes, $fail unexpected"
[[ $fail -eq 0 ]]
