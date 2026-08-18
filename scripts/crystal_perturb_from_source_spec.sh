#!/usr/bin/env bash
# Perturbation proofs for the SEMANTICS side: the new IRConst aggregate
# evaluation case and the re-authored ir_const_value. These require a rebuild,
# because the gate is the ELABORATOR — each witness is an Eq.refl the kernel
# must discharge by running the evaluator.
set -uo pipefail
OUT="$(mktemp)"; trap 'rm -f "$OUT"' EXIT
REPO="$(cd "$(dirname "$0")/.." && pwd -P)"
OPS="$REPO/crates/clean-verify/src/spec/core_spec/eval_ir_ops.rs"

pass=0; fail=0
run() { (cd "$REPO" && cargo test --locked -p clean-verify --test eval_ir --message-format=short) >"$OUT" 2>&1; }
expect() {
  run; rc=$?
  want="$1"; label="$2"
  if [[ "$want" == "PASS" && $rc -eq 0 ]] || [[ "$want" == "FAIL" && $rc -ne 0 ]]; then
    echo "OK   [$want] $label"; pass=$((pass+1))
  else
    echo "BAD  [want $want rc=$rc] $label"; tail -20 "$OUT"; fail=$((fail+1))
  fi
}
reason() { grep -oE "(SpecError|Elaboration|failed to elaborate|panicked at [^\"]*|kernel|Type mismatch|expected|test result: FAILED[^\"]*)" "$OUT" | head -4;
           grep -m2 -oE "(ir_const[a-z_]*|Eq\.refl[^\"]{0,60})" "$OUT" | head -2;
           grep -m1 -E "assertion|elaborat|mismatch|Failed" "$OUT" | cut -c1-300; }
# A silent no-substitution would make a MUTATED run look green, which is the
# one false negative this methodology cannot tolerate — so the anchor must occur
# exactly once and a miss aborts the run.
sub() { python3 - "$1" "$2" "$3" <<'PY'
import sys
p,a,b=sys.argv[1],sys.argv[2],sys.argv[3]
s=open(p).read()
assert a in s and s.count(a)==1, "anchor must occur exactly once: %s" % a[:60]
open(p,'w').write(s.replace(a,b,1))
PY
} || exit 9

echo "== baseline =="
expect PASS "baseline: eval_ir green"

echo
echo "== P11: ir_const_agg_eval's type check inverted =="
sub "$OPS" '"(IRStepResult.fault (IROutcome.type_error IRFault.not_agg)) ",
                "(IRStepResult.value (IRScalar.aggv (ir_const_value sp))) ",
                "(ir_ty_is_agg t)",' '"(IRStepResult.value (IRScalar.aggv (ir_const_value sp))) ",
                "(IRStepResult.fault (IROutcome.type_error IRFault.not_agg)) ",
                "(ir_ty_is_agg t)",'
expect FAIL "P11 mutated: aggregate constants accepted at scalar types and rejected at aggregate types"; reason
sub "$OPS" '"(IRStepResult.value (IRScalar.aggv (ir_const_value sp))) ",
                "(IRStepResult.fault (IROutcome.type_error IRFault.not_agg)) ",
                "(ir_ty_is_agg t)",' '"(IRStepResult.fault (IROutcome.type_error IRFault.not_agg)) ",
                "(IRStepResult.value (IRScalar.aggv (ir_const_value sp))) ",
                "(ir_ty_is_agg t)",'
expect PASS "P11 reverted"

echo
echo "== P12: the aggregate materialization STUBBED =="
sub "$OPS" '"(fun (_sp : IRConst) (ih : IRScalar) => IRScalar.aggv ih) ",' '"(fun (_sp : IRConst) (ih : IRScalar) => IRScalar.undef_) ",'
expect FAIL "P12 mutated: ir_const_value's aggregate arm returns undef_ — a STUB instead of a value"; reason
sub "$OPS" '"(fun (_sp : IRConst) (ih : IRScalar) => IRScalar.undef_) ",' '"(fun (_sp : IRConst) (ih : IRScalar) => IRScalar.aggv ih) ",'
expect PASS "P12 reverted"

echo
echo "== P13: two PRE-EXISTING minors transposed in the new recursor =="
sub "$OPS" '"IRScalar.unit_ ",
                "IRScalar.nullptr_ ",' '"IRScalar.nullptr_ ",
                "IRScalar.unit_ ",'
expect FAIL "P13 mutated: ir_const_value's unit_ and null_ minors swapped"; reason
sub "$OPS" '"IRScalar.nullptr_ ",
                "IRScalar.unit_ ",' '"IRScalar.unit_ ",
                "IRScalar.nullptr_ ",'
expect PASS "P13 reverted"

echo
echo "== P14: ir_ty_is_agg widened to accept a scalar type =="
sub "$OPS" '| IRTy.uint_ w => Bool.false
| IRTy.float_ w => Bool.false
| IRTy.ptr_ => Bool.false
| IRTy.ref_ p => Bool.false
| IRTy.refmut_ p => Bool.false
| IRTy.rawconst_ p => Bool.false
| IRTy.rawmut_ p => Bool.false
| IRTy.rc_ p => Bool.false
| IRTy.fatptr_ p => Bool.false' '| IRTy.uint_ w => Bool.true
| IRTy.float_ w => Bool.false
| IRTy.ptr_ => Bool.false
| IRTy.ref_ p => Bool.false
| IRTy.refmut_ p => Bool.false
| IRTy.rawconst_ p => Bool.false
| IRTy.rawmut_ p => Bool.false
| IRTy.rc_ p => Bool.false
| IRTy.fatptr_ p => Bool.false'
expect FAIL "P14 mutated: uint_ counts as an aggregate type, so the fail-closed edge disappears"; reason
sub "$OPS" '| IRTy.uint_ w => Bool.true
| IRTy.float_ w => Bool.false
| IRTy.ptr_ => Bool.false
| IRTy.ref_ p => Bool.false
| IRTy.refmut_ p => Bool.false
| IRTy.rawconst_ p => Bool.false
| IRTy.rawmut_ p => Bool.false
| IRTy.rc_ p => Bool.false
| IRTy.fatptr_ p => Bool.false' '| IRTy.uint_ w => Bool.false
| IRTy.float_ w => Bool.false
| IRTy.ptr_ => Bool.false
| IRTy.ref_ p => Bool.false
| IRTy.refmut_ p => Bool.false
| IRTy.rawconst_ p => Bool.false
| IRTy.rawmut_ p => Bool.false
| IRTy.rc_ p => Bool.false
| IRTy.fatptr_ p => Bool.false'
expect PASS "P14 reverted"

echo
echo "SPEC PERTURBATIONS: $pass expected outcomes, $fail unexpected"
[[ $fail -eq 0 ]]
