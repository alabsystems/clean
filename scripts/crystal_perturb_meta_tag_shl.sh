#!/usr/bin/env bash
# Perturbation proofs for the TENTH chain's gates:
#   tc::local_context::LocalContext::push_low_local::META_TAG
#
# The CFG / evidence gates read the spec source text and the fixtures from disk
# at RUNTIME (CARGO_MANIFEST_DIR), so the compiled test binary is driven
# directly: a perturbation is a file edit, the binary re-reads it, and no
# rebuild is involved. Each case mutates, asserts FAIL, reverts, asserts PASS.
#
# THE CASES THAT EXIST BECAUSE OF THIS CHAIN'S OWN LANES:
#   * P1-P4    — the ASSERT itself: deleted, on a different scrutinee, moved
#                after the shift, and given a result id. Before the `asserts`
#                lane, `Inst::Assert` was in NO lane — it binds no result,
#                carries no type and has no target, so DELETING it changed
#                nothing the gate read.
#   * P5-P7    — the assert's CONDITION negated three ways: the icmp operator,
#                its operand order, and its width.
#   * P8-P10   — WHERE THE ASSERT GOES WHEN IT FAILS. trust-ir has no target
#                operand, so the failing edge is pinned against the registered
#                SEMANTICS: redirect it to a different outcome, to a value, or
#                collapse the two-sidedness, and the gate must go red naming it.
#   * P11-P14  — the THREE constants in ONE block. The value lanes were keyed by
#                BLOCK until this chain and kept one of each kind, so changing
#                the second or third was invisible.
#   * P15-P18  — the TWO casts of one operand: opcode swap, each width.
#   * P19-P20  — a MULTI-RESULT node's ids, which the program-order lane read as
#                `u32::MAX` on both sides before its result slot became a list.
#   * P30+     — the recorded evidence: the CTFE-seam census, the link-2b
#                reading, the build items, and the correction this lane owes the
#                ninth chain's own record.
#
# The `sub` helper inherits the eighth chain's fix and the ninth's proof of it:
# a substitution that does not match exactly one declaration line is FATAL.
set -uo pipefail
OUT="$(mktemp)"; trap 'rm -f "$OUT"' EXIT
REPO="$(cd "$(dirname "$0")/.." && pwd -P)"
BIN="${CRYSTAL_BIN:?set CRYSTAL_BIN to the compiled crystal_a1_lineage test binary}"

MT_SPEC="$REPO/crates/clean-verify/src/spec/core_spec/eval_ir_meta_tag.rs"
MT_FIX="$REPO/crates/clean-verify/tests/fixtures/meta_tag_shl.trust-ir.txt"
MT_JSON="$REPO/crates/clean-verify/tests/fixtures/meta_tag_shl.lineage.json"

pass=0; fail=0
FILTER=meta_tag_shl
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
  if [[ $rc -ne 0 ]]; then
    echo "FATAL: substitution failed in $1 (anchor did not match exactly one declaration line)"
    exit 9
  fi
}

# The same, SCOPED TO ONE DECLARATION. The shipped module and its two
# counterfactuals are the same nine nodes with one constant changed, so almost
# every anchor into `ir_mt_b0` also matches `ir_mt_oob_b0` and `ir_mt_neg_b0` --
# three declaration lines, which the unscoped helper correctly REFUSES. Scoping
# keeps the exactly-one-match property (it is now exactly one occurrence inside
# the NAMED declaration) and adds the precision the three-way shape needs.
subin() { python3 - "$1" "$2" "$3" "$4" <<'PYEOF'
import sys
p, decl, a, b = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]
lines = open(p).read().split("\n")
head = "const %s:" % decl
hits = [i for i, l in enumerate(lines) if l.startswith(head)]
assert len(hits) == 1, "declaration %s must appear exactly once, matched %d" % (decl, len(hits))
i = hits[0]
assert lines[i].count(a) == 1, "anchor must occur exactly once in %s, occurred %d: %s" % (
    decl, lines[i].count(a), a[:80])
lines[i] = lines[i].replace(a, b, 1)
open(p, "w").write("\n".join(lines))
PYEOF
  rc=$?
  if [[ $rc -ne 0 ]]; then
    echo "FATAL: scoped substitution failed in $1 / $2 (anchor did not occur exactly once)"
    exit 9
  fi
}

snap() { cp -p "$1" "$1.snap"; }
restore() { mv -f "$1.snap" "$1"; }

echo "== baseline =="
expect PASS "baseline: all meta_tag_shl gates green"

# ── the GUARD ITSELF, proved rather than trusted ───────────────────────────
# `IRInst.const_ ir_vc_tu64 (IRConst.int_ 1)` appears in the shipped module AND
# in both counterfactual modules — three declaration lines — so an anchor on it
# must ABORT rather than silently mutate one of them.
echo
echo "== G0: the substitution guard ABORTS on an ambiguous anchor =="
( sub "$MT_SPEC" "IRInst.const_ ir_vc_tu64 (IRConst.int_ 1)" "IRInst.const_ ir_vc_tu64 (IRConst.int_ 2)" ) >/dev/null 2>&1
grc=$?
if [[ $grc -eq 9 ]]; then
  echo "OK   [ABORT] G0: an anchor matching 3 declaration lines is FATAL, not a silent no-op"
  pass=$((pass+1))
else
  echo "BAD  [want abort rc=9, rc=$grc] G0: the substitution guard did not fire"
  fail=$((fail+1))
fi
expect PASS "G0: the tree is untouched after the refused substitution"

# ───────────────────────────── THE PANIC ARM ───────────────────────────────

echo
echo "== P1: THE ASSERT, DELETED FROM THE PROVED MODULE =="
subin "$MT_SPEC" SRC_IR_MT_B0 "(ir_nd (IRInst.assert ir_d4)) (ir_nd1 (IRInst.cast IRCastOp.sext ir_mt_ti32 ir_vc_tu64 ir_d1) ir_d5)" "(ir_nd (IRInst.assert ir_d4)) (ir_nd (IRInst.assert ir_d4)) (ir_nd1 (IRInst.cast IRCastOp.sext ir_mt_ti32 ir_vc_tu64 ir_d1) ir_d5)"
expect FAIL "P1 mutated: the proved module asserts TWICE — the assert lane and the order lane both see it, and before the assert lane neither did"; reason
subin "$MT_SPEC" SRC_IR_MT_B0 "(ir_nd (IRInst.assert ir_d4)) (ir_nd (IRInst.assert ir_d4)) (ir_nd1 (IRInst.cast IRCastOp.sext ir_mt_ti32 ir_vc_tu64 ir_d1) ir_d5)" "(ir_nd (IRInst.assert ir_d4)) (ir_nd1 (IRInst.cast IRCastOp.sext ir_mt_ti32 ir_vc_tu64 ir_d1) ir_d5)"
expect PASS "P1 reverted"

echo
echo "== P2: THE ASSERT'S SCRUTINEE — %4 becomes %0 =="
subin "$MT_SPEC" SRC_IR_MT_B0 "IRInst.assert ir_d4" "IRInst.assert ir_d0"
expect FAIL "P2 mutated: the module asserts the CONSTANT 1 rather than the comparison — an integer, which ir_as_bool declines. The order lane cannot see it: same class, same empty result list"; reason
subin "$MT_SPEC" SRC_IR_MT_B0 "IRInst.assert ir_d0" "IRInst.assert ir_d4"
expect PASS "P2 reverted"

echo
echo "== P3: THE ASSERT, DELETED FROM THE ARTIFACT =="
snap "$MT_FIX"
python3 - "$MT_FIX" <<'PY'
import sys
p = sys.argv[1]
s = open(p).read()
assert s.count("    assert %4") == 1
open(p, "w").write(s.replace("    assert %4  ; #proof: shift_in_range  ; #loc: 435 157 30\n", ""))
PY
expect FAIL "P3 mutated: the artifact side loses its assert — an unchecked shift is a different program"; reason
restore "$MT_FIX"
expect PASS "P3 reverted"

echo
echo "== P4: THE ASSERT BINDS A RESULT =="
subin "$MT_SPEC" SRC_IR_MT_B0 "(ir_nd (IRInst.assert ir_d4))" "(ir_nd1 (IRInst.assert ir_d4) ir_d7)"
expect FAIL "P4 mutated: Assert is VALUE-LESS — the machine advances past it without binding. A module that binds a result there is a different program, and only the program-order lane's RESULT LIST can see it"; reason
subin "$MT_SPEC" SRC_IR_MT_B0 "(ir_nd1 (IRInst.assert ir_d4) ir_d7)" "(ir_nd (IRInst.assert ir_d4))"
expect PASS "P4 reverted"

# ────────────────────── THE ASSERT'S CONDITION, NEGATED ────────────────────

echo
echo "== P5: THE CONDITION NEGATED — ult becomes uge =="
subin "$MT_SPEC" SRC_IR_MT_B0 "IRInst.icmp IRICmpOp.ult ir_br_tu32 ir_d2 ir_d3" "IRInst.icmp IRICmpOp.uge ir_br_tu32 ir_d2 ir_d3"
expect FAIL "P5 mutated: the proved module asserts \`amount >= 64\` — the exact NEGATION of the range check, so the shipped body's passing arm becomes the panicking one"; reason
subin "$MT_SPEC" SRC_IR_MT_B0 "IRInst.icmp IRICmpOp.uge ir_br_tu32 ir_d2 ir_d3" "IRInst.icmp IRICmpOp.ult ir_br_tu32 ir_d2 ir_d3"
expect PASS "P5 reverted"

echo
echo "== P6: THE CONDITION'S OPERAND ORDER — \`64 < amount\` =="
subin "$MT_SPEC" SRC_IR_MT_B0 "IRInst.icmp IRICmpOp.ult ir_br_tu32 ir_d2 ir_d3" "IRInst.icmp IRICmpOp.ult ir_br_tu32 ir_d3 ir_d2"
expect FAIL "P6 mutated: the operands are exchanged, which is the negation again and changes no type"; reason
subin "$MT_SPEC" SRC_IR_MT_B0 "IRInst.icmp IRICmpOp.ult ir_br_tu32 ir_d3 ir_d2" "IRInst.icmp IRICmpOp.ult ir_br_tu32 ir_d2 ir_d3"
expect PASS "P6 reverted"

echo
echo "== P7: THE CONDITION'S WIDTH — u32 becomes u64 =="
subin "$MT_SPEC" SRC_IR_MT_B0 "IRInst.icmp IRICmpOp.ult ir_br_tu32 ir_d2 ir_d3" "IRInst.icmp IRICmpOp.ult ir_vc_tu64 ir_d2 ir_d3"
expect FAIL "P7 mutated: ir_int_cmp canonicalizes BOTH operands at the declared width, so the same operands decide a different predicate (ir_mt_icmp_width_is_semantic executes exactly that at width 8)"; reason
subin "$MT_SPEC" SRC_IR_MT_B0 "IRInst.icmp IRICmpOp.ult ir_vc_tu64 ir_d2 ir_d3" "IRInst.icmp IRICmpOp.ult ir_br_tu32 ir_d2 ir_d3"
expect PASS "P7 reverted"

# ───────────── WHERE THE ASSERT GOES WHEN IT FAILS (no target in IR) ────────

echo
echo "== P8: THE FAILURE TARGET REDIRECTED — a different fault =="
subin "$MT_SPEC" SRC_IR_MT_DICHOTOMY "(IRConfig.halted (IROutcome.ub IRFault.assert_failed)) (ir_advance s) b) := Bool.rec" "(IRConfig.halted (IROutcome.ub IRFault.unreachable)) (ir_advance s) b) := Bool.rec"
expect FAIL "P8 mutated: a failing assert is claimed to reach \`unreachable\` rather than \`assert_failed\`. trust-ir gives the instruction NO target, so this is the only place the failing edge can be pinned"; reason
subin "$MT_SPEC" SRC_IR_MT_DICHOTOMY "(IRConfig.halted (IROutcome.ub IRFault.unreachable)) (ir_advance s) b) := Bool.rec" "(IRConfig.halted (IROutcome.ub IRFault.assert_failed)) (ir_advance s) b) := Bool.rec"
expect PASS "P8 reverted"

echo
echo "== P9: THE FAILING ARM CLAIMED TO ADVANCE =="
subin "$MT_SPEC" SRC_IR_MT_DICHOTOMY "(IRConfig.halted (IROutcome.ub IRFault.assert_failed)) (ir_advance s) b) := Bool.rec" "(ir_advance s) (ir_advance s) b) := Bool.rec"
expect FAIL "P9 mutated: BOTH arms advance — the panic is claimed away entirely, which is the mutation a one-sided theorem could not have caught"; reason
subin "$MT_SPEC" SRC_IR_MT_DICHOTOMY "(ir_advance s) (ir_advance s) b) := Bool.rec" "(IRConfig.halted (IROutcome.ub IRFault.assert_failed)) (ir_advance s) b) := Bool.rec"
expect PASS "P9 reverted"

echo
echo "== P10: THE EXECUTED COUNTERFACTUAL NO LONGER PANICS =="
subin "$MT_SPEC" SRC_IR_MT_OOB_TRAPS "def ir_mt_oob_traps (mem : IRList IRMemSlot) (na : Nat) : Eq IROutcome (ir_run ir_d9 ir_mt_oob_module" "def ir_mt_oob_traps (mem : IRList IRMemSlot) (na : Nat) : Eq IROutcome (ir_run ir_d9 ir_mt_module"
expect FAIL "P10 mutated: the counterfactual is pointed at the SHIPPED module, so the recorded panic would be a claim about a body that returns a value"; reason
subin "$MT_SPEC" SRC_IR_MT_OOB_TRAPS "def ir_mt_oob_traps (mem : IRList IRMemSlot) (na : Nat) : Eq IROutcome (ir_run ir_d9 ir_mt_module" "def ir_mt_oob_traps (mem : IRList IRMemSlot) (na : Nat) : Eq IROutcome (ir_run ir_d9 ir_mt_oob_module"
expect PASS "P10 reverted"

echo
echo "== P11: THE COUNTERFACTUAL IS THE SHIPPED BODY =="
subin "$MT_SPEC" SRC_IR_MT_OOB_B0 "def ir_mt_oob_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (ir_mt_bd9 (ir_nd1 (IRInst.const_ ir_vc_tu64 (IRConst.int_ 1)) ir_d0) (ir_nd1 (IRInst.const_ ir_mt_ti32 (IRConst.int_ 64)) ir_d1)" "def ir_mt_oob_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (ir_mt_bd9 (ir_nd1 (IRInst.const_ ir_vc_tu64 (IRConst.int_ 1)) ir_d0) (ir_nd1 (IRInst.const_ ir_mt_ti32 (IRConst.int_ 63)) ir_d1)"
expect FAIL "P11 mutated: the OOB counterfactual shifts by 63 too, so it is the shipped body under another name and the boundary is pinned from one side only"; reason
subin "$MT_SPEC" SRC_IR_MT_OOB_B0 "def ir_mt_oob_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (ir_mt_bd9 (ir_nd1 (IRInst.const_ ir_vc_tu64 (IRConst.int_ 1)) ir_d0) (ir_nd1 (IRInst.const_ ir_mt_ti32 (IRConst.int_ 63)) ir_d1)" "def ir_mt_oob_b0 : IRBlock := IRBlock.mk ir_d0 ir_nl0 (ir_mt_bd9 (ir_nd1 (IRInst.const_ ir_vc_tu64 (IRConst.int_ 1)) ir_d0) (ir_nd1 (IRInst.const_ ir_mt_ti32 (IRConst.int_ 64)) ir_d1)"
expect PASS "P11 reverted"

echo
echo "== P12: THE TERMINALITY OF THE FAILING ARM, at one fuel instead of every =="
subin "$MT_SPEC" SRC_IR_MT_OOB_ANY_FUEL "def ir_mt_oob_never_returns_at_any_fuel (mem : IRList IRMemSlot) (na : Nat) (g : Nat)" "def ir_mt_oob_never_returns_at_any_fuel (mem : IRList IRMemSlot) (na : Nat) (h : Nat)"
expect FAIL "P12 mutated: the fuel is no longer the quantified \`g\`, so \`nothing after the assert runs\` would be a statement at one fuel"; reason
subin "$MT_SPEC" SRC_IR_MT_OOB_ANY_FUEL "def ir_mt_oob_never_returns_at_any_fuel (mem : IRList IRMemSlot) (na : Nat) (h : Nat)" "def ir_mt_oob_never_returns_at_any_fuel (mem : IRList IRMemSlot) (na : Nat) (g : Nat)"
expect PASS "P12 reverted"

# ─────────────── THE THREE CONSTANTS, WHICH USED TO COLLAPSE ───────────────

echo
echo "== P13: THE FIRST CONSTANT — the shifted value =="
subin "$MT_SPEC" SRC_IR_MT_B0 "(ir_nd1 (IRInst.const_ ir_vc_tu64 (IRConst.int_ 1)) ir_d0) (ir_nd1 (IRInst.const_ ir_mt_ti32 (IRConst.int_ 63)) ir_d1)" "(ir_nd1 (IRInst.const_ ir_vc_tu64 (IRConst.int_ 2)) ir_d0) (ir_nd1 (IRInst.const_ ir_mt_ti32 (IRConst.int_ 63)) ir_d1)"
expect FAIL "P13 mutated: the body shifts 2 rather than 1 — a different constant, and the one a block-keyed lane WOULD have caught"; reason
subin "$MT_SPEC" SRC_IR_MT_B0 "(ir_nd1 (IRInst.const_ ir_vc_tu64 (IRConst.int_ 2)) ir_d0) (ir_nd1 (IRInst.const_ ir_mt_ti32 (IRConst.int_ 63)) ir_d1)" "(ir_nd1 (IRInst.const_ ir_vc_tu64 (IRConst.int_ 1)) ir_d0) (ir_nd1 (IRInst.const_ ir_mt_ti32 (IRConst.int_ 63)) ir_d1)"
expect PASS "P13 reverted"

echo
echo "== P14: THE SECOND CONSTANT — the shift amount. INVISIBLE before this chain =="
subin "$MT_SPEC" SRC_IR_MT_B0 "(ir_nd1 (IRInst.const_ ir_mt_ti32 (IRConst.int_ 63)) ir_d1)" "(ir_nd1 (IRInst.const_ ir_mt_ti32 (IRConst.int_ 62)) ir_d1)"
expect FAIL "P14 mutated: the tag bit moves from 63 to 62. The pre-2026-08-16 int_consts lane was keyed by BLOCK and held only the FIRST constant of bb0, so this was compared by nothing"; reason
subin "$MT_SPEC" SRC_IR_MT_B0 "(ir_nd1 (IRInst.const_ ir_mt_ti32 (IRConst.int_ 62)) ir_d1)" "(ir_nd1 (IRInst.const_ ir_mt_ti32 (IRConst.int_ 63)) ir_d1)"
expect PASS "P14 reverted"

echo
echo "== P15: THE THIRD CONSTANT — the width bound. ALSO invisible before =="
subin "$MT_SPEC" SRC_IR_MT_B0 "(ir_nd1 (IRInst.const_ ir_br_tu32 (IRConst.int_ 64)) ir_d3)" "(ir_nd1 (IRInst.const_ ir_br_tu32 (IRConst.int_ 99)) ir_d3)"
expect FAIL "P15 mutated: the range check compares against 99 rather than the register width"; reason
subin "$MT_SPEC" SRC_IR_MT_B0 "(ir_nd1 (IRInst.const_ ir_br_tu32 (IRConst.int_ 99)) ir_d3)" "(ir_nd1 (IRInst.const_ ir_br_tu32 (IRConst.int_ 64)) ir_d3)"
expect PASS "P15 reverted"

echo
echo "== P16: A CONSTANT'S TYPE — i32 becomes u32, so the sext stops sign-extending =="
subin "$MT_SPEC" SRC_IR_MT_B0 "(ir_nd1 (IRInst.const_ ir_mt_ti32 (IRConst.int_ 63)) ir_d1)" "(ir_nd1 (IRInst.const_ ir_br_tu32 (IRConst.int_ 63)) ir_d1)"
expect FAIL "P16 mutated: the shift amount is materialized UNSIGNED. Same value, same id, different type — and the const_tys lane is the only one that reads it"; reason
subin "$MT_SPEC" SRC_IR_MT_B0 "(ir_nd1 (IRInst.const_ ir_br_tu32 (IRConst.int_ 63)) ir_d1)" "(ir_nd1 (IRInst.const_ ir_mt_ti32 (IRConst.int_ 63)) ir_d1)"
expect PASS "P16 reverted"

# ───────────────────────── THE TWO CASTS OF ONE OPERAND ────────────────────

echo
echo "== P17: THE OPCODES SWAPPED — bitcast becomes sext =="
subin "$MT_SPEC" SRC_IR_MT_B0 "IRInst.cast IRCastOp.bitcast ir_mt_ti32 ir_br_tu32 ir_d1" "IRInst.cast IRCastOp.sext ir_mt_ti32 ir_br_tu32 ir_d1"
expect FAIL "P17 mutated: the range check would see the SIGN-EXTENDED amount. At the i32 sign bit the two disagree — 2^31 versus 2^64 - 2^31 — which is the executed pair the chain registers"; reason
subin "$MT_SPEC" SRC_IR_MT_B0 "IRInst.cast IRCastOp.sext ir_mt_ti32 ir_br_tu32 ir_d1" "IRInst.cast IRCastOp.bitcast ir_mt_ti32 ir_br_tu32 ir_d1"
expect PASS "P17 reverted"

echo
echo "== P18: THE BITCAST'S DESTINATION WIDTH =="
subin "$MT_SPEC" SRC_IR_MT_B0 "IRInst.cast IRCastOp.bitcast ir_mt_ti32 ir_br_tu32 ir_d1" "IRInst.cast IRCastOp.bitcast ir_mt_ti32 ir_vc_tu64 ir_d1"
expect FAIL "P18 mutated: a bitcast between DIFFERENT widths, which ir_bitcast_eval refuses — the narrowing the tenth chain's build item deliberately kept"; reason
subin "$MT_SPEC" SRC_IR_MT_B0 "IRInst.cast IRCastOp.bitcast ir_mt_ti32 ir_vc_tu64 ir_d1" "IRInst.cast IRCastOp.bitcast ir_mt_ti32 ir_br_tu32 ir_d1"
expect PASS "P18 reverted"

echo
echo "== P19: THE SEXT'S OPERAND — %1 becomes %2 =="
subin "$MT_SPEC" SRC_IR_MT_B0 "IRInst.cast IRCastOp.sext ir_mt_ti32 ir_vc_tu64 ir_d1" "IRInst.cast IRCastOp.sext ir_mt_ti32 ir_vc_tu64 ir_d2"
expect FAIL "P19 mutated: the shift amount comes from the BITCAST rather than from the constant, which changes no type at all"; reason
subin "$MT_SPEC" SRC_IR_MT_B0 "IRInst.cast IRCastOp.sext ir_mt_ti32 ir_vc_tu64 ir_d2" "IRInst.cast IRCastOp.sext ir_mt_ti32 ir_vc_tu64 ir_d1"
expect PASS "P19 reverted"

echo
echo "== P20: THE SHIFT'S OPERAND ORDER =="
subin "$MT_SPEC" SRC_IR_MT_B0 "IRInst.binop IRBinOp.shl ir_vc_tu64 ir_d0 ir_d5" "IRInst.binop IRBinOp.shl ir_vc_tu64 ir_d5 ir_d0"
expect FAIL "P20 mutated: \`63 << 1\` rather than \`1 << 63\` — a different number, and the operand lane is the only one that sees it"; reason
subin "$MT_SPEC" SRC_IR_MT_B0 "IRInst.binop IRBinOp.shl ir_vc_tu64 ir_d5 ir_d0" "IRInst.binop IRBinOp.shl ir_vc_tu64 ir_d0 ir_d5"
expect PASS "P20 reverted"

echo
echo "== P21: THE RETURNED VALUE — the shift result becomes the constant =="
subin "$MT_SPEC" SRC_IR_MT_B0 "IRInst.ret (ir_nl1 ir_d6)" "IRInst.ret (ir_nl1 ir_d0)"
expect FAIL "P21 mutated: the body returns 1 rather than 1 << 63"; reason
subin "$MT_SPEC" SRC_IR_MT_B0 "IRInst.ret (ir_nl1 ir_d0)" "IRInst.ret (ir_nl1 ir_d6)"
expect PASS "P21 reverted"

echo
echo "== P22: PROGRAM ORDER — the assert hoisted above the comparison =="
subin "$MT_SPEC" SRC_IR_MT_B0 "(ir_nd1 (IRInst.icmp IRICmpOp.ult ir_br_tu32 ir_d2 ir_d3) ir_d4) (ir_nd (IRInst.assert ir_d4))" "(ir_nd (IRInst.assert ir_d4)) (ir_nd1 (IRInst.icmp IRICmpOp.ult ir_br_tu32 ir_d2 ir_d3) ir_d4)"
expect FAIL "P22 mutated: the assert reads %4 before anything binds it. Every per-KIND lane is bit-identical; only the program-order lane sees the interleaving"; reason
subin "$MT_SPEC" SRC_IR_MT_B0 "(ir_nd (IRInst.assert ir_d4)) (ir_nd1 (IRInst.icmp IRICmpOp.ult ir_br_tu32 ir_d2 ir_d3) ir_d4)" "(ir_nd1 (IRInst.icmp IRICmpOp.ult ir_br_tu32 ir_d2 ir_d3) ir_d4) (ir_nd (IRInst.assert ir_d4))"
expect PASS "P22 reverted"

echo
echo "== P23: THE FUNCTION SIGNATURE — a parameter appears =="
subin "$MT_SPEC" SRC_IR_MT_FUNC "IRFunc.mk ir_d0 ir_nl0 ir_d0 (ir_blk ir_mt_b0 ir_blk0)" "IRFunc.mk ir_d0 (ir_nl1 ir_d0) ir_d0 (ir_blk ir_mt_b0 ir_blk0)"
expect FAIL "P23 mutated: a const initializer takes NO arguments; a module that declares one reads its input from a binding the caller never makes"; reason
subin "$MT_SPEC" SRC_IR_MT_FUNC "IRFunc.mk ir_d0 (ir_nl1 ir_d0) ir_d0 (ir_blk ir_mt_b0 ir_blk0)" "IRFunc.mk ir_d0 ir_nl0 ir_d0 (ir_blk ir_mt_b0 ir_blk0)"
expect PASS "P23 reverted"

# ───────────────────────── FAIL-CLOSED ON MISSING INPUT ────────────────────

echo
echo "== P24: THE FIXTURE, DELETED =="
mv "$MT_FIX" "$MT_FIX.bak"
expect FAIL "P24: a missing fixture must fail CLOSED, not pass vacuously"; reason
mv "$MT_FIX.bak" "$MT_FIX"
expect PASS "P24 reverted"

echo
echo "== P25: THE FIXTURE, EMPTIED =="
cp "$MT_FIX" "$MT_FIX.bak"; : > "$MT_FIX"
expect FAIL "P25: an EMPTY fixture parses to an empty Cfg, which is exactly the silent-agreement mode the coverage denominator exists to refuse"; reason
mv "$MT_FIX.bak" "$MT_FIX"
expect PASS "P25 reverted"

echo
echo "== P26: THE EVIDENCE JSON, DELETED =="
mv "$MT_JSON" "$MT_JSON.bak"
expect FAIL "P26: missing A0/A6 evidence must fail CLOSED"; reason
mv "$MT_JSON.bak" "$MT_JSON"
expect PASS "P26 reverted"

echo
echo "== P27: THE EVIDENCE JSON, EMPTIED =="
cp "$MT_JSON" "$MT_JSON.bak"; : > "$MT_JSON"
expect FAIL "P27: an empty evidence file is not valid JSON and must fail CLOSED"; reason
mv "$MT_JSON.bak" "$MT_JSON"
expect PASS "P27 reverted"

echo
echo "== P28: THE SPEC MODULE, EMPTIED =="
cp "$MT_SPEC" "$MT_SPEC.bak"; : > "$MT_SPEC"
expect FAIL "P28: with no registered module the Clean side is empty — two empty Cfgs compare equal, so this MUST be caught by the coverage denominator rather than by the equality"; reason
mv "$MT_SPEC.bak" "$MT_SPEC"
expect PASS "P28 reverted"

# ───────────────────────────── THE MEASURED ROW ────────────────────────────

echo
echo "== P29: markers_detail ZEROED — already zero, so it is INVERTED =="
sub "$MT_JSON" '"markers_detail": "0 marker line(s) identical"' '"markers_detail": "2 marker line(s) identical"'
expect FAIL "P29 mutated: this chain's markers_exact IS vacuous and the gate says so. Claiming two real marker lines would make it look like the ninth chain's, which it is not"; reason
sub "$MT_JSON" '"markers_detail": "2 marker line(s) identical"' '"markers_detail": "0 marker line(s) identical"'
expect PASS "P29 reverted"

echo
echo "== P30: THE VACUITY FLAG =="
sub "$MT_JSON" '"markers_exact_is_vacuous": true' '"markers_exact_is_vacuous": false'
expect FAIL "P30 mutated: the record must SAY the marker comparison is vacuous, not leave a reader to parse the detail string"; reason
sub "$MT_JSON" '"markers_exact_is_vacuous": false' '"markers_exact_is_vacuous": true'
expect PASS "P30 reverted"

echo
echo "== P31: THE SEAM =="
sub "$MT_JSON" '"seam": "ctfe"' '"seam": "codegen"'
expect FAIL "P31 mutated: the seam is what link 2b MEANS. A CTFE flip binds the VALUE the const-eval interpreter produced; a codegen flip binds the instruction stream. They are not interchangeable"; reason
sub "$MT_JSON" '"seam": "codegen"' '"seam": "ctfe"'
expect PASS "P31 reverted"

echo
echo "== P32: THE VERIFIED ASSERT COUNT =="
sub "$MT_JSON" '"asserts": 1' '"asserts": 0'
expect FAIL "P32 mutated: asserts=1 is the ONE axis on which this chain rests on more producer-side checking than the codegen chains — verify_assert_parity is vacuous at 0 on all 178 of them"; reason
sub "$MT_JSON" '"asserts": 0' '"asserts": 1'
expect PASS "P32 reverted"

echo
echo "== P33: THE LINEAGE DIGEST =="
snap "$MT_JSON"
python3 - "$MT_JSON" <<'PYX'
import json, sys
p = sys.argv[1]
d = json.load(open(p))
d["flip_event"]["lineage"] = d["flip_event"]["lineage"].replace("501b50e5", "501b50e6")
json.dump(d, open(p, "w"), indent=4)
PYX
expect FAIL "P33 mutated: the flip event's lineage no longer equals the coverage row's, so the artifact inspected is not the artifact compiled"; reason
restore "$MT_JSON"
expect PASS "P33 reverted"

echo
echo "== P34: THE PANIC-ARM POPULATION — the codegen count =="
sub "$MT_JSON" '"codegen_flips_carrying_an_assert": 0' '"codegen_flips_carrying_an_assert": 21'
expect FAIL "P34 mutated: if codegen flips carried asserts, this chain would not be the first over a panic arm and \`panic arms 0\` would never have needed the word CODEGEN"; reason
sub "$MT_JSON" '"codegen_flips_carrying_an_assert": 21' '"codegen_flips_carrying_an_assert": 0'
expect PASS "P34 reverted"

echo
echo "== P35: THE PANIC-ARM POPULATION — the CTFE count =="
sub "$MT_JSON" '"ctfe_flips_carrying_an_assert": 21' '"ctfe_flips_carrying_an_assert": 32'
expect FAIL "P35 mutated: 21 of 32, measured — not all of them"; reason
sub "$MT_JSON" '"ctfe_flips_carrying_an_assert": 32' '"ctfe_flips_carrying_an_assert": 21'
expect PASS "P35 reverted"

echo
echo "== P36: LINK 2b IS WEAKER, and the record must say so =="
sub "$MT_JSON" '"is_weaker_than_the_codegen_form": true' '"is_weaker_than_the_codegen_form": false'
expect FAIL "P36 mutated: claiming parity with the codegen form is the one thing this lane was told not to do"; reason
sub "$MT_JSON" '"is_weaker_than_the_codegen_form": false' '"is_weaker_than_the_codegen_form": true'
expect PASS "P36 reverted"

echo
echo "== P37: WHAT LINK 2b DOES NOT BIND =="
sub "$MT_JSON" '"what_it_does_NOT_bind": "no machine code' '"what_it_does_NOT_bind": "nothing worth'
expect FAIL "P37 mutated: the weakening must be stated as what is NOT bound, first and plainly"; reason
sub "$MT_JSON" '"what_it_does_NOT_bind": "nothing worth' '"what_it_does_NOT_bind": "no machine code'
expect PASS "P37 reverted"

echo
echo "== P38: THE MARKER GATE DOES NOT DIFFER BY SEAM =="
sub "$MT_JSON" '"same_markers_gate": "flip_registry.rs:641' '"same_markers_gate": "the CTFE seam skips it, which is why'
expect FAIL "P38 mutated: the panic-arm asymmetry is a POPULATION difference, not a gate difference — record_green is the sole writer for both seams and consults markers_exact identically"; reason
sub "$MT_JSON" '"same_markers_gate": "the CTFE seam skips it, which is why' '"same_markers_gate": "flip_registry.rs:641'
expect PASS "P38 reverted"

echo
echo "== P39: WAS THE ASSERT A BUILD ITEM? =="
sub "$MT_JSON" '"was_the_assert_a_build_item": "NO"' '"was_the_assert_a_build_item": "YES"'
expect FAIL "P39 mutated: ir_assert_exec was already exact. Claiming the assert as this lane's build item would misattribute the work and hide where it actually was"; reason
sub "$MT_JSON" '"was_the_assert_a_build_item": "YES"' '"was_the_assert_a_build_item": "NO"'
expect PASS "P39 reverted"

echo
echo "== P40: THE SEMANTICS BUILD ITEM =="
sub "$MT_JSON" '"what": "IRCastOp.bitcast, which was a blanket ir_width_fault"' '"what": "nothing"'
expect FAIL "P40 mutated: the bitcast narrowing is the semantics change this lane made and it must stay named"; reason
sub "$MT_JSON" '"what": "nothing"' '"what": "IRCastOp.bitcast, which was a blanket ir_width_fault"'
expect PASS "P40 reverted"

echo
echo "== P41: WHAT THE NARROWED REFUSAL STILL REFUSES =="
snap "$MT_JSON"
python3 - "$MT_JSON" <<'PY'
import json, sys
p = sys.argv[1]
d = json.load(open(p))
d["build_items"]["semantics_build_item"]["what_stays_refused"] = ["only one thing"]
json.dump(d, open(p, "w"), indent=4)
PY
expect FAIL "P41 mutated: narrowing a refusal must enumerate what is STILL refused, or it is a relaxation wearing a narrowing's clothes"; reason
restore "$MT_JSON"
expect PASS "P41 reverted"

echo
echo "== P42: THE CORRECTION THIS LANE OWES THE NINTH CHAIN =="
sub "$MT_JSON" '"is_false_at_HEAD": true' '"is_false_at_HEAD": false'
expect FAIL "P42 mutated: the ninth chain recorded that no clean-kernel body flips a bitcast. That is FALSE at the CTFE seam and it is the same codegen-only reading error the panic-arm claim had"; reason
sub "$MT_JSON" '"is_false_at_HEAD": false' '"is_false_at_HEAD": true'
expect PASS "P42 reverted"

echo
echo "== P43: THE usize REFUSAL, which is why the other nine are unchained =="
sub "$MT_JSON" '"refused_because": "every operand is `usize`' '"refused_because": "they were less interesting'
expect FAIL "P43 mutated: the nine no_overflow bodies are refused by a GATE — the ?usize rule — not by preference, and the distinction is the whole reason this body was the pick"; reason
sub "$MT_JSON" '"refused_because": "they were less interesting' '"refused_because": "every operand is `usize`'
expect PASS "P43 reverted"

echo
echo "== P44: THE NEGATIVE CONTROL, for the CTFE lane specifically =="
sub "$MT_JSON" '"ctfe_flip_events_crate_wide": 0' '"ctfe_flip_events_crate_wide": 32'
expect FAIL "P44 mutated: -Ztrust-ir-flip=no must kill the CTFE events too, or the event is not evidence that the flip lane produced them"; reason
sub "$MT_JSON" '"ctfe_flip_events_crate_wide": 32' '"ctfe_flip_events_crate_wide": 0'
expect PASS "P44 reverted"

echo
echo "== P45: THE COMPILER IDENTIFICATION =="
sub "$MT_JSON" '"compiler_identified_by_behaviour_not_stamp"' '"compiler_identified_by_stamp"'
expect FAIL "P45 mutated: selftest returns UNPROVEN on identical class sets, so identification is BY OUTPUT DIGEST and the record must say which"; reason
sub "$MT_JSON" '"compiler_identified_by_stamp"' '"compiler_identified_by_behaviour_not_stamp"'
expect PASS "P45 reverted"

echo
echo "== P46: THE THREE UNIQUE SHIFT AMOUNTS =="
snap "$MT_JSON"
python3 - "$MT_JSON" <<'PY'
import json, sys
p = sys.argv[1]
d = json.load(open(p))
d["candidate_selection"]["the_twenty_one_by_shape"]["shift_in_range"]["unique_shift_amounts"] = [63]
json.dump(d, open(p, "w"), indent=4)
PY
expect FAIL "P46 mutated: three of the twelve are unique by shift amount, and META_TAG being one of three rather than the only one is what makes the choice a CHOICE"; reason
restore "$MT_JSON"
expect PASS "P46 reverted"

echo
echo "== P47: THE INSTRUCTION COUNT =="
sub "$MT_JSON" '"instr_count": 9' '"instr_count": 8'
expect FAIL "P47 mutated: nine nodes, the longest block any chain has transcribed"; reason
sub "$MT_JSON" '"instr_count": 8' '"instr_count": 9'
expect PASS "P47 reverted"

echo
echo "== P48: THE LANE MATRIX — the asserts cell, emptied on the ARTIFACT =="
# `lane_matrix.rs` is Rust compiled INTO the binary, so mutating its source at
# runtime proves nothing. The matrix reads the FIXTURES at runtime, and that is
# where the mutation belongs: strip the assert from the artifact and this
# chain's measured non-empty lane set loses `asserts`, which must disagree with
# the pinned row.
snap "$MT_FIX"
python3 - "$MT_FIX" <<'PYX'
import sys
p = sys.argv[1]
s = open(p).read()
assert s.count("    assert %4") == 1
open(p, "w").write(s.replace("    assert %4  ; #proof: shift_in_range  ; #loc: 435 157 30\n", ""))
PYX
"$BIN" the_lane_matrix_is_pinned_for_every_chain --test-threads=1 >"$OUT" 2>&1
lrc=$?
if [[ $lrc -ne 0 ]]; then
  echo "OK   [FAIL] P48 mutated: the measured lane set loses \`asserts\` and the pinned row says otherwise — the coverage denominator refuses a body that quietly stopped exercising a lane"
  pass=$((pass+1))
else
  echo "BAD  [want FAIL] P48: the lane matrix did not notice a lane going empty"
  fail=$((fail+1))
fi
restore "$MT_FIX"
expect PASS "P48 reverted"

echo
echo "== P49: PARSER TOTALITY — an UNROUTED mnemonic appears in a fixture =="
snap "$MT_FIX"
python3 - "$MT_FIX" <<'PYX'
import sys
p = sys.argv[1]
s = open(p).read()
assert s.count("    ret %6") == 1
open(p, "w").write(s.replace("    ret %6", "    %7 = ctlz u64 %0\n    ret %6", 1))
PYX
"$BIN" every_emitted_mnemonic_has_a_lane --test-threads=1 >"$OUT" 2>&1
lrc=$?
if [[ $lrc -ne 0 ]]; then
  echo "OK   [FAIL] P49 mutated: a mnemonic the parser routes NOWHERE falls through its catch-all arm and is compared by nothing on both sides — it must fail here, naming itself"
  pass=$((pass+1))
else
  echo "BAD  [want FAIL] P49: parser totality did not notice an unrouted mnemonic"
  fail=$((fail+1))
fi
restore "$MT_FIX"
expect PASS "P49 reverted"

echo
echo "PERTURBATIONS: $pass expected outcomes, $fail unexpected"
[[ $fail -eq 0 ]]
