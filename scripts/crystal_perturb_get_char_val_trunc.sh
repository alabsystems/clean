#!/usr/bin/env bash
# Perturbation proofs for the NINTH chain's gates:
#   env::native_reducers_beq_shortcircuit::get_char_val::{closure#0}
#
# The CFG / evidence gates read the spec source text and the fixtures from disk
# at RUNTIME (CARGO_MANIFEST_DIR), so the compiled test binary is driven
# directly: a perturbation is a file edit, the binary re-reads it, and no
# rebuild is involved. Each case mutates, asserts FAIL, reverts, asserts PASS.
#
# THE CASES THAT EXIST BECAUSE OF THIS CHAIN'S OWN LANES:
#   * P1-P2, P14        — the OPCODE. `zext` and `trunc` are the same shape and
#                         opposite operations, and before the `casts` lane a
#                         cast was in NO lane at all: this body parsed to an
#                         ENTIRELY EMPTY Cfg on both sides.
#   * P3, P15           — the SOURCE width, changed independently. It decides
#                         FAULT versus VALUE (`ir_nat_leb dw sw`), so it is not
#                         "the operand's type, already implied".
#   * P4-P5, P16        — the DESTINATION width, changed independently. It is
#                         the modulus (`ir_wrap dw x`).
#   * P17               — `usize` must stay UNRESOLVED and LOUD, not silently
#                         assumed to be 64.
#   * P6, P18           — the cast's OPERAND, which no type lane can see.
#   * P34-P39           — the recorded cast-semantics answer and the two zext
#                         siblings, so a later lane cannot claim the boundary
#                         away or re-derive the census without a gate noticing.
#
# The `sub` helper inherits the eighth chain's fix: an ambiguous revert anchor
# once let 32 of its cases run against a still-mutated tree, so a substitution
# that does not match exactly one declaration line is FATAL here.
set -uo pipefail
OUT="$(mktemp)"; trap 'rm -f "$OUT"' EXIT
REPO="$(cd "$(dirname "$0")/.." && pwd -P)"
BIN="${CRYSTAL_BIN:?set CRYSTAL_BIN to the compiled crystal_a1_lineage test binary}"

GC_SPEC="$REPO/crates/clean-verify/src/spec/core_spec/eval_ir_trunc.rs"
GC_FIX="$REPO/crates/clean-verify/tests/fixtures/get_char_val_trunc.trust-ir.txt"
GC_JSON="$REPO/crates/clean-verify/tests/fixtures/get_char_val_trunc.lineage.json"

pass=0; fail=0
FILTER=get_char_val_trunc
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
expect PASS "baseline: all get_char_val_trunc gates green"

# ── the GUARD ITSELF, proved rather than trusted ───────────────────────────
# The eighth chain's battery found a defect IN ITSELF: an ambiguous revert
# anchor matched two declaration lines, the substitution silently did nothing,
# and 32 cases ran against a still-mutated tree. The fix is the `assert` in
# `sub`. A fix nobody exercises is a fix nobody has. This runs `sub` in a
# SUBSHELL (so its `exit 9` does not take the script with it) against an anchor
# that genuinely matches three declaration lines — `IRCastOp.trunc ir_vc_tu64
# ir_br_tu32` appears in the module, in ir_gc_trunc_is_the_low_word and in
# ir_gc_non_integer_operand_is_a_type_error — and requires the abort.
echo
echo "== G0: the substitution guard ABORTS on an ambiguous anchor =="
( sub "$GC_SPEC" "IRCastOp.trunc ir_vc_tu64 ir_br_tu32" "IRCastOp.zext ir_vc_tu64 ir_br_tu32" ) >/dev/null 2>&1
grc=$?
if [[ $grc -eq 9 ]]; then
  echo "OK   [ABORT] G0: an anchor matching 3 declaration lines is FATAL, not a silent no-op"
  pass=$((pass+1))
else
  echo "BAD  [want abort rc=9, rc=$grc] G0: the substitution guard did not fire"
  fail=$((fail+1))
fi
expect PASS "G0: the tree is untouched after the refused substitution"

# ───────────────────────── the emitted instruction ─────────────────────────

echo
echo "== P1: THE OPCODE — trunc becomes zext =="
sub "$GC_SPEC" "IRInst.cast IRCastOp.trunc ir_vc_tu64 ir_br_tu32 ir_d1" "IRInst.cast IRCastOp.zext ir_vc_tu64 ir_br_tu32 ir_d1"
expect FAIL "P1 mutated: the proved module zero-extends where the artifact truncates — and at these widths zext is ir_width_fault, so a value becomes a fault"; reason
sub "$GC_SPEC" "IRInst.cast IRCastOp.zext ir_vc_tu64 ir_br_tu32 ir_d1" "IRInst.cast IRCastOp.trunc ir_vc_tu64 ir_br_tu32 ir_d1"
expect PASS "P1 reverted"

echo
echo "== P2: THE OPCODE — trunc becomes sext =="
sub "$GC_SPEC" "IRInst.cast IRCastOp.trunc ir_vc_tu64 ir_br_tu32 ir_d1" "IRInst.cast IRCastOp.sext ir_vc_tu64 ir_br_tu32 ir_d1"
expect FAIL "P2 mutated: sign extension, which is a third distinct operation on the same shape"; reason
sub "$GC_SPEC" "IRInst.cast IRCastOp.sext ir_vc_tu64 ir_br_tu32 ir_d1" "IRInst.cast IRCastOp.trunc ir_vc_tu64 ir_br_tu32 ir_d1"
expect PASS "P2 reverted"

echo
echo "== P3: THE SOURCE WIDTH, changed alone — u64 becomes u32 =="
sub "$GC_SPEC" "IRInst.cast IRCastOp.trunc ir_vc_tu64 ir_br_tu32 ir_d1" "IRInst.cast IRCastOp.trunc ir_br_tu32 ir_br_tu32 ir_d1"
expect FAIL "P3 mutated: the source is transcribed at u32 while the artifact reads a u64"; reason
sub "$GC_SPEC" "IRInst.cast IRCastOp.trunc ir_br_tu32 ir_br_tu32 ir_d1" "IRInst.cast IRCastOp.trunc ir_vc_tu64 ir_br_tu32 ir_d1"
expect PASS "P3 reverted"

echo
echo "== P4: THE DESTINATION WIDTH, changed alone — u32 becomes u8 =="
sub "$GC_SPEC" "IRInst.cast IRCastOp.trunc ir_vc_tu64 ir_br_tu32 ir_d1" "IRInst.cast IRCastOp.trunc ir_vc_tu64 ir_tU8 ir_d1"
expect FAIL "P4 mutated: the destination is u8, so the modulus is 2^8 and the body computes a different function of the same operand"; reason
sub "$GC_SPEC" "IRInst.cast IRCastOp.trunc ir_vc_tu64 ir_tU8 ir_d1" "IRInst.cast IRCastOp.trunc ir_vc_tu64 ir_br_tu32 ir_d1"
expect PASS "P4 reverted"

echo
echo "== P5: THE DESTINATION WIDTH — u32 becomes u64, i.e. a no-op cast =="
sub "$GC_SPEC" "IRInst.cast IRCastOp.trunc ir_vc_tu64 ir_br_tu32 ir_d1" "IRInst.cast IRCastOp.trunc ir_vc_tu64 ir_vc_tu64 ir_d1"
expect FAIL "P5 mutated: truncating u64 to u64 discards nothing, which is exactly the information-loss this chain is about"; reason
sub "$GC_SPEC" "IRInst.cast IRCastOp.trunc ir_vc_tu64 ir_vc_tu64 ir_d1" "IRInst.cast IRCastOp.trunc ir_vc_tu64 ir_br_tu32 ir_d1"
expect PASS "P5 reverted"

echo
echo "== P6: THE OPERAND — cast the closure environment instead of the argument =="
sub "$GC_SPEC" "ir_vc_tu64 ir_br_tu32 ir_d1) ir_d2" "ir_vc_tu64 ir_br_tu32 ir_d0) ir_d2"
expect FAIL "P6 mutated: the cast reads %0, the closure environment, instead of %1"; reason
sub "$GC_SPEC" "ir_vc_tu64 ir_br_tu32 ir_d0) ir_d2" "ir_vc_tu64 ir_br_tu32 ir_d1) ir_d2"
expect PASS "P6 reverted"

echo
echo "== P7: THE RESULT ID the cast binds =="
sub "$GC_SPEC" "ir_vc_tu64 ir_br_tu32 ir_d1) ir_d2" "ir_vc_tu64 ir_br_tu32 ir_d1) ir_d3"
expect FAIL "P7 mutated: the truncation is bound at %3 while the ret still reads %2"; reason
sub "$GC_SPEC" "ir_vc_tu64 ir_br_tu32 ir_d1) ir_d3" "ir_vc_tu64 ir_br_tu32 ir_d1) ir_d2"
expect PASS "P7 reverted"

echo
echo "== P8: THE RET LANE — return the ARGUMENT instead of the truncation =="
sub "$GC_SPEC" "(ir_nd (IRInst.ret (ir_nl1 ir_d2)))" "(ir_nd (IRInst.ret (ir_nl1 ir_d1)))"
expect FAIL "P8 mutated: the body returns %1, its u64 argument, instead of %2"; reason
sub "$GC_SPEC" "(ir_nd (IRInst.ret (ir_nl1 ir_d1)))" "(ir_nd (IRInst.ret (ir_nl1 ir_d2)))"
expect PASS "P8 reverted"

echo
echo "== P9: THE BLOCK ID =="
sub "$GC_SPEC" "IRBlock.mk ir_d0 ir_nl0" "IRBlock.mk ir_d1 ir_nl0"
expect FAIL "P9 mutated: the only block is bb1, and the function still enters at bb0"; reason
sub "$GC_SPEC" "IRBlock.mk ir_d1 ir_nl0" "IRBlock.mk ir_d0 ir_nl0"
expect PASS "P9 reverted"

echo
echo "== P10: THE PARAMETER LIST — the closure environment dropped =="
sub "$GC_SPEC" "IRFunc.mk ir_d0 (ir_nl2 ir_d0 ir_d1) ir_d0" "IRFunc.mk ir_d0 (ir_nl1 ir_d1) ir_d0"
expect FAIL "P10 mutated: one parameter where the artifact takes two"; reason
sub "$GC_SPEC" "IRFunc.mk ir_d0 (ir_nl1 ir_d1) ir_d0" "IRFunc.mk ir_d0 (ir_nl2 ir_d0 ir_d1) ir_d0"
expect PASS "P10 reverted"

echo
echo "== P11: THE ENTRY BLOCK the function starts at =="
sub "$GC_SPEC" "(ir_nl2 ir_d0 ir_d1) ir_d0 (ir_blk" "(ir_nl2 ir_d0 ir_d1) ir_d1 (ir_blk"
expect FAIL "P11 mutated: the function enters at bb1, which does not exist"; reason
sub "$GC_SPEC" "(ir_nl2 ir_d0 ir_d1) ir_d1 (ir_blk" "(ir_nl2 ir_d0 ir_d1) ir_d0 (ir_blk"
expect PASS "P11 reverted"

echo
echo "== P12: THE CAST DELETED from the proved module =="
sub "$GC_SPEC" "(ir_bd2 (ir_nd1 (IRInst.cast IRCastOp.trunc ir_vc_tu64 ir_br_tu32 ir_d1) ir_d2) (ir_nd (IRInst.ret (ir_nl1 ir_d2))))" "(ir_bd1 (ir_nd (IRInst.ret (ir_nl1 ir_d2))))"
expect FAIL "P12 mutated: the module is a bare return. Before the casts lane existed this compared EQUAL to the artifact on every lane"; reason
sub "$GC_SPEC" "(ir_bd1 (ir_nd (IRInst.ret (ir_nl1 ir_d2))))" "(ir_bd2 (ir_nd1 (IRInst.cast IRCastOp.trunc ir_vc_tu64 ir_br_tu32 ir_d1) ir_d2) (ir_nd (IRInst.ret (ir_nl1 ir_d2))))"
expect PASS "P12 reverted"

# ────────────────────────── the emitted FIXTURE ────────────────────────────

echo
echo "== P13: THE ARTIFACT SIDE — the cast deleted =="
sub "$GC_FIX" "    %2 = trunc u64 %1 to u32  ; #loc: 347 120 60" "    ; #loc: 347 120 60"
expect FAIL "P13 mutated: the emitted body has no cast"; reason
sub "$GC_FIX" "    ; #loc: 347 120 60" "    %2 = trunc u64 %1 to u32  ; #loc: 347 120 60"
expect PASS "P13 reverted"

echo
echo "== P14: THE ARTIFACT SIDE's opcode — trunc becomes zext =="
sub "$GC_FIX" "%2 = trunc u64 %1 to u32" "%2 = zext u64 %1 to u32"
expect FAIL "P14 mutated: the emitted instruction zero-extends"; reason
sub "$GC_FIX" "%2 = zext u64 %1 to u32" "%2 = trunc u64 %1 to u32"
expect PASS "P14 reverted"

echo
echo "== P15: THE ARTIFACT SIDE's SOURCE width, changed alone =="
sub "$GC_FIX" "trunc u64 %1 to u32" "trunc u16 %1 to u32"
expect FAIL "P15 mutated: the emitted source is u16, where the proved module reads a u64. At those widths the semantics is ir_width_fault rather than a value"; reason
sub "$GC_FIX" "trunc u16 %1 to u32" "trunc u64 %1 to u32"
expect PASS "P15 reverted"

echo
echo "== P16: THE ARTIFACT SIDE's DESTINATION width, changed alone =="
sub "$GC_FIX" "trunc u64 %1 to u32" "trunc u64 %1 to u16"
expect FAIL "P16 mutated: the emitted destination is u16, so the modulus is 2^16"; reason
sub "$GC_FIX" "trunc u64 %1 to u16" "trunc u64 %1 to u32"
expect PASS "P16 reverted"

echo
echo "== P17: THE ARTIFACT SIDE at usize — must be UNRESOLVED and LOUD =="
sub "$GC_FIX" "trunc u64 %1 to u32" "trunc u64 %1 to usize"
expect FAIL "P17 mutated: usize normalizes to the loud ?usize rather than to an assumed 64, and the lane refuses an unresolved type on either side"; reason
sub "$GC_FIX" "trunc u64 %1 to usize" "trunc u64 %1 to u32"
expect PASS "P17 reverted"

echo
echo "== P18: THE ARTIFACT SIDE's operand =="
sub "$GC_FIX" "trunc u64 %1 to u32" "trunc u64 %0 to u32"
expect FAIL "P18 mutated: the emitted cast reads the closure environment"; reason
sub "$GC_FIX" "trunc u64 %0 to u32" "trunc u64 %1 to u32"
expect PASS "P18 reverted"

echo
echo "== P19: THE ARTIFACT SIDE returns its argument =="
sub "$GC_FIX" "ret %2" "ret %1"
expect FAIL "P19 mutated: the emitted body returns %1"; reason
sub "$GC_FIX" "ret %1" "ret %2"
expect PASS "P19 reverted"

echo
echo "== P20: THE ARTIFACT SIDE's parameter list =="
sub "$GC_FIX" "bb0(%0: (), %1: u64):" "bb0(%1: u64):"
expect FAIL "P20 mutated: the emitted signature loses the closure environment"; reason
sub "$GC_FIX" "bb0(%1: u64):" "bb0(%0: (), %1: u64):"
expect PASS "P20 reverted"

echo
echo "== P21: FIXTURE DELETED — the gate must fail CLOSED, not vacuously pass =="
mv "$GC_FIX" "$GC_FIX.bak"
expect FAIL "P21 mutated: emitted trust-ir fixture absent"; reason
mv "$GC_FIX.bak" "$GC_FIX"
expect PASS "P21 reverted"

echo
echo "== P22: FIXTURE EMPTIED =="
cp "$GC_FIX" "$GC_FIX.bak"; : > "$GC_FIX"
expect FAIL "P22 mutated: emitted fixture is zero bytes"; reason
mv "$GC_FIX.bak" "$GC_FIX"
expect PASS "P22 reverted"

echo
echo "== P23: EVIDENCE FILE DELETED — fail closed as well =="
mv "$GC_JSON" "$GC_JSON.bak"
expect FAIL "P23 mutated: the A0/A6 evidence is absent"; reason
mv "$GC_JSON.bak" "$GC_JSON"
expect PASS "P23 reverted"

echo
echo "== P24: EVIDENCE FILE EMPTIED =="
cp "$GC_JSON" "$GC_JSON.bak"; : > "$GC_JSON"
expect FAIL "P24 mutated: the A0/A6 evidence is zero bytes"; reason
mv "$GC_JSON.bak" "$GC_JSON"
expect PASS "P24 reverted"

# ──────────────────────────── the A0/A6 evidence ───────────────────────────

echo
echo "== P25: markers_detail ZEROED (the two real marker lines) =="
sub "$GC_JSON" '"markers_detail": "2 marker line(s) identical"' '"markers_detail": "0 marker line(s) identical"'
expect FAIL "P25 mutated: the 2-line marker sequence becomes empty, i.e. markers_exact goes vacuous"; reason
sub "$GC_JSON" '"markers_detail": "0 marker line(s) identical"' '"markers_detail": "2 marker line(s) identical"'
expect PASS "P25 reverted"

echo
echo "== P26: markers_exact itself =="
sub "$GC_JSON" '"markers_exact": true' '"markers_exact": false'
expect FAIL "P26 mutated: the -O marker gate did not hold"; reason
sub "$GC_JSON" '"markers_exact": false' '"markers_exact": true'
expect PASS "P26 reverted"

echo
echo "== P27: the FLIP EVENT's lineage digest, by one nibble =="
# TWO leading spaces: the FLIP EVENT's lineage is nested one level deeper than
# the coverage row's, so this anchor reaches the event and not the artifact.
sub "$GC_JSON" '  "lineage": "sha256:607c1d96f6bbe7856a4f2221a9eb577cdc4b58259b8c04586871cb590eb84589"' '  "lineage": "sha256:607c1d96f6bbe7856a4f2221a9eb577cdc4b58259b8c04586871cb590eb8458a"'
expect FAIL "P27 mutated: the artifact inspected is not the artifact compiled"; reason
sub "$GC_JSON" '  "lineage": "sha256:607c1d96f6bbe7856a4f2221a9eb577cdc4b58259b8c04586871cb590eb8458a"' '  "lineage": "sha256:607c1d96f6bbe7856a4f2221a9eb577cdc4b58259b8c04586871cb590eb84589"'
expect PASS "P27 reverted"

echo
echo "== P28: the flip event FIRED =="
sub "$GC_JSON" '"fired": true' '"fired": false'
expect FAIL "P28 mutated: no codegen flip, so the derived IR is a side model"; reason
sub "$GC_JSON" '"fired": false' '"fired": true'
expect PASS "P28 reverted"

echo
echo "== P29: the flip SEAM =="
sub "$GC_JSON" '"seam": "codegen"' '"seam": "ctfe"'
expect FAIL "P29 mutated: a CTFE flip is not the shipped object code"; reason
sub "$GC_JSON" '"seam": "ctfe"' '"seam": "codegen"'
expect PASS "P29 reverted"

echo
echo "== P30: the NEGATIVE CONTROL =="
sub "$GC_JSON" '"flip_events_crate_wide": 0' '"flip_events_crate_wide": 1'
expect FAIL "P30 mutated: -Ztrust-ir-flip=no produced an event, so the flag proves nothing"; reason
sub "$GC_JSON" '"flip_events_crate_wide": 1' '"flip_events_crate_wide": 0'
expect PASS "P30 reverted"

echo
echo "== P31: the INTERPRETER differential's sample count =="
sub "$GC_JSON" '"samples": 5' '"samples": 0'
expect FAIL "P31 mutated: \`agreed\` on zero samples is a vacuous agreement"; reason
sub "$GC_JSON" '"samples": 0' '"samples": 5'
expect PASS "P31 reverted"

echo
echo "== P32: the CALL COUNT — bodyful reachable closure =="
sub "$GC_JSON" '  "resolved": 0,' '  "resolved": 1,'
expect FAIL "P32 mutated: a resolved call reopens the closure question"; reason
sub "$GC_JSON" '  "resolved": 1,' '  "resolved": 0,'
expect PASS "P32 reverted"

echo
echo "== P33: the LINEAGE DOMAIN version =="
sub "$GC_JSON" '"lineage_domain": "trust_thir_lower.body_lineage.v2"' '"lineage_domain": "trust_thir_lower.body_lineage.v3"'
expect FAIL "P33 mutated: a digest and its domain travel together or neither means anything"; reason
sub "$GC_JSON" '"lineage_domain": "trust_thir_lower.body_lineage.v3"' '"lineage_domain": "trust_thir_lower.body_lineage.v2"'
expect PASS "P33 reverted"

echo
echo "== P34: the REPRODUCTION claim =="
sub "$GC_JSON" '"coverage_json_byte_identical_across_all_three": true' '"coverage_json_byte_identical_across_all_three": false'
expect FAIL "P34 mutated: one observation is not a measurement"; reason
sub "$GC_JSON" '"coverage_json_byte_identical_across_all_three": false' '"coverage_json_byte_identical_across_all_three": true'
expect PASS "P34 reverted"

echo
echo "== P35: the PROVEN-NEVER-READ closure environment =="
sub "$GC_JSON" 'proven-never-read opaque param(s) as placeholders' 'opaque param(s) as placeholders'
expect FAIL "P35 mutated: without the producer's own never-read record, quantifying over the environment with no premise is an assumption"; reason
sub "$GC_JSON" 'opaque param(s) as placeholders' 'proven-never-read opaque param(s) as placeholders'
expect PASS "P35 reverted"

# ─────────────── the census, the siblings and the semantics answer ──────────

echo
echo "== P36: the RE-DERIVED OPERATOR CENSUS — the trunc count =="
sub "$GC_JSON" '"trunc": 1' '"trunc": 2'
expect FAIL "P36 mutated: a trunc is 1 of 177 and the census must reproduce the float lane's"; reason
sub "$GC_JSON" '"trunc": 2' '"trunc": 1'
expect PASS "P36 reverted"

echo
echo "== P37: the VACUITY figure this lane re-derived =="
sub "$GC_JSON" '"markers_exact_rows_that_are_NON_vacuous": 27' '"markers_exact_rows_that_are_NON_vacuous": 1084'
expect FAIL "P37 mutated: 1084 markers_exact rows read as 1084 checked bodies"; reason
sub "$GC_JSON" '"markers_exact_rows_that_are_NON_vacuous": 1084' '"markers_exact_rows_that_are_NON_vacuous": 27'
expect PASS "P37 reverted"

echo
echo "== P38: a ZEXT SIBLING's recorded lineage =="
sub "$GC_JSON" '"lineage": "sha256:8a8aa6ba1b9903461934d613a555b7155ca39eea75edeed80c2f6db79a475dec"' '"lineage": "sha256:8a8aa6ba1b9903461934d613a555b7155ca39eea75edeed80c2f6db79a475ded"'
expect FAIL "P38 mutated: NodeId::index's recorded digest is wrong, so the next lane would chain against a body that is not the one measured"; reason
sub "$GC_JSON" '"lineage": "sha256:8a8aa6ba1b9903461934d613a555b7155ca39eea75edeed80c2f6db79a475ded"' '"lineage": "sha256:8a8aa6ba1b9903461934d613a555b7155ca39eea75edeed80c2f6db79a475dec"'
expect PASS "P38 reverted"

echo
echo "== P39: a ZEXT SIBLING's recorded def_index =="
sub "$GC_JSON" '"def_index": 13453' '"def_index": 13454'
expect FAIL "P39 mutated: ExtensionIdx::index's recorded def_index is wrong"; reason
sub "$GC_JSON" '"def_index": 13454' '"def_index": 13453'
expect PASS "P39 reverted"

echo
echo "== P40: the SIBLINGS ARE THE SAME BODY TWICE =="
sub "$GC_JSON" '"they_are_the_same_body_twice": true' '"they_are_the_same_body_twice": false'
expect FAIL "P40 mutated: if the two zext bodies were genuinely different, the reason this chain chose the trunc would be one reason weaker"; reason
sub "$GC_JSON" '"they_are_the_same_body_twice": false' '"they_are_the_same_body_twice": true'
expect PASS "P40 reverted"

echo
echo "== P41: what a ZEXT chain still owes =="
sub "$GC_JSON" '"what_a_later_lane_still_owes": "the transcription, and a decision about `usize`.' '"what_a_later_lane_still_owes": "nothing.'
expect FAIL "P41 mutated: the usize decision is claimed away, so the next lane would assume a width"; reason
sub "$GC_JSON" '"what_a_later_lane_still_owes": "nothing.' '"what_a_later_lane_still_owes": "the transcription, and a decision about `usize`.'
expect PASS "P41 reverted"

echo
echo "== P42: THE CAST-SEMANTICS ANSWER =="
sub "$GC_JSON" '"answer": "EXPRESSIBLE, EXACTLY' '"answer": "PARTLY'
expect FAIL "P42 mutated: the answer is a measurement, not a mood — a truncation to a narrower integer is TOTAL"; reason
sub "$GC_JSON" '"answer": "PARTLY' '"answer": "EXPRESSIBLE, EXACTLY'
expect PASS "P42 reverted"

echo
echo "== P43: WHAT THE BUILD ITEM ACTUALLY WAS =="
sub "$GC_JSON" '"what_WAS_the_build_item": "the CFG GATE.' '"what_WAS_the_build_item": "the semantics.'
expect FAIL "P43 mutated: the build item was the GATE, and the reason (two empty CFGs compare equal) must stay stated"; reason
sub "$GC_JSON" '"what_WAS_the_build_item": "the semantics.' '"what_WAS_the_build_item": "the CFG GATE.'
expect PASS "P43 reverted"

echo
echo "== P44: THE SOURCE WIDTH's recorded reason =="
sub "$GC_JSON" 'so trunc u8 -> u32 is ir_width_fault where trunc u64 -> u32 is a value -- the source width decides FAULT versus VALUE' 'the source width is the operand type'
expect FAIL "P44 mutated: the half of the cast type lane with no analogue in binop_tys is claimed away"; reason
sub "$GC_JSON" 'the source width is the operand type' 'so trunc u8 -> u32 is ir_width_fault where trunc u64 -> u32 is a value -- the source width decides FAULT versus VALUE'
expect PASS "P44 reverted"

echo
echo "== P45: THE REFUSED PERIODICITY LAW's trust cost =="
sub "$GC_JSON" 'ACCELERATED CONSTANTS whose declared bodies the kernel never consults' 'a small helper'
expect FAIL "P45 mutated: the refusal must name what buying the law would cost in trust"; reason
sub "$GC_JSON" 'a small helper' 'ACCELERATED CONSTANTS whose declared bodies the kernel never consults'
expect PASS "P45 reverted"

echo
echo "== P46: THE ACCELERATED-CONSTANT COUNT =="
sub "$GC_JSON" '"accelerated_constants_added": 0' '"accelerated_constants_added": 1'
expect FAIL "P46 mutated: if this ever becomes non-zero the trust argument has changed"; reason
sub "$GC_JSON" '"accelerated_constants_added": 1' '"accelerated_constants_added": 0'
expect PASS "P46 reverted"

echo
echo "== P47: THE FLOAT LANE's hole, looked for on BOTH types =="
sub "$GC_JSON" 'the eighth chain found that `fdiv f32` and `fdiv f64` differed in NO lane the gate had' 'the widths were assumed to be fine'
expect FAIL "P47 mutated: the reason both cast types were checked before the lane was trusted is deleted"; reason
sub "$GC_JSON" 'the widths were assumed to be fine' 'the eighth chain found that `fdiv f32` and `fdiv f64` differed in NO lane the gate had'
expect PASS "P47 reverted"

echo
echo "PERTURBATIONS: $pass expected outcomes, $fail unexpected"
[[ $fail -eq 0 ]]
