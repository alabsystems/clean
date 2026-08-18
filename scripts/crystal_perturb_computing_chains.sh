#!/usr/bin/env bash
# Perturbation proofs for the two COMPUTING chains' gates:
#   flat::types::FlatFlags::contains   (binop + icmp, three field reads)
#   expr::bvar_in_range                (two condbrs, four icmps, two joins)
#
# The CFG / evidence gates read the spec source text and the fixtures from disk
# at RUNTIME (CARGO_MANIFEST_DIR), so the compiled test binary is driven
# directly: a perturbation is a file edit, the binary re-reads it, and no
# rebuild is involved. Each case mutates, asserts FAIL, reverts, asserts PASS.
#
# Two of the cases below exist because of a gap the earlier perturbation scripts
# could not have found: before this lane the CFG gate had no binop, icmp,
# extractfield or condbr lane at all, so swapping a conditional branch's targets
# or turning an AND into an OR changed NOTHING the gate looked at. P4 and P11
# are the direct evidence that those lanes are load-bearing.
set -uo pipefail
OUT="$(mktemp)"; trap 'rm -f "$OUT"' EXIT
REPO="$(cd "$(dirname "$0")/.." && pwd -P)"
BIN="${CRYSTAL_BIN:?set CRYSTAL_BIN to the compiled crystal_a1_lineage test binary}"

FC_SPEC="$REPO/crates/clean-verify/src/spec/core_spec/eval_ir_contains.rs"
FC_FIX="$REPO/crates/clean-verify/tests/fixtures/flat_flags_contains.trust-ir.txt"
FC_JSON="$REPO/crates/clean-verify/tests/fixtures/flat_flags_contains.lineage.json"
BR_SPEC="$REPO/crates/clean-verify/src/spec/core_spec/eval_ir_bvar_range.rs"
BR_FIX="$REPO/crates/clean-verify/tests/fixtures/bvar_in_range.trust-ir.txt"
BR_JSON="$REPO/crates/clean-verify/tests/fixtures/bvar_in_range.lineage.json"

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

# Substitute inside the DECLARATION lines only.
#
# The spec modules also carry unit tests that quote the same block sources
# verbatim, so a whole-file anchor is not unique. A silent no-substitution would
# make a MUTATED run look green - the exact false negative this script exists to
# rule out - so the helper restricts .rs edits to lines beginning `const SRC_`
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
} || exit 9

echo "== baseline =="
expect PASS "baseline: all crystal_a1_lineage gates green"

# ─────────────────────────── flat_flags_contains ───────────────────────────
FILTER=flat_flags_contains

echo
echo "== P1: the DUPLICATE field read =="
sub "$FC_SPEC" "(IRInst.extractfield ir_tU8 ir_d1 ir_d0) ir_d5)" "(IRInst.extractfield ir_tU8 ir_d0 ir_d0) ir_d5)"
expect FAIL "P1 mutated: the second read of other.0 reads self.0 instead"; reason
sub "$FC_SPEC" "(IRInst.extractfield ir_tU8 ir_d0 ir_d0) ir_d5)" "(IRInst.extractfield ir_tU8 ir_d1 ir_d0) ir_d5)"
expect PASS "P1 reverted"

echo
echo "== P2: the field INDEX =="
sub "$FC_SPEC" "(IRInst.extractfield ir_tU8 ir_d0 ir_d0) ir_d2)" "(IRInst.extractfield ir_tU8 ir_d0 ir_d1) ir_d2)"
expect FAIL "P2 mutated: self.0 becomes self.1"; reason
sub "$FC_SPEC" "(IRInst.extractfield ir_tU8 ir_d0 ir_d1) ir_d2)" "(IRInst.extractfield ir_tU8 ir_d0 ir_d0) ir_d2)"
expect PASS "P2 reverted"

echo
echo "== P3: the BINOP — and vs or =="
sub "$FC_SPEC" "IRInst.binop IRBinOp.and_ ir_tU8 ir_d2 ir_d3" "IRInst.binop IRBinOp.or_ ir_tU8 ir_d2 ir_d3"
expect FAIL "P3 mutated: the AND becomes an OR"; reason
sub "$FC_SPEC" "IRInst.binop IRBinOp.or_ ir_tU8 ir_d2 ir_d3" "IRInst.binop IRBinOp.and_ ir_tU8 ir_d2 ir_d3"
expect PASS "P3 reverted"

echo
echo "== P4: the ICMP operand — %5 (the duplicate read) vs %3 =="
sub "$FC_SPEC" "IRInst.icmp IRICmpOp.eq_ ir_tU8 ir_d4 ir_d5" "IRInst.icmp IRICmpOp.eq_ ir_tU8 ir_d4 ir_d3"
expect FAIL "P4 mutated: the comparison uses the FIRST read of other.0"; reason
sub "$FC_SPEC" "IRInst.icmp IRICmpOp.eq_ ir_tU8 ir_d4 ir_d3" "IRInst.icmp IRICmpOp.eq_ ir_tU8 ir_d4 ir_d5"
expect PASS "P4 reverted"

echo
echo "== P5: the flip-event lineage digest =="
sub "$FC_JSON" '  "lineage": "sha256:1afb2dc3d56c0feb14ebdfa487474aed27ece83dabb93ef9c24f465af7f0de0f",' '  "lineage": "sha256:1afb2dc3d56c0feb14ebdfa487474aed27ece83dabb93ef9c24f465af7f0de0b",'
expect FAIL "P5 mutated: the FLIP EVENT's lineage differs from the coverage row's by one nibble"; reason
sub "$FC_JSON" '  "lineage": "sha256:1afb2dc3d56c0feb14ebdfa487474aed27ece83dabb93ef9c24f465af7f0de0b",' '  "lineage": "sha256:1afb2dc3d56c0feb14ebdfa487474aed27ece83dabb93ef9c24f465af7f0de0f",'
expect PASS "P5 reverted"

echo
echo "== P6: the negative control =="
sub "$FC_JSON" '"flip_events_crate_wide": 0' '"flip_events_crate_wide": 1'
expect FAIL "P6 mutated: -Ztrust-ir-flip=no produced an event"; reason
sub "$FC_JSON" '"flip_events_crate_wide": 1' '"flip_events_crate_wide": 0'
expect PASS "P6 reverted"

echo
echo "== P7: markers_exact NON-VACUITY =="
sub "$FC_JSON" '"markers_detail": "8 marker line(s) identical"' '"markers_detail": "0 marker line(s) identical"'
expect FAIL "P7 mutated: the marker sequence is empty, so markers_exact is vacuous here too"; reason
sub "$FC_JSON" '"markers_detail": "0 marker line(s) identical"' '"markers_detail": "8 marker line(s) identical"'
expect PASS "P7 reverted"

echo
echo "== P8: FIXTURE DELETED — the gate must fail CLOSED, not vacuously pass =="
mv "$FC_FIX" "$FC_FIX.bak"
expect FAIL "P8 mutated: emitted trust-ir fixture absent"; reason
mv "$FC_FIX.bak" "$FC_FIX"
expect PASS "P8 reverted"

echo
echo "== P9: FIXTURE EMPTIED — a zero-byte fixture must not compare equal to an empty Clean CFG =="
cp "$FC_FIX" "$FC_FIX.bak"; : > "$FC_FIX"
expect FAIL "P9 mutated: emitted fixture is zero bytes"; reason
mv "$FC_FIX.bak" "$FC_FIX"
expect PASS "P9 reverted"

# ───────────────────────────── bvar_in_range ──────────────────────────────
FILTER=bvar_in_range

echo
echo "== P10: baseline for the second chain =="
expect PASS "P10 baseline: bvar_in_range gates green"

echo
echo "== P11: the OUTER condbr's targets, EXCHANGED =="
sub "$BR_SPEC" "IRInst.condbr ir_d6 ir_d1 ir_nl0 ir_d2 ir_nl0" "IRInst.condbr ir_d6 ir_d2 ir_nl0 ir_d1 ir_nl0"
expect FAIL "P11 mutated: then/else exchanged on the sentinel test"; reason
sub "$BR_SPEC" "IRInst.condbr ir_d6 ir_d2 ir_nl0 ir_d1 ir_nl0" "IRInst.condbr ir_d6 ir_d1 ir_nl0 ir_d2 ir_nl0"
expect PASS "P11 reverted"

echo
echo "== P12: the INNER condbr's targets, EXCHANGED (the short circuit inverted) =="
sub "$BR_SPEC" "IRInst.condbr ir_d8 ir_d4 ir_nl0 ir_d5 ir_nl0" "IRInst.condbr ir_d8 ir_d5 ir_nl0 ir_d4 ir_nl0"
expect FAIL "P12 mutated: the short circuit evaluates the upper bound when the lower FAILS"; reason
sub "$BR_SPEC" "IRInst.condbr ir_d8 ir_d5 ir_nl0 ir_d4 ir_nl0" "IRInst.condbr ir_d8 ir_d4 ir_nl0 ir_d5 ir_nl0"
expect PASS "P12 reverted"

echo
echo "== P13: uge vs ugt — the comparison operator at the closed end =="
sub "$BR_SPEC" "IRInst.icmp IRICmpOp.uge ir_br_tu32 ir_d0 ir_d1) ir_d8" "IRInst.icmp IRICmpOp.ugt ir_br_tu32 ir_d0 ir_d1) ir_d8"
expect FAIL "P13 mutated: idx >= start becomes idx > start in the bounded arm"; reason
sub "$BR_SPEC" "IRInst.icmp IRICmpOp.ugt ir_br_tu32 ir_d0 ir_d1) ir_d8" "IRInst.icmp IRICmpOp.uge ir_br_tu32 ir_d0 ir_d1) ir_d8"
expect PASS "P13 reverted"

echo
echo "== P14: ult vs ule — the comparison operator at the open end =="
sub "$BR_SPEC" "IRInst.icmp IRICmpOp.ult ir_br_tu32 ir_d0 ir_d2" "IRInst.icmp IRICmpOp.ule ir_br_tu32 ir_d0 ir_d2"
expect FAIL "P14 mutated: idx < end becomes idx <= end"; reason
sub "$BR_SPEC" "IRInst.icmp IRICmpOp.ule ir_br_tu32 ir_d0 ir_d2" "IRInst.icmp IRICmpOp.ult ir_br_tu32 ir_d0 ir_d2"
expect PASS "P14 reverted"

echo
echo "== P15: the SENTINEL literal =="
sub "$BR_SPEC" "IRConst.int_ 4294967295" "IRConst.int_ 4294967294"
expect FAIL "P15 mutated: the sentinel is u32::MAX - 1"; reason
sub "$BR_SPEC" "IRConst.int_ 4294967294" "IRConst.int_ 4294967295"
expect PASS "P15 reverted"

echo
echo "== P16: the two lower-bound comparisons SHARED instead of recomputed =="
# NOTE the anchors: after the mutation `... ir_d1) ir_d7` matches BOTH bb1 and
# bb2, so a revert keyed on it would match two `const SRC_` lines, the helper
# would abort, and every case after this one would run against a still-mutated
# file. Both anchors therefore carry the following `condbr`, which only bb2 has.
sub "$BR_SPEC" "ir_d1) ir_d8) (ir_nd (IRInst.condbr" "ir_d1) ir_d7) (ir_nd (IRInst.condbr"
expect FAIL "P16 mutated: bb2 binds the same SSA id bb1 does"; reason
sub "$BR_SPEC" "ir_d1) ir_d7) (ir_nd (IRInst.condbr" "ir_d1) ir_d8) (ir_nd (IRInst.condbr"
expect PASS "P16 reverted"

echo
echo "== P17: the join CHAIN collapsed =="
sub "$BR_SPEC" "(ir_bd1 (ir_nd (IRInst.br ir_d3 (ir_nl1 ir_d4))))" "(ir_bd1 (ir_nd (IRInst.br ir_d6 (ir_nl1 ir_d4))))"
expect FAIL "P17 mutated: the inner join branches to itself instead of to the outer join"; reason
sub "$BR_SPEC" "(ir_bd1 (ir_nd (IRInst.br ir_d6 (ir_nl1 ir_d4))))" "(ir_bd1 (ir_nd (IRInst.br ir_d3 (ir_nl1 ir_d4))))"
expect PASS "P17 reverted"

echo
echo "== P18: the flip-event lineage digest =="
sub "$BR_JSON" '  "lineage": "sha256:2b2d0f246983429cbe978c36cf22975101824f610b0ea35b8152251a1bbc0c2a",' '  "lineage": "sha256:2b2d0f246983429cbe978c36cf22975101824f610b0ea35b8152251a1bbc0c2b",'
expect FAIL "P18 mutated: the FLIP EVENT's lineage differs from the coverage row's by one nibble"; reason
sub "$BR_JSON" '  "lineage": "sha256:2b2d0f246983429cbe978c36cf22975101824f610b0ea35b8152251a1bbc0c2b",' '  "lineage": "sha256:2b2d0f246983429cbe978c36cf22975101824f610b0ea35b8152251a1bbc0c2a",'
expect PASS "P18 reverted"

echo
echo "== P19: markers_exact NON-VACUITY =="
sub "$BR_JSON" '"markers_detail": "21 marker line(s) identical"' '"markers_detail": "0 marker line(s) identical"'
expect FAIL "P19 mutated: the 21-line marker sequence becomes empty"; reason
sub "$BR_JSON" '"markers_detail": "0 marker line(s) identical"' '"markers_detail": "21 marker line(s) identical"'
expect PASS "P19 reverted"

echo
echo "== P20: the interpreter differential's SAMPLE COUNT =="
sub "$BR_JSON" '"samples": 125' '"samples": 0'
expect FAIL "P20 mutated: `agreed` on zero samples is a vacuous agreement"; reason
sub "$BR_JSON" '"samples": 0' '"samples": 125'
expect PASS "P20 reverted"

echo
echo "== P21: FIXTURE DELETED — the gate must fail CLOSED, not vacuously pass =="
mv "$BR_FIX" "$BR_FIX.bak"
expect FAIL "P21 mutated: emitted trust-ir fixture absent"; reason
mv "$BR_FIX.bak" "$BR_FIX"
expect PASS "P21 reverted"

echo
echo "== P22: FIXTURE EMPTIED =="
cp "$BR_FIX" "$BR_FIX.bak"; : > "$BR_FIX"
expect FAIL "P22 mutated: emitted fixture is zero bytes"; reason
mv "$BR_FIX.bak" "$BR_FIX"
expect PASS "P22 reverted"

echo
echo "PERTURBATIONS: $pass expected outcomes, $fail unexpected"
[[ $fail -eq 0 ]]
