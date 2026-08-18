#!/usr/bin/env bash
# Perturbation proofs for the from_source_system chain's gates.
#
# The CFG / evidence gates read the spec source text and the fixtures from disk
# at RUNTIME (CARGO_MANIFEST_DIR), so the compiled test binary is driven
# directly: a perturbation is a file edit, the binary re-reads it, and no
# rebuild is involved. Each case mutates, asserts FAIL, reverts, asserts PASS.
set -uo pipefail
OUT="$(mktemp)"; trap 'rm -f "$OUT"' EXIT
REPO="$(cd "$(dirname "$0")/.." && pwd -P)"
BIN="${CRYSTAL_BIN:?set CRYSTAL_BIN to the compiled crystal_a1_lineage test binary}"
FILTER="${FILTER:-from_source_system}"

SPEC="$REPO/crates/clean-verify/src/spec/core_spec/eval_ir_from_source.rs"
FIX="$REPO/crates/clean-verify/tests/fixtures/from_source_system.trust-ir.txt"
JSON="$REPO/crates/clean-verify/tests/fixtures/from_source_system.lineage.json"

pass=0; fail=0
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

reason() { awk '/panicked at/{f=1} f{print "     | " $0} /^note: run with/{exit}' "$OUT" | head -8; }

# Substitute inside the DECLARATION lines only.
#
# The spec module also carries unit tests that quote the same block sources
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
expect PASS "baseline: all from_source_system gates green"

echo
echo "== P1: switch case list (the non-contiguous tag 11) =="
sub "$SPEC" "(ir_sc ir_d11 ir_d11 ir_sc0)" "(ir_sc ir_d10 ir_d11 ir_sc0)"
expect FAIL "P1 mutated: explicit case 11 renumbered to 10"; reason
sub "$SPEC" "(ir_sc ir_d10 ir_d11 ir_sc0)" "(ir_sc ir_d11 ir_d11 ir_sc0)"
expect PASS "P1 reverted"

echo
echo "== P2: an aggregate constant answer =="
sub "$SPEC" "(ir_cvar ir_d5)) ir_d10)" "(ir_cvar ir_d4)) ir_d10)"
expect FAIL "P2 mutated: Mizar answers Classical instead of SetTheoretic"; reason
sub "$SPEC" "(ir_cvar ir_d4)) ir_d10)" "(ir_cvar ir_d5)) ir_d10)"
expect PASS "P2 reverted"

echo
echo "== P3: the switch default target =="
sub "$SPEC" "IRInst.switch ir_d2 ir_d12 ir_nl0" "IRInst.switch ir_d2 ir_d11 ir_nl0"
expect FAIL "P3 mutated: default edge points at bb11"; reason
sub "$SPEC" "IRInst.switch ir_d2 ir_d11 ir_nl0" "IRInst.switch ir_d2 ir_d12 ir_nl0"
expect PASS "P3 reverted"

echo
echo "== P4: the join block's parameter =="
sub "$SPEC" "IRBlock.mk ir_d13 (ir_nl1 ir_d1)" "IRBlock.mk ir_d13 ir_nl0"
expect FAIL "P4 mutated: join block takes no parameter"; reason
sub "$SPEC" "IRBlock.mk ir_d13 ir_nl0" "IRBlock.mk ir_d13 (ir_nl1 ir_d1)"
expect PASS "P4 reverted"

echo
echo "== P5: the aggregate lane is not the integer lane =="
sub "$SPEC" "(IRInst.const_ ir_fs_tmode (ir_cvar ir_d2)) ir_d6)" "(IRInst.const_ ir_fs_tmode (IRConst.int_ ir_d2)) ir_d6)"
expect FAIL "P5 mutated: CubicalAgda's arm is a SCALAR constant, same number"; reason
sub "$SPEC" "(IRInst.const_ ir_fs_tmode (IRConst.int_ ir_d2)) ir_d6)" "(IRInst.const_ ir_fs_tmode (ir_cvar ir_d2)) ir_d6)"
expect PASS "P5 reverted"

echo
echo "== P6: the flip-event lineage digest =="
sub "$JSON" '  "lineage": "sha256:119b253d3aa6a24626021f621f0c8e0ce00b396467f55761bdd51deab3e6f135",' '  "lineage": "sha256:119b253d3aa6a24626021f621f0c8e0ce00b396467f55761bdd51deab3e6f136",'
expect FAIL "P6 mutated: flip-event lineage differs from the coverage row's by one nibble"; reason
sub "$JSON" '  "lineage": "sha256:119b253d3aa6a24626021f621f0c8e0ce00b396467f55761bdd51deab3e6f136",' '  "lineage": "sha256:119b253d3aa6a24626021f621f0c8e0ce00b396467f55761bdd51deab3e6f135",'
expect PASS "P6 reverted"

echo
echo "== P7: the negative control =="
sub "$JSON" '"flip_events_crate_wide": 0' '"flip_events_crate_wide": 1'
expect FAIL "P7 mutated: -Ztrust-ir-flip=no produced an event"; reason
sub "$JSON" '"flip_events_crate_wide": 1' '"flip_events_crate_wide": 0'
expect PASS "P7 reverted"

echo
echo "== P8: the measured aggregate shape =="
sub "$JSON" '"arity": 1' '"arity": 2'
expect FAIL "P8 mutated: recorded arity is 2, not the measured 1"; reason
sub "$JSON" '"arity": 2' '"arity": 1'
expect PASS "P8 reverted"

echo
echo "== P9: FIXTURE DELETED — the gate must fail CLOSED, not vacuously pass =="
mv "$FIX" "$FIX.bak"
expect FAIL "P9 mutated: emitted trust-ir fixture absent"; reason
mv "$FIX.bak" "$FIX"
expect PASS "P9 reverted"

echo
echo "== P10: FIXTURE EMPTIED — a zero-byte fixture must not compare equal to an empty Clean CFG =="
cp "$FIX" "$FIX.bak"; : > "$FIX"
expect FAIL "P10 mutated: emitted fixture is zero bytes"; reason
mv "$FIX.bak" "$FIX"
expect PASS "P10 reverted"

echo
echo "PERTURBATIONS: $pass expected outcomes, $fail unexpected"
[[ $fail -eq 0 ]]
