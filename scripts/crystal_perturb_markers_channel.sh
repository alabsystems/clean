#!/usr/bin/env bash
# Negative controls for the MARKERS-CHANNEL witness (crystal A0).
#
# `markers_exact: true` is VACUOUS on every crystal chain body — the flag compares zero marker
# lines against zero marker lines. `markers_channel_witness.json` discharges the part of that
# which was actually in doubt (is the channel an instrument at all?) with a two-sided witness.
#
# A witness is only worth its ink if corrupting it makes the gate FAIL. That is what this
# script establishes: each case mutates one recorded value, asserts the test binary FAILS,
# reverts, and asserts it PASSES again. A mutation that leaves the suite green means the
# assertion was decorative.
#
# The fixture is read at RUNTIME, so the compiled binary is driven directly — a perturbation is
# a file edit with no rebuild involved.
#
#   CRYSTAL_BIN=<path to the compiled crystal_a1_lineage test binary> \
#     bash scripts/crystal_perturb_markers_channel.sh
set -uo pipefail
OUT="$(mktemp)"; trap 'rm -f "$OUT"' EXIT
REPO="$(cd "$(dirname "$0")/.." && pwd -P)"
BIN="${CRYSTAL_BIN:?set CRYSTAL_BIN to the compiled crystal_a1_lineage test binary}"
FILTER="${FILTER:-markers_channel}"

WIT="$REPO/crates/clean-verify/tests/fixtures/markers_channel_witness.json"

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

# Anchored substitution that FAILS LOUDLY when the anchor does not match exactly one line —
# a silent no-substitution would make a mutated run look green, which is the precise false
# negative this script exists to rule out.
sub() { python3 - "$1" "$2" "$3" <<'PY'
import sys
p, a, b = sys.argv[1], sys.argv[2], sys.argv[3]
lines = open(p).read().split("\n")
hits = [i for i, l in enumerate(lines) if a in l]
assert len(hits) == 1, "anchor must match exactly one line, matched %d: %s" % (len(hits), a[:80])
i = hits[0]
assert lines[i].count(a) == 1, "anchor not unique within its line: %s" % a[:80]
lines[i] = lines[i].replace(a, b, 1)
open(p, "w").write("\n".join(lines))
PY
}

# Path-addressed mutation. `sub` anchors on a LINE, which silently becomes ambiguous the
# moment a sibling witness carries the same value (adding `second_positive_witness` made
# `"flip_event_fired": true` match two lines). This addresses a JSON PATH instead and asserts
# the current value, so an ambiguous or drifted target fails loudly rather than mutating the
# wrong node.
setj() { python3 - "$WIT" "$1" "$2" "$3" <<'PY'
import sys, json
p, path, want, new = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]
j = json.load(open(p)); node = j; keys = path.split('.')
for k in keys[:-1]:
    node = node[k]
cur = json.dumps(node[keys[-1]])
assert cur == want, 'expected %s at %s, found %s' % (want, path, cur)
node[keys[-1]] = json.loads(new)
open(p, 'w').write(json.dumps(j, indent=1) + chr(10))
PY
}

echo "== baseline =="
expect PASS "unperturbed markers-channel witness"

echo
echo "== M1: a witness that compares ZERO marker lines is not a witness =="
sub "$WIT" '"marker_lines_compared": 8' '"marker_lines_compared": 0'
expect FAIL "M1 mutated: the positive witness compares nothing — the vacuity it rules out"; reason
sub "$WIT" '"marker_lines_compared": 0' '"marker_lines_compared": 8'
expect PASS "M1 reverted"

echo
echo "== M2: the recorded count must be the one the differential emitted =="
sub "$WIT" '"markers_detail": "8 marker line(s) identical"' '"markers_detail": "7 marker line(s) identical"'
expect FAIL "M2 mutated: detail string disagrees with marker_lines_compared"; reason
sub "$WIT" '"markers_detail": "7 marker line(s) identical"' '"markers_detail": "8 marker line(s) identical"'
expect PASS "M2 reverted"

echo
echo "== M3: a marker agreement on a body the flip never consumes exercises no gate =="
setj positive_witness.flip_event_fired true false
expect FAIL "M3 mutated: the positive witness does not flip"; reason
setj positive_witness.flip_event_fired false true
expect PASS "M3 reverted"

echo
echo "== M4: if markers_exact is never false, it is not a gate =="
setj negative_witness.markers_exact false true
expect FAIL "M4 mutated: the negative witness now agrees — nothing shows the flag can be false"; reason
setj negative_witness.markers_exact true false
expect PASS "M4 reverted"

echo
echo "== M5: the -O gate must actually REFUSE the disagreeing body =="
setj negative_witness.flip_event_fired false true
expect FAIL "M5 mutated: markers differ yet the body flipped — the gate gated nothing"; reason
setj negative_witness.flip_event_fired true false
expect PASS "M5 reverted"

echo
echo "== M6: if NO body compares a marker line, the channel has gone dark =="
sub "$WIT" '"of_those_comparing_MORE_THAN_ZERO": 27' '"of_those_comparing_MORE_THAN_ZERO": 0'
expect FAIL "M6 mutated: zero non-vacuous comparisons crate-wide"; reason
sub "$WIT" '"of_those_comparing_MORE_THAN_ZERO": 0' '"of_those_comparing_MORE_THAN_ZERO": 27'
expect PASS "M6 reverted"

echo
echo "== M7: the two classes must exhaust markers_exact=true =="
sub "$WIT" '"of_those_comparing_ZERO_marker_lines": 1055' '"of_those_comparing_ZERO_marker_lines": 1054'
expect FAIL "M7 mutated: 1054 + 17 != 1072, so the population is mis-partitioned"; reason
sub "$WIT" '"of_those_comparing_ZERO_marker_lines": 1054' '"of_those_comparing_ZERO_marker_lines": 1055'
expect PASS "M7 reverted"

echo
echo "== M8: FIXTURE DELETED — the gate must fail CLOSED, not vacuously pass =="
mv "$WIT" "$WIT.bak"
expect FAIL "M8 mutated: witness fixture absent"; reason
mv "$WIT.bak" "$WIT"
expect PASS "M8 reverted"

echo
echo "PERTURBATIONS: $pass expected outcomes, $fail unexpected"
[[ $fail -eq 0 ]]
