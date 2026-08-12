#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
#
# Foreign-kernel cross-check of the clean-verify self-verification metatheory:
# export the FULL live spec environment to a self-contained Lean 4 file and have
# an INDEPENDENT kernel (Lean 4, disjoint implementation) re-check every emitted
# declaration. This is the referee-runnable form of
# docs/SELF_VERIFICATION_CERTIFICATE.md section 4.
#
# It asserts INVARIANTS, not exact counts, so it stays green as the metatheory
# grows (the decl/coverage totals climb commit-to-commit; the invariants hold):
#
#   1. Lean accepts the whole export           — 0 `error:` lines, exit 0
#   2. Exactly the 3 foundational axioms        — {propext, Quot.sound, Classical.choice}
#   3. Zero skips                               — every spec definition is cross-checked
#   4. 100% spec coverage                       — direct + via-block == total
#   5. Flagship theorems reach no axiom          — `#print axioms` says "does not depend on any axioms"
#
# Requires the pinned Lean toolchain (leanprover/lean4:v4.30.0-rc2) on PATH via
# elan. Usage:  scripts/self_verify_crosscheck.sh
# Exit 0 iff every invariant holds; prints the measured numbers either way.

set -uo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO"

TOOLCHAIN="leanprover/lean4:v4.30.0-rc2"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
EXPORT="$WORK/CleanVerifyExportAll.lean"
SUMMARY="$WORK/export_summary.txt"
LEANOUT="$WORK/lean_check.txt"

# Flagship roots whose #print axioms footer must report a zero-axiom closure.
FLAGSHIPS=(
  "CleanVerify.tc_infer_soundness"
  "CleanVerify.bootstrap_infer_sound"
  "CleanVerify.whnf_terminates_well_typed_dependent"
  # C4 / the crystal: the bridge's keystone rule and its non-vacuity witness.
  # NOTE: this array only greps output that `lean_export`'s DEFAULT_ROOTS
  # decides to emit. Adding a name HERE alone reports "did NOT report a
  # zero-axiom closure" for a declaration that is in fact axiom-free — the two
  # lists must be changed together.
  "CleanVerify.impl_bridge_fvar"
  "CleanVerify.impl_bridge_fvar_witness"
)

fail() { echo "FAIL: $*" >&2; exit 1; }

command -v lean >/dev/null 2>&1 || command -v ~/.elan/bin/lean >/dev/null 2>&1 \
  || fail "no lean on PATH (install elan + $TOOLCHAIN)"
LEAN="$(command -v lean || echo "$HOME/.elan/bin/lean")"

echo "==> building lean_export (release)"
cargo build --locked --release -p clean-verify --bin lean_export >/dev/null 2>&1 \
  || fail "lean_export build failed"

echo "==> exporting full live spec -> Lean"
./target/release/lean_export --all-spec --out "$EXPORT" 2>"$SUMMARY" \
  || fail "lean_export run failed"

# Invariant 3 — zero skips.
grep -q "skipped: none" "$SUMMARY" || fail "export has skips: $(grep -i skipped "$SUMMARY")"

# Invariant 2 — exactly the 3 foundational axioms.
naxioms="$(sed -n 's/.*explicit axioms in export (\([0-9]*\)):.*/\1/p' "$SUMMARY")"
[ "$naxioms" = "3" ] || fail "expected 3 explicit axioms, got '${naxioms:-?}'"
for ax in propext Quot.sound Classical.choice; do
  grep -qE "^\[lean_export\]   axiom $ax\$" "$SUMMARY" \
    || fail "missing foundational axiom in export: $ax"
done
grep -E "^\[lean_export\]   axiom " "$SUMMARY" | grep -qvE "axiom (propext|Quot\.sound|Classical\.choice)$" \
  && fail "export carries a non-foundational axiom: $(grep 'axiom ' "$SUMMARY")"

# Invariant 4 — 100% spec coverage (direct + via-block == total).
read -r direct viablock total < <(sed -n \
  's/.*coverage: \([0-9]*\) directly + \([0-9]*\) via inductive blocks, of \([0-9]*\) total.*/\1 \2 \3/p' "$SUMMARY")
[ -n "${total:-}" ] || fail "could not parse coverage line"
[ "$((direct + viablock))" = "$total" ] \
  || fail "coverage not 100%: $direct + $viablock != $total"

emitted="$(sed -n 's/.*emitted \([0-9]*\) Lean declarations.*/\1/p' "$SUMMARY")"

echo "==> lean $TOOLCHAIN re-checking $emitted declarations"
"$LEAN" "+$TOOLCHAIN" "$EXPORT" >"$LEANOUT" 2>&1
lexit=$?

# Invariant 1 — Lean accepts (exit 0, no error lines).
nerr="$(grep -c 'error:' "$LEANOUT")"
[ "$lexit" = "0" ] || fail "lean exited $lexit"
[ "$nerr" = "0" ] || { grep 'error:' "$LEANOUT" | head; fail "lean reported $nerr error(s)"; }

# Invariant 5 — flagship theorems reach no axiom.
for f in "${FLAGSHIPS[@]}"; do
  grep -qF "'$f' does not depend on any axioms" "$LEANOUT" \
    || fail "flagship '$f' did NOT report a zero-axiom closure"
done

echo ""
echo "PASS — foreign-kernel cross-check green"
echo "  toolchain          : $TOOLCHAIN"
echo "  emitted decls      : $emitted"
echo "  spec coverage      : $direct direct + $viablock via-block = $total (100%)"
echo "  explicit axioms    : 3 (propext, Quot.sound, Classical.choice)"
echo "  skips              : 0"
echo "  lean errors        : 0"
echo "  flagship closures  : ${#FLAGSHIPS[@]} × zero-axiom"
exit 0
