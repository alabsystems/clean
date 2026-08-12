#!/usr/bin/env bash
# u2_battery.sh — the U2 universe-polymorphism probe battery (rung 0 of
# designs/2026-08-08-u2-universe-polymorphism-ladder.md).
#
# Pins TODAY'S measured elaborator behavior exactly: declaration-side
# polymorphism AND concrete constructor instantiation PASS (P1-P9; the
# loud rigid refusal P6 stays a FAIL pin), the remaining solver-gap
# uses FAIL with their pinned error shapes (P10-P12). Each U2
# rung names the probes it flips FAIL->PASS and this gate asserts
# everything else byte-stable. Fail-closed: any drift (a probe passing
# that must fail, failing that must pass, or failing DIFFERENTLY) exits 1.
#
# Usage: scripts/u2_battery.sh [--bin path/to/clean]
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BIN="${REPO_ROOT}/target/release/clean"
if [[ "${1:-}" == "--bin" ]]; then
  BIN="${2:?--bin requires a path argument}"
fi
[[ -x "$BIN" ]] || { echo "[u2-battery] FAIL: no executable clean binary at $BIN" >&2; exit 1; }

FIX="${REPO_ROOT}/tests/fixtures/universes"
OUT_JSON="${REPO_ROOT}/reports/u2-battery.json"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

# Provenance: fixtures and this script must be tracked and clean.
for f in "$FIX"/*.lean "scripts/u2_battery.sh"; do
  rel="${f#"$REPO_ROOT"/}"
  git -C "$REPO_ROOT" ls-files --error-unmatch "$rel" > /dev/null 2>&1 \
    || { echo "[u2-battery] FAIL: gate input not tracked: $rel" >&2; exit 1; }
done
DIRTY="$(git -C "$REPO_ROOT" status --porcelain -- "$FIX" scripts/u2_battery.sh)"
[[ -z "$DIRTY" ]] || { echo "[u2-battery] FAIL: gate inputs dirty:"$'\n'"$DIRTY" >&2; exit 1; }

pass_probe() { # file expected_pass_count
  local f="$1" want="$2"
  local out
  out="$("$BIN" check --prelude builtin "$FIX/$f" 2>&1 | grep -E "passed" | tail -1)"
  [[ "$out" == *" $want passed, 0 failed"* ]] \
    || { echo "[u2-battery] FAIL: $f expected '$want passed, 0 failed', got: $out" >&2; exit 1; }
  echo "  PASS-pinned  $f ($want decls)"
}

fail_probe() { # file expected_error_fragment
  local f="$1" frag="$2"
  local out rc=0
  out="$("$BIN" check --prelude builtin "$FIX/$f" 2>&1)" || rc=$?
  [[ "$rc" -ne 0 ]] \
    || { echo "[u2-battery] FAIL: $f must FAIL today but passed — a rung flipped it; update the battery deliberately" >&2; exit 1; }
  grep -qF "$frag" <<<"$out" \
    || { echo "[u2-battery] FAIL: $f failed with an UNPINNED shape (expected fragment '$frag'):"$'\n'"$out" >&2; exit 1; }
  echo "  FAIL-pinned  $f ($frag)"
}

echo "[u2-battery] declaration-side polymorphism (must PASS):"
pass_probe p01_poly_def_two_uses.lean 3
pass_probe p02_autobound.lean 1
pass_probe p03_struct_explicit_max.lean 1
pass_probe p04_struct_no_ascription.lean 1
pass_probe p05_inductive_explicit_sort.lean 1
pass_probe p07_explicit_mk.lean 3
pass_probe p08_implicit_mk.lean 2
pass_probe p09_concrete_solve.lean 2
pass_probe p13_poly_mtower_corec.lean 21
pass_probe p14_at_explicit_universe_inst.lean 6
pass_probe p11_codata_upoly.lean 5
pass_probe p15_sigma_over_type.lean 2
pass_probe p10_inductive_default.lean 6
pass_probe p16_two_universe_mcore.lean 13
pass_probe p17_hk_functor_args.lean 7
pass_probe p19_cmp_arrow_precedence.lean 7
pass_probe p18_hk_poly_const_arg.lean 2
pass_probe p20_level_generalization.lean 7
pass_probe p21_explicit_list_autoextends.lean 2
pass_probe p22_exists_working_forms.lean 5
pass_probe p23_exists_intro.lean 3
pass_probe p24_prelude_fidelity.lean 23
pass_probe p25_nat_homogeneous_instances.lean 7
pass_probe p26_rfl_match_pattern.lean 3
pass_probe p27_quotient_setoid.lean 8
pass_probe p28_bare_ctor_expected_type.lean 4

echo "[u2-battery] pinned failures (the solver gap + defaults + gates):"
fail_probe p06_rigid_refusal_MUST_FAIL.lean 'TypeMismatch { expected: "Sort u", actual: "Type" }'
fail_probe p12_sigma_over_type_MUST_FAIL.lean 'TypeMismatch { expected: "Type", actual: "Type 1" }'

GIT_SHA="$(git -C "$REPO_ROOT" rev-parse HEAD)"
python3 - "$OUT_JSON" "$GIT_SHA" "$BIN" "$FIX" <<'PY'
import json, sys, hashlib, glob, os
out, sha, bin_path, fix = sys.argv[1:5]
def sha256(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()
report = {
    "schema": "u2-battery-v1",
    "commit": sha,
    "clean_binary_sha256": sha256(bin_path),
    "fixtures": {os.path.basename(p): sha256(p) for p in sorted(glob.glob(f"{fix}/*.lean"))},
    "split": {
        "pass": ["p01", "p02", "p03", "p04", "p05", "p07", "p08", "p09", "p10", "p11", "p13", "p14", "p15", "p16", "p17", "p18", "p19", "p20", "p21", "p22", "p23", "p24", "p25", "p26", "p27", "p28"],
        "fail_pinned": ["p06", "p12"],
    },
    "note": "P6 is a SOUND loud reject (rigid refusal) and stays a FAIL pin "
            "forever; P8/P9 FLIPPED at rung 2 (structure-ctor params were "
            "explicit, not a solver gap); P13 pins the rung-6 lane OPEN: the "
            ".{u}-polymorphic indexed M-tower + coherence + Subtype carrier + "
            "IMcorec + rfl head law (21 decls) all elaborate+kernel-check on "
            "the rung-2+1a+3a elaborator. P10 FLIPPED at rung 5 "
            "(omitted-sort inference from ctor fields, .{u}-declared only); "
            "P11 FLIPPED at rung 7 part 2 "
            "(codata .{u} live, rfl-computing at u=0 and u=1); P12's `: Type` "
            "large-Sigma is a SOUND forever-reject like P6 (ill-typed in Lean "
            "too) with P15 pinning the working Type-1 forms; "
            "P14 FLIPPED same day: "
            "the parser bound argument-position .{} to the application head "
            "(f.{u+1} PUnit instead of PUnit.{u+1}) — fixed like projection "
            "attachment — see the U2 ladder doc.",
    "gate_command": "scripts/u2_battery.sh",
}
json.dump(report, open(out, "w"), indent=2)
print(f"[u2-battery] GREEN — wrote {out}")
PY
