#!/usr/bin/env bash
# source_frontier_battery.sh — the Mathlib-SOURCE frontier probe battery
# (FRONTIER STAGE 0, "the instrument";
#  docs/analysis/frontier-next-class-2026-08-25.md §6).
#
# Pins TODAY'S measured behaviour on the three largest single-mechanism classes
# of the 2026-08-25 five-file source-elaboration measurement. Every probe runs
# `--prelude builtin` with no Mathlib and no imports, in well under a second.
#
#   CLASS II  dot notation whose target does not resolve       (44/497 entries)
#   CLASS I   instance search through a `def`-based alias      (34/497 entries)
#   MASK 3    auto-implicit swallowing an unresolved head      (17/497 entries)
#
# 2026-08-26, FRONTIER STAGE I-1: the CLASS I rows are no longer all baselines.
# p08/p09/p11 are re-pinned FAIL -> PASS by the candidate-side repair, p18 pins
# the goal-side residue that is still open, and p19-p23 pin the risk axis a
# capability-adding change to instance search creates — more candidates must
# never mean a wrong candidate. See the CLASS I re-pin block below.
#
# 2026-08-26, FRONTIER STAGE I-2: the goal side closes. p18 is re-pinned
# FAIL -> PASS (and renamed), and p24/p25/p26 are new — the capability with the
# built-in `Decidable`/`Eq` bridge removed and over a DEPENDENT telescope, plus
# the two refusals that keep it from being a blanket: the conclusion must hold
# for an ARBITRARY argument (the telescope opens over rigid locals, never
# metavariables), and an over-deep goal is refused WHOLE, never truncated into a
# lambda of the wrong arity.
#
# Fail-closed: any drift — a probe passing that must fail, failing that must
# pass, or failing DIFFERENTLY — exits 1. A probe that flips is a RESULT: re-pin
# it deliberately, with a dated note here, exactly as scripts/u2_battery.sh does.
#
# WHAT THIS BATTERY CANNOT SAY, and no reading of it may claim (recon §7.1):
# nothing about corpus counts. It has no Mathlib corpus and measures no
# success_count, no per-file delta, and no ratchet. Those need the corpus box:
#   scripts/source_elab_gate.sh --jobs 2 --update
#
# Usage: scripts/source_frontier_battery.sh [--bin path/to/clean]
# Env:   SRCFRONTIER_REQUIRE_PINNED=1  fail closed unless every gate input is
#                                      git-tracked and clean (set this wherever
#                                      the battery is wired into a gate).
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BIN="${REPO_ROOT}/target/release/clean"
if [[ "${1:-}" == "--bin" ]]; then
  BIN="${2:?--bin requires a path argument}"
fi
[[ -x "$BIN" ]] || { echo "[srcfrontier] FAIL: no executable clean binary at $BIN" >&2; exit 1; }

FIX="${REPO_ROOT}/tests/fixtures/source_frontier"
OUT_JSON="${REPO_ROOT}/reports/source-frontier-battery.json"

# Provenance. u2_battery.sh HARD-FAILS on an untracked or dirty input because it
# is wired into a gate; this battery lands with its fixtures, so it reports the
# same fact instead of asserting it, and the artifact records which it was.
# `SRCFRONTIER_REQUIRE_PINNED=1` turns the report back into an assertion — an
# artifact from an unpinned run can never be mistaken for a pinned one, and a
# gate can never accidentally accept one.
INPUTS_PINNED=true
UNPINNED_DETAIL=""
for f in "$FIX"/*.lean "$FIX/README.md" "${BASH_SOURCE[0]}"; do
  rel="${f#"$REPO_ROOT"/}"
  git -C "$REPO_ROOT" ls-files --error-unmatch "$rel" > /dev/null 2>&1 \
    || { INPUTS_PINNED=false; UNPINNED_DETAIL+="untracked: $rel"$'\n'; }
done
DIRTY="$(git -C "$REPO_ROOT" status --porcelain -- "$FIX" "${BASH_SOURCE[0]}")"
if [[ -n "$DIRTY" ]]; then
  INPUTS_PINNED=false
  UNPINNED_DETAIL+="$DIRTY"$'\n'
fi
if [[ "$INPUTS_PINNED" != true ]]; then
  if [[ "${SRCFRONTIER_REQUIRE_PINNED:-0}" == "1" ]]; then
    echo "[srcfrontier] FAIL: gate inputs not tracked-and-clean:"$'\n'"$UNPINNED_DETAIL" >&2
    exit 1
  fi
  echo "[srcfrontier] PROVENANCE: UNPINNED — inputs are not tracked-and-clean."
  echo "[srcfrontier]   verdicts below are still measured; the artifact records inputs_pinned=false."
  printf '%s' "$UNPINNED_DETAIL" | sed 's/^/[srcfrontier]   /'
fi

pass_probe() { # file expected_pass_count
  local f="$1" want="$2"
  local out
  out="$("$BIN" check --prelude builtin "$FIX/$f" 2>&1 | grep -E "passed" | tail -1)"
  [[ "$out" == *" $want passed, 0 failed"* ]] \
    || { echo "[srcfrontier] FAIL: $f expected '$want passed, 0 failed', got: $out" >&2; exit 1; }
  echo "  PASS-pinned  $f ($want decls)"
}

fail_probe() { # file expected_error_fragment
  local f="$1" frag="$2"
  local out rc=0
  out="$("$BIN" check --prelude builtin "$FIX/$f" 2>&1)" || rc=$?
  [[ "$rc" -ne 0 ]] \
    || { echo "[srcfrontier] FAIL: $f must FAIL today but passed — read its header before re-pinning" >&2; exit 1; }
  grep -qF -- "$frag" <<<"$out" \
    || { echo "[srcfrontier] FAIL: $f failed with an UNPINNED shape (expected fragment '$frag'):"$'\n'"$out" >&2; exit 1; }
  echo "  FAIL-pinned  $f ($frag)"
}

fail_probe_json() { # file expected_error_fragment  -- pins the DISPLAY form
  # The terminal renders a top-level declaration's failure with `{e:?}` and a
  # namespaced one with `{e}` (crates/clean-cli/src/cmd_core.rs). Mathlib
  # declarations are all namespaced, so the artifact carries Display — this
  # helper pins the string the CORPUS REPORT will hold, read out of the report
  # itself rather than out of the terminal.
  local f="$1" frag="$2"
  local out rc=0
  out="$("$BIN" check --prelude builtin --json "$FIX/$f" 2>&1)" || rc=$?
  [[ "$rc" -ne 0 ]] \
    || { echo "[srcfrontier] FAIL: $f must FAIL today but passed" >&2; exit 1; }
  grep -qF -- "$frag" <<<"$out" \
    || { echo "[srcfrontier] FAIL: $f report shape drifted (expected fragment '$frag'):"$'\n'"$out" >&2; exit 1; }
  echo "  FAIL-pinned  $f [report form] ($frag)"
}

echo "[srcfrontier] CLASS II controls — a receiver with no nameable head DOES do"
echo "              dot notation when the target resolves (so class II is a"
echo "              missing NAME, not a missing feature):"
pass_probe p01_control_pi_receiver_resolvable.lean 4
pass_probe p04_control_namespaced_resolvable.lean 3
pass_probe p07_control_proj_receiver_resolvable.lean 7
pass_probe p13_control_strict_implicit_resolvable.lean 4

echo "[srcfrontier] CLASS II — the two sub-shapes, now NAMED (stage 0 repair):"
# Before the 2026-08-26 repair both of these read
#   NotImplemented("cannot extract type name from <raw Expr dump>")
# with the identifier deleted. The pinned fragment is the NAME, because that is
# the property the repair exists to deliver and the one that must not regress.
# Verdicts are unchanged across the repair — measured probe-by-probe, and that
# is the point: the repair converts opaque entries, it does not fix them.
# RE-PINNED 2026-08-27 (finding-2 residual (b)): these pinned the Rust DEBUG
# struct rendering, which only the TOP-LEVEL declaration path ever printed.
# Unifying the two render paths on Display — the form every NAMESPACED
# declaration already used, i.e. every Mathlib declaration and therefore every
# corpus artifact entry — moves these fragments deliberately. The content is
# strictly larger, not smaller: the Display form carries the identifier, the
# receiver type, the reduced head AND (new) the line number the namespaced
# path never had.
fail_probe p03_dot_pi_receiver_MUST_FAIL.lean 'Unknown identifier: MyInj.nosuchfield'
fail_probe p03_dot_pi_receiver_MUST_FAIL.lean 'whose head does not name a type after reduction (Pi)'
fail_probe p06_dot_proj_receiver_MUST_FAIL.lean 'Unknown identifier: MyLE.le.nosuchfield'
fail_probe p06_dot_proj_receiver_MUST_FAIL.lean 'after reduction (Proj(MyLE, 0))'
# p05 is the untouched `Const`-headed path: it must stay byte-stable, which is
# what proves the repair did not leak out of its site.
# RE-PINNED 2026-08-27 (finding-2 residual (b), same Debug->Display unification)
fail_probe p05_control_const_head_MUST_FAIL.lean \
  'Unknown identifier: And.nosuchfield'
# p17 pins the DISPLAY form — the one the corpus artifact will carry. Its
# leading `Unknown identifier:` is what moves these 44 entries out of
# `not implemented (elaborator NYI)` in scripts/srcelab_classify.py, and the
# name-first order is what survives per_error_class's 400-char truncation.
fail_probe_json p17_artifact_form_MUST_FAIL.lean \
  'Unknown identifier: Fr.MyInj.nosuchfield; dot notation `.nosuchfield`'

echo "[srcfrontier] CLASS I controls:"
pass_probe p10_control_class_declared.lean 3
pass_probe p12_control_explicit_dictionary.lean 2

# ---------------------------------------------------------------------------
# CLASS I RE-PIN, 2026-08-26 — FRONTIER STAGE I-1, the candidate side.
#
# p08, p09 and p11 were FAIL pins here from 2026-08-26 (stage 0) until the
# candidate-side match landed the same day. All three flipped FAIL -> PASS and
# are re-pinned as PASS probes with their exact declaration counts; the three
# fixtures were renamed to drop `_MUST_FAIL` (u2_battery.sh's convention for a
# probe whose pinned verdict moves) and each carries the old pin in its header.
#
#   p08  0/2 -> 2/0   the `Decidable (@Eq α a b)` bridge reaches its dictionary
#   p11  0/1 -> 1/0   the candidate face: a local matched as-bound
#   p09  1/2 -> 2/0   the goal face
#
# p09 is the one to read carefully. The recon (§4.5, §6) scheduled it for
# stage I-2 — the goal-side ∀-telescope — and expected stage I-1 to leave it
# red. It went green at stage I-1, because its carrier is a local binder of
# the same declaration, so the goal had to be FOUND and not BUILT. The goal
# side is NOT therefore done: p18 below is the residue that still needs it.
#
# The pinned counts are exact (`N passed, 0 failed`), so a later change that
# resolves MORE or FEWER declarations in these files fails this gate.
# ---------------------------------------------------------------------------
echo "[srcfrontier] CLASS I — goal face, candidate face, and the decEq bridge"
echo "              (all three FLIPPED by stage I-1 on 2026-08-26):"
pass_probe p08_deceq_bridge.lean 2
pass_probe p09_deceq_goal_face.lean 2
pass_probe p11_unwhnfd_goal.lean 1

echo "[srcfrontier] CLASS I — the GOAL side, FLIPPED by stage I-2 on 2026-08-26:"
# A Pi-shaped alias goal whose answer must be CONSTRUCTED (no local of that
# type in scope; the body answerable only from the global table) is now solved
# by opening the goal's forall-telescope over rigid locals, resolving the
# conclusion, and re-abstracting into lambdas. p18 was the stage's exit
# criterion and is re-pinned FAIL -> PASS (2/1 -> 3/0); its in-file control
# `bodyIsSolvable` was passing before and after, so what moved is the
# abstraction and not the body.
pass_probe p18_goal_side_constructed.lean 3
# THE GENERAL CAPABILITY, with the hand-written `Decidable`/`Eq` bridge out of
# the picture (p18 and p09 both run through it): a user-declared class, a
# user-declared `def`-based alias, a user-declared global instance — and a
# DEPENDENT telescope (`(x : α) → (y : x = x) → …`) whose second binder type
# mentions the first binder, which comes out well-typed only if abstraction
# reaches into binder types and not just the conclusion.
pass_probe p24_goal_side_telescope_no_bridge.lean 10

echo "[srcfrontier] CLASS I — the risk axis: MORE candidates must not mean a"
echo "              WRONG candidate. Selection, refusal, ambiguity, hygiene:"
# p19/p20 are a pair and neither means anything alone: p19 alone is satisfied
# by "grab any local", p20 alone by "grab nothing". Together they pin the
# boundary. p19's two `if`s take their OWN dictionaries and survive the kernel
# re-check; p20's foreign carrier is refused, with its pre-existing diagnostic
# unchanged.
pass_probe p19_control_two_carriers_selected.lean 1
fail_probe p20_wrong_carrier_refused_MUST_FAIL.lean \
  'failed to synthesize instance Decidable'
# AMBIGUITY. Half 1 of p21 proves a telescoped local IS a viable candidate for
# `MyE Nat`; half 2 proves that at a class which ALSO has a global instance,
# the GLOBAL still wins — measured by `rfl`, which closes only if the global
# was selected. The candidate-side match runs only after the primary search
# has returned None, so this is structural, not lucky.
pass_probe p21_control_global_beats_telescoped_local.lean 10
# HYGIENE. A telescope binder the goal does not determine is refused rather
# than emitted as `h ?x` — an unassigned metavariable is carried as a tagged
# free variable and would surface far away as the kernel's "Declaration
# contains free variables".
fail_probe p22_undetermined_binder_refused_MUST_FAIL.lean \
  'def undetermined: failed to synthesize instance `MyD True`'
# THE GENERAL CAPABILITY, with the hand-written `Decidable`/`Eq` bridge out of
# the picture: a user-declared class, a user-declared `def`-based alias, and a
# conclusion match that returns the local APPLIED (`h a b`), not the binder.
pass_probe p23_control_telescoped_local_no_bridge.lean 4
# ARBITRARY ARGUMENT — the refusal that makes p24 mean something. The goal
# telescope is opened over rigid LOCALS, never metavariables: an instance that
# covers exactly ONE argument (`MyD (true = true)`) must not be generalised
# into `fun x y => trueMyD`, which is ill-typed for every other argument.
# Opening with metavariables would have let the conclusion's search ASSIGN the
# telescope variables and "succeed". The count is pinned too: p25's in-file
# control `bodyAtTrue` resolves that one argument today, so the refusal is not
# "the instance is unreachable".
fail_probe p25_goal_side_arbitrary_argument_MUST_FAIL.lean \
  'failed to synthesize instance `(b : Bool) -> (b1 : Bool) -> MyD (b = b1)`'
fail_probe p25_goal_side_arbitrary_argument_MUST_FAIL.lean '5 passed, 1 failed'
# ARITY — the cap (MAX_GOAL_TELESCOPE = 8) refuses the goal WHOLE rather than
# truncating it. A truncated telescope would emit a lambda of the wrong arity.
# The pinned count carries the in-file control: `useNarrow`, the same alias
# shape at two binders, PASSES in the same file, so what is refused is the
# arity and not the shape.
fail_probe p26_goal_telescope_arity_cap_MUST_FAIL.lean \
  'def useWide: elaboration left unresolved variables'
fail_probe p26_goal_telescope_arity_cap_MUST_FAIL.lean '7 passed, 1 failed'

# RE-PINNED 2026-08-27 (finding-2 residual (b)) — batch: every remaining
# fragment above that quoted the Rust DEBUG struct rendering now quotes the
# unified Display form. Same assertions, same fixtures, strictly more
# readable content; no probe changed its PASS/FAIL verdict.
echo "[srcfrontier] MASK 3 — auto-implicit swallowing an unresolved applied head:"
# p14 is the recon's own probe and its verdict is unchanged: in a VALUE position
# the identifier is named, because auto-implicit is off inside term bodies.
fail_probe p14_control_term_body_MUST_FAIL.lean \
  'Unknown identifier: nosuchfn'
# p15/p16 FIRE the mask the recon could not fire (§2.6, §7.5 leave the class
# unattributed pending corpus lines). They are not needed: the trigger is a
# SIGNATURE position, and the identifier is deleted from the report there.
# The fragment stops before the level parameter's name so it pins the
# MECHANISM (a Sort-typed head over-applied), not a mint counter.
# RE-PINNED 2026-08-27 (finding-2 mask-3 repair): p15/p16 used to pin the
# TooManyArguments dump with the identifier DELETED. The repair names the
# identifier auto-implicit swallowed, so the fragments move deliberately —
# the battery's own doctrine, a flipped probe is re-pinned with a dated note.
# p30 is the boundary control: a REAL binder over-applied must keep the old
# message byte-for-byte, so the repair cannot be an over-broad "name every
# over-applied head".
fail_probe p15_sorthead_binder_type_MUST_FAIL.lean 'Unknown identifier: nosuchpred'
fail_probe p15_sorthead_binder_type_MUST_FAIL.lean 'auto-bound implicit'
fail_probe p16_sorthead_result_type_MUST_FAIL.lean 'Unknown identifier: nosuchfn'
fail_probe p16_sorthead_result_type_MUST_FAIL.lean 'auto-bound implicit'
fail_probe p30_real_binder_over_applied_MUST_FAIL.lean 'Too many arguments'
fail_probe p30_real_binder_over_applied_MUST_FAIL.lean 'argument(s) remain'

GIT_SHA="$(git -C "$REPO_ROOT" rev-parse HEAD)"
mkdir -p "$(dirname "$OUT_JSON")"
INPUTS_PINNED="$INPUTS_PINNED" python3 - "$OUT_JSON" "$GIT_SHA" "$BIN" "$FIX" "${BASH_SOURCE[0]}" <<'PY'
import json, sys, hashlib, glob, os, re
out, sha, bin_path, fix, script = sys.argv[1:6]

def sha256(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()

# The split is DERIVED from the probe calls in this script, never
# hand-maintained (the u2 battery shipped a hardcoded split that drifted from
# the gate it described; same failure mode, same fix).
script_text = open(script).read()
split_pass = sorted(set(re.findall(r"^pass_probe (p\d+)", script_text, re.M)))
split_fail = sorted(set(re.findall(r"^fail_probe(?:_json)? (p\d+)", script_text, re.M)))
report = {
    "schema": "source-frontier-battery-v1",
    "commit": sha,
    "inputs_pinned": os.environ["INPUTS_PINNED"] == "true",
    "clean_binary_sha256": sha256(bin_path),
    "fixtures": {os.path.basename(p): sha256(p) for p in sorted(glob.glob(f"{fix}/*.lean"))},
    "split": {"pass": split_pass, "fail_pinned": split_fail},
    "classes": {
        "class II (dot target unresolved)": ["p01", "p03", "p04", "p05", "p06",
                                             "p07", "p13", "p17"],
        "class I (def-based class alias)": ["p08", "p09", "p10", "p11", "p12",
                                            "p18", "p19", "p20", "p21", "p22",
                                            "p23", "p24", "p25", "p26"],
        "mask 3 (auto-implicit Sort head)": ["p14", "p15", "p16"],
    },
    "scope_note": (
        "Builtin-prelude probes only. This artifact carries NO corpus count, no "
        "success_count, no per-file delta and no ratchet state, and none may be "
        "inferred from it: this box has no Mathlib corpus "
        "(docs/analysis/frontier-next-class-2026-08-25.md §7.1). The corpus "
        "reading is `scripts/source_elab_gate.sh --jobs 2 --update`, elsewhere."
    ),
    "stage0_note": (
        "2026-08-26: the class-II message repair landed against these fixtures. "
        "ElabError::UnresolvedDotTarget replaces "
        "NotImplemented(\"cannot extract type name from <Expr dump>\") at the "
        "dot-notation site in infer/elab_proj.rs. Diagnostic only — all twelve "
        "pre-existing probe verdicts are byte-identical across it, and p05 pins "
        "the untouched Const-headed path. Classes I and mask 3 are UNCHANGED by "
        "stage 0; their probes are baselines taken before the work, not after."
    ),
    "stage1_note": (
        "2026-08-26 FRONTIER STAGE I-1, the CLASS I candidate side: "
        "ElabCtx::resolve_local_instance_telescoped in infer/instance.rs matches "
        "LOCAL instance binders that a `def`-based class alias had made invisible "
        "-- (A) as-bound, (C) whole normalised type for a Pi-shaped goal (the "
        "restriction that stops a bare-metavariable goal being SOLVED rather than "
        "matched), (B) under the local's forall-telescope. Consulted ONLY after "
        "the primary search has returned "
        "None, so no resolution that succeeded before can take a different answer "
        "now. Flipped FAIL->PASS: p08 (0/2->2/0), p09 (1/2->2/0), p11 (0/1->1/0); "
        "those three fixtures were renamed to drop _MUST_FAIL. p18/p19/p20/p21/"
        "p22/p23 are new: the goal-side residue, and the risk axis (selection, "
        "refusal, ambiguity, hygiene, and the capability with the decEq bridge "
        "removed from the picture). Every class-II and mask-3 verdict is "
        "byte-identical across it -- measured, all sixteen stage-0 fixtures re-run."
    ),
    "stage2_note": (
        "2026-08-26 FRONTIER STAGE I-2, the CLASS I GOAL side: "
        "ElabCtx::resolve_pi_goal_by_abstraction in infer/instance.rs solves a "
        "Pi-shaped instance goal -- the class alias the CALLER already "
        "delta-unfolded, with no local of that type in scope -- by opening its "
        "forall-telescope over fresh RIGID LOCALS, resolving the conclusion as an "
        "ordinary instance goal, and re-abstracting the locals into lambdas. "
        "Consulted ONLY after the primary search AND the stage I-1 candidate-side "
        "match have both returned None, so it can add resolutions and never change "
        "one. Ground goals only (a goal carrying metavariables is refused outright: "
        "solving the conclusion under the telescope could assign one of the goal's "
        "OWN metavariables to a term mentioning a telescope local, which "
        "abstraction of the returned term does not fix). Flipped FAIL->PASS: p18 "
        "(2/1 -> 3/0), renamed to drop _MUST_FAIL. p24/p25/p26 are new: the "
        "capability with the decEq bridge removed and a DEPENDENT telescope, the "
        "arbitrary-argument refusal (rigid locals, not metavariables), and the "
        "arity cap refusing whole rather than truncating. Every other probe "
        "verdict is byte-identical across it -- measured, all twenty-two "
        "pre-existing fixtures re-run before and after."
    ),
}
with open(out, "w") as f:
    json.dump(report, f, indent=2)
    f.write("\n")
print(f"[srcfrontier] wrote {out} "
      f"({len(split_pass)} pass-pinned, {len(split_fail)} fail-pinned, "
      f"inputs_pinned={report['inputs_pinned']})")
PY

echo "[srcfrontier] OK — every probe verdict and every pinned fragment holds."
