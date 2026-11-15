#!/usr/bin/env bash
# coind_full_green.sh — regenerate the clean-coind FULL-SURFACE green artifact
# (reports/coind-full-green.json).
#
# Gate for the Brick-4 flagship corpus of the rank-1 full gfp lowering
# (data/graduation/clean-coind/proof/CoindFull.lean, brick ladder of
# designs/2026-08-25-rank1-full-gfp-lowering.md): every predicate declared
# through the real `coinductive` surface (multi-constructor ⋁, ∃ binders,
# index equations), flagship `CoLe_trans` by Park coinduction on the
# composition candidate. Four checks, all fail-closed, mirroring
# scripts/coind_green.sh checks 1-4 (that gate and its 43/26 pins are
# untouched — this is a SIBLING artifact):
#
#   1. `clean check --prelude builtin` accepts proof/CoindFull.lean
#      (exactly the pinned declaration count — surface-generated companions
#      included — 0 failed, 0 sorry).
#   2. `clean export-cert` exports exactly the pinned theorem count
#      (source theorems + generated companion theorems) with
#      all_axiom_closures_foundational_only = true and empty
#      non-foundational/trust-marker lists per declaration; the flagship
#      set (CoLe_trans, CoLe_refl, CoLe_inf, CoLe_one_zero_absurd,
#      Div_loop, Div_stuck_absurd, Cycle_zero, Cycle_two_absurd,
#      InfDesc_zero_absurd) must be present by name.
#   3. `clean kernel cert verify` independently replays the .cleancert
#      bundle (replay.json parsed: all_passed true, passed == exported).
#   4. ANTI-TRIVIALITY: `clean check --json` on
#      proof/coind_full_must_fail.lean must reject EXACTLY 2 declarations —
#      `cole_one_zero_MUST_FAIL` (a `CoLe one zero` assertion: the `z`
#      intro demands `1 = 0`) and `cole_rec_exists_MUST_FAIL` (`CoLe.rec`,
#      an induction principle, must NOT exist) — while every duplicated
#      definition and the generated `CoLe` family still check; the
#      duplicated declarations must be byte-identical to CoindFull.lean.
#
# Provenance: by default refuses to run on untracked/dirty gate inputs; the
# artifact records the commit sha plus sha256 of the source, the probe, and
# the binary. `--pre-commit` runs anyway but stamps the report's provenance
# block "pre-commit" with the offending paths listed — for the integration
# window before the inputs land on a commit. Re-run without the flag after
# committing to mint the tracked-clean artifact.
#
# Usage: scripts/coind_full_green.sh [--bin path/to/clean] [--pre-commit]
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BIN="${REPO_ROOT}/target/release/clean"
PRE_COMMIT=0
while [[ $# -gt 0 ]]; do
  case "$1" in
    --bin) BIN="${2:?--bin requires a path argument}"; shift 2 ;;
    --pre-commit) PRE_COMMIT=1; shift ;;
    *) echo "[coind-full-green] FAIL: unknown argument: $1" >&2; exit 1 ;;
  esac
done
if [[ ! -x "$BIN" ]]; then
  echo "[coind-full-green] building clean (release)..." >&2
  (cd "$REPO_ROOT" && targo --unverified build --locked --release -p clean)
fi
[[ -x "$BIN" ]] || { echo "[coind-full-green] FAIL: no executable clean binary at $BIN" >&2; exit 1; }

PROOF_DIR="${REPO_ROOT}/data/graduation/clean-coind/proof"
OUT_JSON="${REPO_ROOT}/reports/coind-full-green.json"

# Exact pins — measured against the landed CoindFull.lean (re-measure and
# re-pin if the corpus extends):
#   EXPECTED_DECLS: `clean check --json` success_count — every declaration
#     the check path registers, INCLUDING the surface-generated companion
#     families (P, P.F, P.coind, P.F_mono, P.unfold, P.fold, P.acc,
#     P.coind_upto, intros, P.cases).
#   EXPECTED_THMS: export-cert `exported` — source theorems plus the
#     generated companion THEOREMS
#     (coind/F_mono/unfold/fold/acc/coind_upto/intros/cases).
#   PROBE pins: the must-fail file's success/failed split.
#   Measured 2026-08-26 (paco parameterized-tower rung: every coinductive
#   declaration gained the 8-companion `P.paco` tower — paco def +
#   paco_coind/paco_unfold/paco_fold/paco_mon/paco_bot/le_paco/paco_acc —
#   and the corpus gained the two tower theorems CoLe_one_inf_paco /
#   Cycle_zero_paco): 146 = the declaration-parameters rung's 96 + 6
#   coinductive families x 8 tower companions + the 2 rung theorems;
#   118 = the previous 74 + 6 x 7 tower THEOREMS (paco itself is a def) +
#   the 2 rung theorems; probe: 24 = 5 duplicated defs + the now
#   19-declaration CoLe family. (Pre-rung history: 96/74/16 after the
#   declaration-parameters rung; 84/64/16 after the guarded-premise rung;
#   70/54/16 after paco/accumulation; 60/44/14 before it.)
EXPECTED_DECLS="146"
EXPECTED_THMS="118"
PROBE_EXPECTED_SUCCESS="24"

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

# Provenance: every gate input must be tracked and clean, or the commit pin
# lies. `--pre-commit` converts the refusal into an honest record: the
# report's provenance block carries mode "pre-commit" plus every path that
# is not tracked-clean, so the artifact never claims a pin it does not have.
GATE_INPUTS=(
  "data/graduation/clean-coind/proof/CoindFull.lean"
  "data/graduation/clean-coind/proof/coind_full_must_fail.lean"
  "data/graduation/clean-coind/proof/source_full.json"
  "scripts/coind_full_green.sh"
)
NOT_TRACKED_CLEAN=()
for f in "${GATE_INPUTS[@]}"; do
  git -C "$REPO_ROOT" ls-files --error-unmatch "$f" > /dev/null 2>&1 \
    || NOT_TRACKED_CLEAN+=("untracked: $f")
done
DIRTY="$(git -C "$REPO_ROOT" status --porcelain -- "${GATE_INPUTS[@]}")"
while IFS= read -r ln; do
  [[ -n "$ln" && "$ln" != '??'* ]] && NOT_TRACKED_CLEAN+=("dirty: ${ln#???}")
done <<< "$DIRTY"
PROVENANCE_MODE="tracked-clean"
if [[ ${#NOT_TRACKED_CLEAN[@]} -gt 0 ]]; then
  if [[ "$PRE_COMMIT" == 1 ]]; then
    PROVENANCE_MODE="pre-commit"
    printf '[coind-full-green] WARN: pre-commit provenance (recorded in the report):\n' >&2
    printf '  %s\n' "${NOT_TRACKED_CLEAN[@]}" >&2
  else
    echo "[coind-full-green] FAIL: gate inputs not tracked-clean (commit them first — the pin must be honest," >&2
    echo "or pass --pre-commit to mint an explicitly pre-commit-stamped artifact):" >&2
    printf '  %s\n' "${NOT_TRACKED_CLEAN[@]}" >&2
    exit 1
  fi
fi

# 1. Elaborate + kernel-check the corpus (exact counts, PYTHONOPTIMIZE-proof checks).
"$BIN" check "${PROOF_DIR}/CoindFull.lean" --prelude builtin --json > "${WORK}/check.json"
python3 - "${WORK}/check.json" "$EXPECTED_DECLS" <<'PY'
import json, sys
j = json.load(open(sys.argv[1])); pin = int(sys.argv[2])
def need(cond, msg):
    if not cond:
        raise SystemExit(f"[coind-full-green] FAIL: {msg}: {j}")
need(j["status"] == "pass", "check status")
need(j["success_count"] == pin and j["failed_count"] == 0,
     f"expected exactly {pin}/{pin} declarations")
need(j["trust_summary"]["sorry_axioms"] == 0, "sorry leaked")
PY

# 2. Export certificates; exact theorem count, flagship names, foundational-only
#    closures, no trust markers.
"$BIN" export-cert "${PROOF_DIR}/CoindFull.lean" \
  --out "${WORK}/coind_full.cleancert" --json-report "${WORK}/cert_report.json" >&2
python3 - "${WORK}/cert_report.json" "$EXPECTED_THMS" <<'PY'
import json, sys
j = json.load(open(sys.argv[1])); pin = int(sys.argv[2])
def need(cond, msg):
    if not cond:
        raise SystemExit(f"[coind-full-green] FAIL: {msg}")
need(j["all_axiom_closures_foundational_only"] is True, "non-foundational axiom leaked")
bad = [d for d in j["per_decl_axiom_closure"]
       if d["non_foundational_axioms"] or d["trust_markers"]]
need(not bad, f"non-empty closures: {bad}")
need(j["exported"] == pin, f"expected exactly {pin} theorems, got {j['exported']}")
for name in ("CoLe_trans", "CoLe_refl", "CoLe_inf", "CoLe_one_zero_absurd",
             "Div_loop", "Div_stuck_absurd", "Cycle_zero", "Cycle_two_absurd",
             "InfDesc_zero_absurd",
             # the paco/accumulation rung: its two corpus theorems
             "CoLe_one_inf_acc", "Div_loop_upto",
             # the guarded-premise rung ("P under ∀/→"): the weak-bisim
             # flagship pair, and the guarded family's own F_mono
             "WBisim_refl", "WBisim_loop_stuck_absurd", "WBisim.F_mono",
             # the declaration-parameters rung: Park instantiating the
             # parameter, a concrete-instantiation refutation, and the
             # param-threaded F_mono of the parametric family
             "Congr_refl", "Congr_id_one_zero_absurd", "Congr.F_mono",
             # the paco parameterized-tower rung: its two corpus theorems
             # (tower entry + two-level accumulation)
             "CoLe_one_inf_paco", "Cycle_zero_paco",
             # the generated companions certify too — spot-pin one full family
             "CoLe.coind", "CoLe.cases", "CoLe.z", "CoLe.s",
             "CoLe.unfold", "CoLe.fold", "CoLe.F_mono",
             "CoLe.acc", "CoLe.coind_upto",
             # ... including the full paco tower of that family (paco itself
             # is a def, so it exports no theorem)
             "CoLe.paco_coind", "CoLe.paco_unfold", "CoLe.paco_fold",
             "CoLe.paco_mon", "CoLe.paco_bot", "CoLe.le_paco",
             "CoLe.paco_acc"):
    need(name in j["exported_theorems"], f"required theorem missing: {name}")
PY

# 3. Independent kernel replay of the bundle; parse the result, don't trust exit alone.
"$BIN" kernel cert verify "${WORK}/coind_full.cleancert" --json > "${WORK}/replay.json" \
  || { echo "[coind-full-green] FAIL: cleancert replay rejected" >&2; exit 1; }
python3 - "${WORK}/replay.json" "${WORK}/cert_report.json" <<'PY'
import json, sys
r = json.load(open(sys.argv[1]))
c = json.load(open(sys.argv[2]))
def need(cond, msg):
    if not cond:
        raise SystemExit(f"[coind-full-green] FAIL: {msg}: {r}")
need(r.get("all_passed") is True, "replay all_passed is not true")
need(r.get("passed") == c["exported"], "replayed count != exported count")
PY

# 4. Anti-triviality: EXACTLY the two MUST_FAIL declarations are rejected.
"$BIN" check "${PROOF_DIR}/coind_full_must_fail.lean" --prelude builtin --json \
  > "${WORK}/antitriv.json" 2> "${WORK}/antitriv.stderr" || true
python3 - "${WORK}/antitriv.json" "$PROBE_EXPECTED_SUCCESS" <<'PY'
import json, sys
j = json.load(open(sys.argv[1])); ok_pin = int(sys.argv[2])
def need(cond, msg):
    if not cond:
        raise SystemExit(f"[coind-full-green] FAIL: anti-triviality probe: {msg}: {j}")
need(j["success_count"] == ok_pin,
     f"the duplicated defs + generated CoLe family must all check ({ok_pin})")
need(j["failed_count"] == 2, "exactly the two MUST_FAIL declarations must fail")
errs = json.dumps(j.get("errors", [])) + json.dumps(j.get("proof_state_feedback", []))
need("cole_one_zero_MUST_FAIL" in errs,
     "the `CoLe one zero` assertion must be among the failures")
need("cole_rec_exists_MUST_FAIL" in errs,
     "the `CoLe.rec` probe must be among the failures (no induction principle)")
PY
# The probe duplicates the carrier defs AND the coinductive declaration from
# CoindFull.lean; they must stay byte-identical so definition drift cannot
# vacuate the certification.
python3 - "${PROOF_DIR}/CoindFull.lean" "${PROOF_DIR}/coind_full_must_fail.lean" <<'PY'
import sys, re
core = open(sys.argv[1]).read()
probe = open(sys.argv[2]).read()
for kind, name in (("def", "CN"), ("def", "pred"), ("def", "inf"),
                   ("def", "zero"), ("def", "one"), ("coinductive", "CoLe")):
    m = re.search(rf"^{kind} {re.escape(name)} .*?(?=\n\n)", probe, re.S | re.M)
    if not m:
        raise SystemExit(f"[coind-full-green] FAIL: probe {kind} {name} not found")
    if m.group(0) not in core:
        raise SystemExit(f"[coind-full-green] FAIL: probe {kind} {name} drifted from CoindFull.lean")
PY

# Assemble the commit-pinned, measurement-derived green artifact.
GIT_SHA="$(git -C "$REPO_ROOT" rev-parse HEAD)"
NOT_TRACKED_CLEAN_JOINED=""
if [[ ${#NOT_TRACKED_CLEAN[@]} -gt 0 ]]; then
  NOT_TRACKED_CLEAN_JOINED="$(printf '%s\n' "${NOT_TRACKED_CLEAN[@]}")"
fi
python3 - "$OUT_JSON" "$WORK" "$GIT_SHA" "$PROOF_DIR" "$BIN" "$PROVENANCE_MODE" \
  "$NOT_TRACKED_CLEAN_JOINED" <<'PY'
import json, sys, hashlib
out, work, sha, proof_dir, bin_path, prov_mode, prov_paths = sys.argv[1:8]
cert = json.load(open(f"{work}/cert_report.json"))
check = json.load(open(f"{work}/check.json"))
replay = json.load(open(f"{work}/replay.json"))
def sha256(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()
report = {
    "schema": "coind-full-green-v1",
    "project": "clean-coind",
    "commit": sha,
    "provenance": {
        "mode": prov_mode,
        "not_tracked_clean": [p for p in prov_paths.split("\n") if p],
        "note": "tracked-clean: commit sha pins every gate input; pre-commit: "
                "one or more inputs were untracked/dirty at mint time and the "
                "sha256 pins below are the provenance; re-run the gate after "
                "committing to mint the tracked-clean artifact",
    },
    "inputs": {
        "source": {"path": "data/graduation/clean-coind/proof/CoindFull.lean",
                   "sha256": sha256(f"{proof_dir}/CoindFull.lean")},
        "anti_triviality_probe": {
            "path": "data/graduation/clean-coind/proof/coind_full_must_fail.lean",
            "sha256": sha256(f"{proof_dir}/coind_full_must_fail.lean")},
        "clean_binary": {"path": bin_path, "sha256": sha256(bin_path)},
    },
    "declarations_checked": check["success_count"],
    "theorems_exported": cert["exported"],
    "exported_theorems": cert["exported_theorems"],
    "axiom_closure": {
        "all_foundational_only": cert["all_axiom_closures_foundational_only"],
        "non_foundational_axioms": sorted({a for d in cert["per_decl_axiom_closure"]
                                           for a in d["non_foundational_axioms"]}),
        "note": "measured: closure ⊆ {propext, Quot.sound, Classical.choice} for every "
                "theorem (export-cert reports non-foundational axioms only; full-closure "
                "emptiness is not machine-reported — see the descriptor)",
    },
    "cleancert_replay": {"all_passed": replay.get("all_passed"),
                          "passed": replay.get("passed")},
    "anti_triviality": {
        "probe": "data/graduation/clean-coind/proof/coind_full_must_fail.lean",
        "result": "duplicated defs + generated CoLe family passed; EXACTLY "
                  "cole_one_zero_MUST_FAIL and cole_rec_exists_MUST_FAIL rejected "
                  "(asserted via --json)",
        "note": "CoLe one zero is refused (and refuted in-corpus by "
                "CoLe_one_zero_absurd, foundational-only); CoLe.rec does not exist "
                "— the surface minted a greatest fixpoint, not an inductive",
    },
    "gate_command": "scripts/coind_full_green.sh",
}
json.dump(report, open(out, "w"), indent=2, ensure_ascii=False)
print(f"[coind-full-green] GREEN — wrote {out}")
PY
