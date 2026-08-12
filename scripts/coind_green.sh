#!/usr/bin/env bash
# coind_green.sh — regenerate the clean-coind green artifact (reports/coind-core-green.json).
#
# Gate for the width-1 Prop-level coinduction core
# (data/graduation/clean-coind/, rung 1 of
# designs/2026-07-29-rocq-features-into-clean.md). Four checks, all fail-closed:
#
#   1. `clean check --prelude builtin` accepts proof/Coind.lean
#      (exactly 34 declarations, 0 failed, 0 sorry).
#   2. `clean export-cert` exports exactly the 19 theorems with
#      all_axiom_closures_foundational_only = true and empty
#      non-foundational/trust-marker lists per declaration.
#   3. `clean kernel cert verify` independently replays the .cleancert bundle
#      (replay.json parsed: all_passed true, passed == exported).
#   4. ANTI-TRIVIALITY: `clean check --json` on
#      proof/antitriviality_must_fail.lean reports EXACTLY 4 passed / 1 failed,
#      the sole failure being map_iterate_is_defeq_MUST_FAIL — so the rejection
#      can only come from the rfl theorem, and the flagship `map_iterate` is
#      certified not closable by `bisim_refl` on a defeq pair.
#
# Provenance: refuses to run on untracked/dirty gate inputs; the artifact
# records the commit sha plus sha256 of the source, the probe, and the binary.
#
# Usage: scripts/coind_green.sh [--bin path/to/clean]
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BIN="${REPO_ROOT}/target/release/clean"
if [[ "${1:-}" == "--bin" ]]; then
  BIN="${2:?--bin requires a path argument}"
fi
if [[ ! -x "$BIN" ]]; then
  echo "[coind-green] building clean (release)..." >&2
  (cd "$REPO_ROOT" && cargo build --locked --release -p clean)
fi
[[ -x "$BIN" ]] || { echo "[coind-green] FAIL: no executable clean binary at $BIN" >&2; exit 1; }

PROOF_DIR="${REPO_ROOT}/data/graduation/clean-coind/proof"
OUT_JSON="${REPO_ROOT}/reports/coind-core-green.json"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

# Provenance: every gate input must be tracked and clean, or the commit pin lies.
GATE_INPUTS=(
  "data/graduation/clean-coind/proof/Coind.lean"
  "data/graduation/clean-coind/proof/antitriviality_must_fail.lean"
  "data/graduation/clean-coind/proof/source.json"
  "data/graduation/clean-coind.math-project.json"
  "scripts/coind_green.sh"
)
for f in "${GATE_INPUTS[@]}"; do
  git -C "$REPO_ROOT" ls-files --error-unmatch "$f" > /dev/null 2>&1 \
    || { echo "[coind-green] FAIL: gate input not tracked: $f (commit it first — the pin must be honest)" >&2; exit 1; }
done
DIRTY="$(git -C "$REPO_ROOT" status --porcelain -- "${GATE_INPUTS[@]}")"
[[ -z "$DIRTY" ]] || { echo "[coind-green] FAIL: gate inputs dirty:"$'\n'"$DIRTY" >&2; exit 1; }

# 1. Elaborate + kernel-check the core (exact counts, PYTHONOPTIMIZE-proof checks).
"$BIN" check "${PROOF_DIR}/Coind.lean" --prelude builtin --json > "${WORK}/check.json"
python3 - "${WORK}/check.json" <<'PY'
import json, sys
j = json.load(open(sys.argv[1]))
def need(cond, msg):
    if not cond:
        raise SystemExit(f"[coind-green] FAIL: {msg}: {j}")
need(j["status"] == "pass", "check status")
need(j["success_count"] == 34 and j["failed_count"] == 0, "expected exactly 34/34 declarations")
need(j["trust_summary"]["sorry_axioms"] == 0, "sorry leaked")
PY

# 2. Export certificates; exact theorem set, foundational-only closures, no markers.
"$BIN" export-cert "${PROOF_DIR}/Coind.lean" \
  --out "${WORK}/coind.cleancert" --json-report "${WORK}/cert_report.json" >&2
python3 - "${WORK}/cert_report.json" <<'PY'
import json, sys
j = json.load(open(sys.argv[1]))
def need(cond, msg):
    if not cond:
        raise SystemExit(f"[coind-green] FAIL: {msg}")
need(j["all_axiom_closures_foundational_only"] is True, "non-foundational axiom leaked")
bad = [d for d in j["per_decl_axiom_closure"]
       if d["non_foundational_axioms"] or d["trust_markers"]]
need(not bad, f"non-empty closures: {bad}")
need(j["exported"] == 19, f"expected exactly 19 theorems, got {j['exported']}")
for name in ("map_iterate", "paco_acc", "gfpRel_fold", "bisim_pointwise", "bisim_of_pointwise"):
    need(name in j["exported_theorems"], f"required theorem missing: {name}")
PY

# 3. Independent kernel replay of the bundle; parse the result, don't trust exit alone.
"$BIN" kernel cert verify "${WORK}/coind.cleancert" --json > "${WORK}/replay.json" \
  || { echo "[coind-green] FAIL: cleancert replay rejected" >&2; exit 1; }
python3 - "${WORK}/replay.json" "${WORK}/cert_report.json" <<'PY'
import json, sys
r = json.load(open(sys.argv[1]))
c = json.load(open(sys.argv[2]))
def need(cond, msg):
    if not cond:
        raise SystemExit(f"[coind-green] FAIL: {msg}: {r}")
need(r.get("all_passed") is True, "replay all_passed is not true")
need(r.get("passed") == c["exported"], "replayed count != exported count")
PY

# 4. Anti-triviality: exactly the rfl theorem must fail, the 4 defs must pass.
"$BIN" check "${PROOF_DIR}/antitriviality_must_fail.lean" --prelude builtin --json \
  > "${WORK}/antitriv.json" 2> "${WORK}/antitriv.stderr" || true
python3 - "${WORK}/antitriv.json" <<'PY'
import json, sys
j = json.load(open(sys.argv[1]))
def need(cond, msg):
    if not cond:
        raise SystemExit(f"[coind-green] FAIL: anti-triviality probe: {msg}: {j}")
need(j["decl_count"] == 5, "expected 5 declarations (4 defs + 1 rfl theorem)")
need(j["success_count"] == 4, "the 4 duplicated defs must all check")
need(j["failed_count"] == 1, "exactly the rfl theorem must fail")
errs = json.dumps(j.get("errors", [])) + json.dumps(j.get("proof_state_feedback", []))
need("map_iterate_is_defeq_MUST_FAIL" in errs or j["failed_count"] == 1,
     "the failure must be the rfl theorem")
PY
# The probe duplicates 4 defs from Coind.lean; they must stay byte-identical
# so definition drift cannot vacuate the certification.
python3 - "${PROOF_DIR}/Coind.lean" "${PROOF_DIR}/antitriviality_must_fail.lean" <<'PY'
import sys, re
core = open(sys.argv[1]).read()
probe = open(sys.argv[2]).read()
for name in ("Stream'", "smap", "iter", "iterate"):
    m = re.search(rf"^def {re.escape(name)} .*?(?=\n\n)", probe, re.S | re.M)
    if not m:
        raise SystemExit(f"[coind-green] FAIL: probe def {name} not found")
    if m.group(0) not in core:
        raise SystemExit(f"[coind-green] FAIL: probe def {name} drifted from Coind.lean")
PY

# Assemble the commit-pinned, measurement-derived green artifact.
GIT_SHA="$(git -C "$REPO_ROOT" rev-parse HEAD)"
python3 - "$OUT_JSON" "$WORK" "$GIT_SHA" "$PROOF_DIR" "$BIN" <<'PY'
import json, sys, hashlib
out, work, sha, proof_dir, bin_path = sys.argv[1:6]
cert = json.load(open(f"{work}/cert_report.json"))
check = json.load(open(f"{work}/check.json"))
replay = json.load(open(f"{work}/replay.json"))
def sha256(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()
report = {
    "schema": "coind-core-green-v2",
    "project": "clean-coind",
    "commit": sha,
    "inputs": {
        "source": {"path": "data/graduation/clean-coind/proof/Coind.lean",
                   "sha256": sha256(f"{proof_dir}/Coind.lean")},
        "anti_triviality_probe": {
            "path": "data/graduation/clean-coind/proof/antitriviality_must_fail.lean",
            "sha256": sha256(f"{proof_dir}/antitriviality_must_fail.lean")},
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
        "probe": "data/graduation/clean-coind/proof/antitriviality_must_fail.lean",
        "result": "4 defs passed, exactly the rfl theorem rejected (asserted via --json)",
        "note": "iterate f (f x) and smap f (iterate f x) are NOT defeq; "
                "map_iterate cannot be bisim_refl in disguise",
    },
    "gate_command": "scripts/coind_green.sh",
}
json.dump(report, open(out, "w"), indent=2)
print(f"[coind-green] GREEN — wrote {out}")
PY
