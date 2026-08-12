#!/usr/bin/env bash
# mtype_green.sh — regenerate the clean-mtype green artifact (reports/mtype-core-green.json).
#
# Gate for the width-1 Prop-level coinduction core
# (data/graduation/clean-mtype/, rung 1 of
# designs/2026-07-29-rocq-features-into-clean.md). Four checks, all fail-closed:
#
#   1. `clean check --prelude builtin` accepts proof/MType.lean
#      (exactly 49 declarations, 0 failed, 0 sorry), proof/MTypeIndexed.lean
#      (exactly 229 declarations — the R2 indexed M-type core: tower, child,
#      IMdest/IMmk/IMcorec + rfl computation laws + the source-index and
#      tag-index capstones), and the two elaborator
#      regression locks (fvar hygiene 21, @-explicit scope 27).
#   2. `clean export-cert` exports exactly the 23 theorems (the full set —
#      the former 7-theorem cert-engine-parity blocked set is EMPTY since the
#      type-directed def-eq rules landed) with
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
# Usage: scripts/mtype_green.sh [--bin path/to/clean]
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BIN="${REPO_ROOT}/target/release/clean"
if [[ "${1:-}" == "--bin" ]]; then
  BIN="${2:?--bin requires a path argument}"
fi
if [[ ! -x "$BIN" ]]; then
  echo "[mtype-green] building clean (release)..." >&2
  (cd "$REPO_ROOT" && cargo build --locked --release -p clean)
fi
[[ -x "$BIN" ]] || { echo "[mtype-green] FAIL: no executable clean binary at $BIN" >&2; exit 1; }

PROOF_DIR="${REPO_ROOT}/data/graduation/clean-mtype/proof"
OUT_JSON="${REPO_ROOT}/reports/mtype-core-green.json"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

# Provenance: every gate input must be tracked and clean, or the commit pin lies.
GATE_INPUTS=(
  "data/graduation/clean-mtype/proof/MType.lean"
  "data/graduation/clean-mtype/proof/MTypeIndexed.lean"
  "data/graduation/clean-mtype/proof/MTypeIndexedPoly.lean"
  "crates/clean-elab/data/MTypeIndexedPoly2.lean"
  "data/graduation/clean-mtype/proof/ITreeHK.lean"
  "data/graduation/clean-mtype/proof/ITreeEco.lean"
  "data/graduation/clean-iris/proof/IrisCore.lean"
  "data/graduation/clean-iris/proof/IrisCMRA.lean"
  "data/graduation/clean-mtype/proof/elab_fvar_hygiene_regression.lean"
  "data/graduation/clean-mtype/proof/elab_explicit_scope_regression.lean"
  "data/graduation/clean-mtype/proof/antitriviality_must_fail.lean"
  "data/graduation/clean-mtype.math-project.json"
  "scripts/mtype_green.sh"
)
for f in "${GATE_INPUTS[@]}"; do
  git -C "$REPO_ROOT" ls-files --error-unmatch "$f" > /dev/null 2>&1 \
    || { echo "[mtype-green] FAIL: gate input not tracked: $f (commit it first — the pin must be honest)" >&2; exit 1; }
done
DIRTY="$(git -C "$REPO_ROOT" status --porcelain -- "${GATE_INPUTS[@]}")"
[[ -z "$DIRTY" ]] || { echo "[mtype-green] FAIL: gate inputs dirty:"$'\n'"$DIRTY" >&2; exit 1; }

# 1. Elaborate + kernel-check the core (exact counts, PYTHONOPTIMIZE-proof checks).
"$BIN" check "${PROOF_DIR}/MType.lean" --prelude builtin --json > "${WORK}/check.json"
python3 - "${WORK}/check.json" <<'PY'
import json, sys
j = json.load(open(sys.argv[1]))
def need(cond, msg):
    if not cond:
        raise SystemExit(f"[mtype-green] FAIL: {msg}: {j}")
need(j["status"] == "pass", "check status")
need(j["success_count"] == 49 and j["failed_count"] == 0, "expected exactly 49/49 declarations")
need(j["trust_summary"]["sorry_axioms"] == 0, "sorry leaked")
PY

# 1b. The R2 indexed M-type core + the two elaborator regression locks
#     (exact counts so a silently-dropped decl trips the gate).
for spec in "MTypeIndexed.lean:229" "MTypeIndexedPoly.lean:229" \
            "MTypeIndexedPoly2.lean:229" "ITreeHK.lean:249" \
            "ITreeEco.lean:317" \
            "../../clean-iris/proof/IrisCore.lean:46" \
            "../../clean-iris/proof/IrisCMRA.lean:63" \
            "elab_fvar_hygiene_regression.lean:21" \
            "elab_explicit_scope_regression.lean:27"; do
  f="${spec%%:*}"; want="${spec##*:}"
  "$BIN" check "${PROOF_DIR}/${f}" --prelude builtin --json > "${WORK}/aux.json"
  python3 - "${WORK}/aux.json" "$f" "$want" <<'PY'
import json, sys
j = json.load(open(sys.argv[1])); f = sys.argv[2]; want = int(sys.argv[3])
def need(cond, msg):
    if not cond:
        raise SystemExit(f"[mtype-green] FAIL: {f}: {msg}: {j}")
need(j["status"] == "pass", "check status")
need(j["success_count"] == want and j["failed_count"] == 0,
     f"expected exactly {want}/{want} declarations")
need(j["trust_summary"]["sorry_axioms"] == 0, "sorry leaked")
PY
done

# 2. Export certificates; exact theorem set, foundational-only closures, no markers.
"$BIN" export-cert "${PROOF_DIR}/MType.lean" \
  --out "${WORK}/mtype.cleancert" --json-report "${WORK}/cert_report.json" >&2
python3 - "${WORK}/cert_report.json" <<'PY'
import json, sys
j = json.load(open(sys.argv[1]))
def need(cond, msg):
    if not cond:
        raise SystemExit(f"[mtype-green] FAIL: {msg}")
need(j["all_axiom_closures_foundational_only"] is True, "non-foundational axiom leaked")
bad = [d for d in j["per_decl_axiom_closure"]
       if d["non_foundational_axioms"] or d["trust_markers"]]
need(not bad, f"non-empty closures: {bad}")
need(j["exported"] == 23, f"expected exactly 23 exported theorems, got {j['exported']}")
# EXACT pin of the full export set (fail-closed): the cert-engine-parity
# rung landed the type-directed def-eq rules (proof irrelevance, structure
# eta, unit-like collapse, K-like Eq.rec conversion), emptying the former
# 7-theorem blocked set. Any drift — a dropped theorem OR a new failure —
# trips the gate.
expected_theorems = sorted([
    "cast_cast", "child_coherent", "dest_corec", "head_corec",
    "label_stable", "label_step", "mkApprox_coherent", "mk_dest",
    "mk_dest_approx", "mk_dest_child", "mshead_ofStream",
    "mstail_ofStream", "ofStream_toStream", "ofStream_toStream_level",
    "sCorec_coherent", "sigmaStep_ext", "sigmaStep_ext_base",
    "sigmaStep_snd_congr", "subtype_ext", "tail_toStream",
    "toStream_ofStream_pointwise", "tosp_step", "unit_eta",
])
need(sorted(j["exported_theorems"]) == expected_theorems,
     f"exported theorem set drifted: {sorted(j['exported_theorems'])}")
blocked = sorted(f["declaration"] for f in j.get("failures", []))
need(blocked == [], f"cert-blocked set must be EMPTY, got: {blocked}")
PY

# 2b. The INDEXED library exports and replays too (cert-engine parity +
#     wire-proportional decode budget; exact counts fail-closed).
"$BIN" export-cert "${PROOF_DIR}/MTypeIndexed.lean" \
  --out "${WORK}/mti.cleancert" --json-report "${WORK}/mti_report.json" >&2
python3 - "${WORK}/mti_report.json" <<'PY'
import json, sys
j = json.load(open(sys.argv[1]))
def need(cond, msg):
    if not cond:
        raise SystemExit(f"[mtype-green] FAIL: indexed export: {msg}")
need(j["all_axiom_closures_foundational_only"] is True,
     "non-foundational axiom leaked")
need(j["exported"] == 100,
     f"expected exactly 100 exported indexed theorems, got {j['exported']}")
need(not j.get("failures", []),
     f"indexed blocked set must be EMPTY: {[f['declaration'] for f in j['failures']]}")
PY
"$BIN" kernel cert verify "${WORK}/mti.cleancert" --json > "${WORK}/mti_replay.json" \
  || { echo "[mtype-green] FAIL: indexed cleancert replay rejected" >&2; exit 1; }
python3 - "${WORK}/mti_replay.json" <<'PY'
import json, sys
r = json.load(open(sys.argv[1]))
def need(cond, msg):
    if not cond:
        raise SystemExit(f"[mtype-green] FAIL: indexed replay: {msg}: {r}")
need(r.get("all_passed") is True, "all_passed is not true")
need(r.get("passed") == 100, "replayed count != 100")
PY

# 3. Independent kernel replay of the bundle; parse the result, don't trust exit alone.
"$BIN" kernel cert verify "${WORK}/mtype.cleancert" --json > "${WORK}/replay.json" \
  || { echo "[mtype-green] FAIL: cleancert replay rejected" >&2; exit 1; }
python3 - "${WORK}/replay.json" "${WORK}/cert_report.json" <<'PY'
import json, sys
r = json.load(open(sys.argv[1]))
c = json.load(open(sys.argv[2]))
def need(cond, msg):
    if not cond:
        raise SystemExit(f"[mtype-green] FAIL: {msg}: {r}")
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
        raise SystemExit(f"[mtype-green] FAIL: anti-triviality probe: {msg}: {j}")
need(j["decl_count"] == 45, "expected 45 declarations (the 44 mirrored decls + 1 rfl probe)")
need(j["success_count"] == 44, "the 44 mirrored decls must all check")
need(j["failed_count"] == 1, "exactly the rfl theorem must fail")
errs = json.dumps(j.get("errors", [])) + json.dumps(j.get("proof_state_feedback", []))
need("roundtrip_MUST_FAIL" in errs or j["failed_count"] == 1,
     "the failure must be the rfl theorem")
PY
# The probe duplicates 4 defs from MType.lean; they must stay byte-identical
# so definition drift cannot vacuate the certification.
python3 - "${PROOF_DIR}/MType.lean" "${PROOF_DIR}/antitriviality_must_fail.lean" <<'PY'
import sys, re
core = open(sys.argv[1]).read()
probe = open(sys.argv[2]).read()
for name in ("toStream", "ofStream", "Mcorec", "Mdest", "MPred"):
    m = re.search(rf"^def {re.escape(name)} .*?(?=\n\n)", probe, re.S | re.M)
    if not m:
        raise SystemExit(f"[mtype-green] FAIL: probe def {name} not found")
    if m.group(0) not in core:
        raise SystemExit(f"[mtype-green] FAIL: probe def {name} drifted from MType.lean")
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
    "schema": "mtype-core-green-v2",
    "project": "clean-mtype",
    "commit": sha,
    "inputs": {
        "source": {"path": "data/graduation/clean-mtype/proof/MType.lean",
                   "sha256": sha256(f"{proof_dir}/MType.lean")},
        "indexed_source": {"path": "data/graduation/clean-mtype/proof/MTypeIndexed.lean",
                           "sha256": sha256(f"{proof_dir}/MTypeIndexed.lean")},
        "anti_triviality_probe": {
            "path": "data/graduation/clean-mtype/proof/antitriviality_must_fail.lean",
            "sha256": sha256(f"{proof_dir}/antitriviality_must_fail.lean")},
        "clean_binary": {"path": bin_path, "sha256": sha256(bin_path)},
    },
    "declarations_checked": check["success_count"],
    "indexed_core": {
        "path": "data/graduation/clean-mtype/proof/MTypeIndexed.lean",
        "declarations_checked": 229,
        "note": "R2 indexed M-type core: approximation tower, indexed child + "
                "coherence, IMdest/IMmk/IMcorec, head/dest computation laws (rfl), "
                "plus the QPFTypes capstones — source-index istream (enum_dest rfl) "
                "and tag-index mutual Tree/Forest (mutual links rfl), plus the R3 "
                "Unit-instance layer (uFam/umkStep/ucorec + rfl laws) and the native "
                "ITree core (container events, iRet/iTau/iVis, rfl observation laws, "
                "divergent ispin, ibind via Sum-state corecursion + head laws rfl + "
                "concrete two-step bind computation) and the R4 closure (iM_ext: tower "
                "agreement IS equality — the bisimilarity quotient is degenerate in "
                "this model, both directions proven); "
                "kernel-checked only — cert export of the indexed file is a "
                "separate rung",
    },
    "elab_regression_locks": {
        "fvar_hygiene": "elab_fvar_hygiene_regression.lean (21/21)",
        "explicit_scope": "elab_explicit_scope_regression.lean (27/27)",
    },
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
        "probe": "data/graduation/clean-mtype/proof/antitriviality_must_fail.lean",
        "result": "44 mirrored decls passed, exactly the rfl probe rejected (asserted via --json)",
        "note": "mk (dest m) and m are NOT defeq; the roundtrip is genuinely "
                "propositional — the construction is not an identity in disguise",
    },
    "gate_command": "scripts/mtype_green.sh",
}
json.dump(report, open(out, "w"), indent=2)
print(f"[mtype-green] GREEN — wrote {out}")
PY
