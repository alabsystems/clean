#!/usr/bin/env bash
# streams_green.sh — regenerate the clean-streams green artifact (reports/streams-green.json).
#
# Gate for the traffic-light protocol stepper demo
# (data/graduation/clean-streams/): a three-state cycle carried by an honestly
# non-terminating codata stream, implemented twice with genuinely different
# computation — stepCase (case analysis) and stepMod (modular arithmetic) —
# and joined by a coinductive bisimulation proof. Three legs, all fail-closed:
#
#   1. PROOF LEG: `clean check --prelude builtin` accepts proof/Streams.lean
#      (0 failed, 0 sorry, every declaration passes), the source carries the
#      required declarations (codata CycleStr, both steps, both codefs, a
#      Bisim theorem over cycleCase/cycleMod), and the two step definitions
#      are BYTE-IDENTICAL to the pinned program text below — so the extracted
#      object cannot drift from the proved one.
#   2. EXTRACTION LEG: `clean extract` on stepMod (C + Rust backends) and
#      stepCase (Rust backend) must each report a PASSED differential in
#      manifest.json — every battery point agrees with kernel-side evaluation.
#      stepCase on the C backend is ATTEMPTED and its verdict recorded: the
#      L5CNF lowering currently refuses the three-arm match's beta-redex
#      (`Application head: Lam`); only that documented refusal is tolerated,
#      and a PASS upgrades the record. Any other failure trips the gate.
#   3. THE JOIN: the two extracted Rust artifacts are compiled together and
#      RUN: stepCase(i) == stepMod(i) for i in {0,1,2} AND
#      stepCase(7) != stepMod(7). The agreement on reachable states and the
#      disagreement outside them are BOTH the claim — the second proves the
#      bisimulation is about the invariant, not accidental equality.
#
# Provenance: by default refuses to run on untracked/dirty gate inputs; the
# artifact records the commit sha plus sha256 of the source, the probe, and the
# binary. `--pre-commit` runs anyway but stamps the report's provenance block
# "pre-commit" with the offending paths listed — for the integration window
# before the inputs land on a commit. Re-run without the flag after committing
# to mint the tracked-clean artifact.
#
# Usage: scripts/streams_green.sh [--bin path/to/clean] [--pre-commit]
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BIN="${REPO_ROOT}/target/release/clean"
PRE_COMMIT=0
while [[ $# -gt 0 ]]; do
  case "$1" in
    --bin) BIN="${2:?--bin requires a path argument}"; shift 2 ;;
    --pre-commit) PRE_COMMIT=1; shift ;;
    *) echo "[streams-green] FAIL: unknown argument: $1" >&2; exit 1 ;;
  esac
done
[[ -x "$BIN" ]] || { echo "[streams-green] FAIL: no executable clean binary at $BIN" >&2; exit 1; }

# The Trust compiler: `clean extract --backend rust` compiles its battery only
# with an ADMITTED Trust compiler (crates/clean-elab/src/oracle_compiler.rs) —
# the `trustc` beside the running `clean`, else the absolute path in
# CLEAN_NATIVE_DECIDE_TRUSTC — and refuses with E_RUST_TOOLCHAIN otherwise; a
# workspace `target/release/clean` has no `trustc` beside it. Name the
# toolchain's compiler binary itself (a PATH `trustc` may be a shim script,
# which is never admitted); `clean` refuses anything that is not Trust's. The
# join below compiles with the same compiler.
TRUSTC="${CLEAN_NATIVE_DECIDE_TRUSTC:-}"
if [[ -z "$TRUSTC" ]]; then
  SYSROOT="$(trustc --print sysroot 2>/dev/null)" \
    || { echo "[streams-green] FAIL: no trustc to name (set CLEAN_NATIVE_DECIDE_TRUSTC)" >&2; exit 1; }
  TRUSTC="${SYSROOT}/bin/trustc"
fi
[[ -x "$TRUSTC" ]] || { echo "[streams-green] FAIL: no executable Trust compiler at $TRUSTC" >&2; exit 1; }
export CLEAN_NATIVE_DECIDE_TRUSTC="$TRUSTC"

PROOF_DIR="${REPO_ROOT}/data/graduation/clean-streams/proof"
SRC="${PROOF_DIR}/Streams.lean"
OUT_JSON="${REPO_ROOT}/reports/streams-green.json"

# Exact declaration count pin — measured 2026-08-24 against the proof lane's
# Streams.lean (56/56, 0 failed, 0 sorry — 53 at mint + the `Bisim.cases`
# inversion companion the coinductive surface began generating with the
# rank-1 Brick 1 landing, 2026-08-26, + the `Bisim.acc` / `Bisim.coind_upto`
# companions of the paco/accumulation rung, 2026-08-26; 64 since the paco
# parameterized-tower rung grew every coinductive family by the 8-companion
# `Bisim.paco` tower, 2026-08-26; 80 since b452e97c8, 2026-09-25, made every
# codata/codef command return the declarations it registers instead of
# `Skipped`, so `clean check` now checks and counts `codata CycleStr`'s 14
# generated declarations and the two codefs `cycleCase`/`cycleMod`, which it
# used to kernel-check without reporting -- 64 + 16, re-measured 2026-10-16 at
# e2fa3dbaf, every one passing). If the proof lane
# extends the file, re-measure and re-pin:
#   target/release/clean check data/graduation/clean-streams/proof/Streams.lean \
#     --prelude builtin --json | python3 -c 'import json,sys; print(json.load(sys.stdin)["success_count"])'
# (Empty = structural mode: all declarations must pass, none may fail, plus the
# required-name checks below.)
EXPECTED_DECLS="80"

# The proof lane owns Streams.lean and is building it concurrently; this gate
# exists from day one and simply fails until the file lands.
[[ -f "$SRC" ]] || {
  echo "[streams-green] FAIL: ${SRC#"$REPO_ROOT"/} does not exist yet (the proof lane owns it)" >&2
  exit 1
}

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

# Provenance: every gate input must be tracked and clean, or the commit pin
# lies. `--pre-commit` converts the refusal into an honest record: the report's
# provenance block carries mode "pre-commit" plus every path that is not
# tracked-clean, so the artifact never claims a commit pin it does not have.
GATE_INPUTS=(
  "data/graduation/clean-streams/proof/Streams.lean"
  "scripts/streams_green.sh"
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
    printf '[streams-green] WARN: pre-commit provenance (recorded in the report):\n' >&2
    printf '  %s\n' "${NOT_TRACKED_CLEAN[@]}" >&2
  else
    echo "[streams-green] FAIL: gate inputs not tracked-clean (commit them first — the pin must be honest," >&2
    echo "or pass --pre-commit to mint an explicitly pre-commit-stamped artifact):" >&2
    printf '  %s\n' "${NOT_TRACKED_CLEAN[@]}" >&2
    exit 1
  fi
fi

# ── 1. PROOF LEG ─────────────────────────────────────────────────────────────
"$BIN" check "$SRC" --prelude builtin --json > "${WORK}/check.json"
python3 - "${WORK}/check.json" "$EXPECTED_DECLS" <<'PY'
import json, sys
j = json.load(open(sys.argv[1])); pin = sys.argv[2]
def need(cond, msg):
    if not cond:
        raise SystemExit(f"[streams-green] FAIL: {msg}: {j}")
need(j["status"] == "pass", "check status")
need(j["failed_count"] == 0, "declarations failed")
need(j["success_count"] == j["decl_count"], "not every declaration passed")
need(j["trust_summary"]["sorry_axioms"] == 0, "sorry leaked")
if pin:
    need(j["success_count"] == int(pin),
         f"expected exactly {pin}/{pin} declarations (pinned)")
PY

# Required declarations + the byte-identity pin of the two step definitions.
# The program is FIXED: the extraction probe below carries EXACTLY this text,
# and it must appear verbatim in Streams.lean, so the differential-checked
# artifact and the proved definition are the same object.
cat > "${WORK}/steps.lean" <<'LEAN'
def stepCase (i : Nat) : Nat :=
  match i with
  | 0 => 1
  | 1 => 2
  | _ => 0

def stepMod (i : Nat) : Nat := Nat.mod (Nat.add i 1) 3
LEAN
python3 - "$SRC" "${WORK}/steps.lean" <<'PY'
import sys
core = open(sys.argv[1]).read()
probe = open(sys.argv[2]).read()
for block in probe.strip().split("\n\n"):
    if block not in core:
        raise SystemExit(
            "[streams-green] FAIL: pinned step definition drifted from Streams.lean "
            f"(the proved and extracted objects must be byte-identical):\n{block}")
for needle in ("codata CycleStr", "codef cycleCase", "codef cycleMod"):
    if needle not in core:
        raise SystemExit(f"[streams-green] FAIL: required declaration missing: {needle}")
if "theorem" not in core or "Bisim" not in core:
    raise SystemExit("[streams-green] FAIL: no Bisim theorem found in Streams.lean")
if not any("cycleCase" in ln and "cycleMod" in ln for ln in core.splitlines()):
    raise SystemExit(
        "[streams-green] FAIL: no line relates cycleCase to cycleMod — the join "
        "theorem must connect the two implementations")
PY

# ── 2. EXTRACTION LEG ────────────────────────────────────────────────────────
# Extraction runs on the byte-identity-pinned probe rather than Streams.lean
# itself: `clean extract` elaborates the WHOLE file, and the codata/codef
# surface needs the builtin prelude that `extract` does not take; the pin
# above is what makes the probe honest.
require_extract() { # decl backend
  local decl="$1" backend="$2" out="${WORK}/x-${2}-${1}"
  "$BIN" extract "${WORK}/steps.lean" --decl "$decl" --out "$out" --backend "$backend" \
    > "${WORK}/extract-${backend}-${decl}.log" 2>&1 \
    || { echo "[streams-green] FAIL: extract $decl --backend $backend:" >&2
         tail -3 "${WORK}/extract-${backend}-${decl}.log" >&2; exit 1; }
  python3 - "${out}/manifest.json" "$decl" "$backend" <<'PY'
import json, sys
m = json.load(open(sys.argv[1]))
d = m.get("differential", "")
if not d.startswith("PASSED"):
    raise SystemExit(
        f"[streams-green] FAIL: {sys.argv[2]} --backend {sys.argv[3]}: "
        f"manifest differential is not PASSED: {d!r}")
PY
}
require_extract stepMod c
require_extract stepMod rust
require_extract stepCase rust

# stepCase on the C lane: attempt, record. The ONLY tolerated failure is the
# documented L5CNF beta-redex refusal; anything else trips the gate.
if "$BIN" extract "${WORK}/steps.lean" --decl stepCase --out "${WORK}/x-c-stepCase" --backend c \
    > "${WORK}/extract-c-stepCase.log" 2>&1; then
  python3 - "${WORK}/x-c-stepCase/manifest.json" <<'PY'
import json, sys
m = json.load(open(sys.argv[1]))
if not m.get("differential", "").startswith("PASSED"):
    raise SystemExit("[streams-green] FAIL: stepCase --backend c wrote a manifest "
                     f"without a PASSED differential: {m}")
PY
  STEPCASE_C_VERDICT="PASSED"
else
  grep -q "Application head: Lam" "${WORK}/extract-c-stepCase.log" || {
    echo "[streams-green] FAIL: stepCase --backend c failed with something OTHER than" >&2
    echo "the documented L5CNF beta-redex refusal:" >&2
    tail -3 "${WORK}/extract-c-stepCase.log" >&2
    exit 1
  }
  STEPCASE_C_VERDICT="REFUSED (known L5CNF lowering gap: three-arm match elaborates a beta-redex default arm, 'Application head: Lam'; the Rust lane carries the differential)"
fi

# ── 3. THE JOIN ──────────────────────────────────────────────────────────────
# Compile the two extracted Rust artifacts TOGETHER and run them: agreement on
# the reachable states {0,1,2}, disagreement at 7. The artifacts under test
# are the exact bytes the differential passed on — copied, never regenerated.
JOIN="${WORK}/join"
mkdir -p "$JOIN"
cp "${WORK}/x-rust-stepCase/stepCase.rs" "${WORK}/x-rust-stepMod/stepMod.rs" "$JOIN/"
cat > "${JOIN}/join.rs" <<'RS'
#[path = "stepCase.rs"]
mod sc;
#[path = "stepMod.rs"]
mod sm;

fn main() {
    let points: Vec<(u64, u64, u64)> = [0u64, 1, 2, 7]
        .iter()
        .map(|&i| (i, sc::stepCase(i), sm::stepMod(i)))
        .collect();
    for &(i, a, b) in &points[..3] {
        if a != b {
            eprintln!("JOIN FAIL: stepCase({i})={a} != stepMod({i})={b} on a reachable state");
            std::process::exit(1);
        }
    }
    let (_, a7, b7) = points[3];
    if a7 == b7 {
        eprintln!(
            "JOIN FAIL: stepCase(7)={a7} == stepMod(7)={b7} — the two steps must \
             genuinely differ outside the invariant, or the bisimulation is vacuous"
        );
        std::process::exit(1);
    }
    for &(i, a, b) in &points {
        println!("{i} {a} {b}");
    }
}
RS
# Compiled with the Trust compiler resolved above (owner directive
# 2026-09-28). This program is a differential oracle, not a verification
# target, so it is compiled with the verifier opt-out; there is no plain-rustc
# fallback.
"$TRUSTC" --edition=2021 -O -Ztrust-verify=off "${JOIN}/join.rs" -o "${JOIN}/join" \
    > "${WORK}/join_rustc.log" 2>&1 \
  || { echo "[streams-green] FAIL: join driver failed to compile with trustc:" >&2
       tail -5 "${WORK}/join_rustc.log" >&2; exit 1; }
"${JOIN}/join" > "${WORK}/join.out" \
  || { echo "[streams-green] FAIL: join check rejected (see values above)" >&2; exit 1; }

# ── 4. The commit-pinned, measurement-derived green artifact ────────────────
GIT_SHA="$(git -C "$REPO_ROOT" rev-parse HEAD)"
NTC_JOINED=""
if [[ ${#NOT_TRACKED_CLEAN[@]} -gt 0 ]]; then
  NTC_JOINED="$(printf '%s\n' "${NOT_TRACKED_CLEAN[@]}")"
fi
mkdir -p "${REPO_ROOT}/reports"
python3 - "$OUT_JSON" "$WORK" "$GIT_SHA" "$SRC" "$BIN" "$STEPCASE_C_VERDICT" \
  "$PROVENANCE_MODE" "$NTC_JOINED" <<'PY'
import hashlib, json, re, sys
out, work, sha, src, bin_path, stepcase_c, prov_mode, ntc = sys.argv[1:9]
check = json.load(open(f"{work}/check.json"))
def sha256(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()
theorems = re.findall(r"^theorem\s+([A-Za-z0-9_.']+)", open(src).read(), re.M)
join_points = [tuple(int(v) for v in ln.split())
               for ln in open(f"{work}/join.out").read().splitlines() if ln.strip()]
report = {
    "schema": "streams-green-v1",
    "project": "clean-streams",
    "commit": sha,
    "provenance": {
        "mode": prov_mode,
        "not_tracked_clean": [ln for ln in ntc.splitlines() if ln.strip()],
        "note": "tracked-clean: commit sha pins every gate input; pre-commit: "
                "inputs listed above were not on the commit at mint time — the "
                "sha256 pins below are the provenance; re-run the gate after "
                "committing to mint the tracked-clean artifact",
    },
    "inputs": {
        "source": {"path": "data/graduation/clean-streams/proof/Streams.lean",
                   "sha256": sha256(src)},
        "extraction_probe": {
            "path": "(generated per run; byte-identity-pinned to the source)",
            "sha256": sha256(f"{work}/steps.lean")},
        "clean_binary": {"path": bin_path, "sha256": sha256(bin_path)},
    },
    "declarations_checked": check["success_count"],
    "theorems": theorems,
    "differential": {
        "stepMod_c": "PASSED",
        "stepMod_rust": "PASSED",
        "stepCase_rust": "PASSED",
        "stepCase_c": stepcase_c,
        "claim": "differential check over the recorded battery per artifact; "
                 "NOT a proof of translation correctness "
                 "(designs/2026-08-06-clean-extract-width1.md)",
    },
    "join_check": {
        "points": [{"i": i, "stepCase": a, "stepMod": b} for i, a, b in join_points],
        "agreement_on": [0, 1, 2],
        "disagreement_at": 7,
        "note": "the two steps agree exactly on the reachable states and differ at "
                "7 — the bisimulation holds on the invariant, not everywhere, and "
                "that asymmetry is the demo's content",
    },
    "gate_command": "scripts/streams_green.sh",
}
json.dump(report, open(out, "w"), indent=2)
print(f"[streams-green] GREEN — wrote {out}")
PY
