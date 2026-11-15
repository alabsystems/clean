#!/usr/bin/env bash
# srcelab_corpus_demo.sh — the CORPUS-IDENTITY teeth of scripts/source_elab_gate.sh,
# asserted directly against the gate in seconds.
#
# WHY THIS EXISTS RATHER THAN A POINTER AT THE TEST SUITE. These properties were
# first recorded as `data/gate_demonstrations.json` arms whose command was
# `bash scripts/test_source_elab_gate.sh` — the whole 58-arm suite, once per arm.
# `check_gate_registry.py --repin source_elab_gate` then ran for 50 minutes and
# was KILLED by its own timeout (RC=124) without moving the pin. A demonstration
# that cannot finish is the same defect class as a gate that cannot run, so the
# arms now drive the gate directly: a fake corpus, a fake `clean`, one gate
# invocation per property, ~2 s each.
#
# Every property is asserted POSITIVELY (the mechanism holds) and this script
# exits NON-ZERO naming the one that broke, so each registry arm can key on its
# own message. Run it bare to check all of them.
set -uo pipefail
# A fake corpus is `git init`ed and committed below. Inherited from a git hook
# or a lane committing over a temporary index, GIT_DIR / GIT_INDEX_FILE would
# point those calls at the REAL repository.
unset GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_COMMON_DIR GIT_OBJECT_DIRECTORY

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
GATE="$ROOT/scripts/source_elab_gate.sh"
RATCHET="$ROOT/data/source_elab_ratchet.json"
TMP="$(mktemp -d -t srcelab_corpus_demo.XXXXXX)"
trap 'rm -rf "$TMP"' EXIT
FAILED=0
note() { printf '  %s\n' "$1"; }
broke() { printf 'SRCELAB-CORPUS-DEMO BROKEN: %s\n' "$1" >&2; FAILED=1; }

# ---- a fake Mathlib corpus WITH AN IDENTITY -------------------------------
# Identity is (git rev, lean-toolchain). A bare directory has neither, and the
# gate refuses to arm against a corpus it cannot name, so the fixture must
# carry both or it would exercise a path the gate forbids.
ML="$TMP/mathlib"
mkdir -p "$ML/.lake/build/lib/lean" "$ML/Mathlib/Logic/Function" \
         "$ML/Mathlib/Data" "$ML/Mathlib/Order"
for f in "Mathlib/Logic/Basic.lean" "Mathlib/Logic/Function/Basic.lean" \
         "Mathlib/Data/Subtype.lean" "Mathlib/Logic/Unique.lean" \
         "Mathlib/Order/Basic.lean"; do
  printf -- '-- fake pinned source (%s)\n' "$f" > "$ML/$f"
done
printf 'leanprover/lean4:v4.99.0-fake\n' > "$ML/lean-toolchain"
(
  cd "$ML" && git init -q . \
    && git config user.email "demo@example.invalid" \
    && git config user.name "srcelab corpus demo" \
    && git add -A \
    && git -c commit.gpgsign=false commit -q -m "fake corpus"
) >/dev/null 2>&1
REV="$(git -C "$ML" rev-parse HEAD 2>/dev/null || true)"
if [ -z "$REV" ]; then
  echo "FATAL: fake corpus has no git rev; cannot exercise corpus identity" >&2
  exit 2
fi

# ---- a fake `clean` that always emits one fixture report ------------------
BIN="$TMP/fake_clean"
{
  printf '#!/bin/sh\ncat <<"JSON"\n'
  cat <<'JSON'
{
  "schema_version": "Clean-check-report-v1",
  "command": "clean check",
  "file": "fixture",
  "module": "fixture",
  "status": "fail",
  "decl_count": 257,
  "success_count": 86,
  "failed_count": 171,
  "trust_summary": { "sorry_axioms": 4, "kernel_check_failures": 0 },
  "errors": ["x: elaboration error"],
  "trust_failures": [],
  "kernel_failures": [],
  "proof_state_feedback": []
}
JSON
  printf 'JSON\nexit 1\n'
} > "$BIN"
chmod +x "$BIN"

mk() {  # mk <outfile> <python-body-editing-d>
  python3 - "$RATCHET" "$1" "$2" "$REV" <<'PY'
import json, sys
d = json.load(open(sys.argv[1], encoding="utf-8"))
REV = sys.argv[4]
exec(sys.argv[3])
# Performance is not this demo's subject (scripts/srcelab_guard_demo.sh owns
# it), and its fake `clean` reports no `timing`: an armed perf_baseline copied
# from the real ratchet would turn every arm here into failed:perf-unmeasured.
for _v in d.get("files", {}).values():
    _v.pop("perf_baseline", None)
json.dump(d, open(sys.argv[2], "w", encoding="utf-8"), indent=2)
PY
}

run() {  # run <ratchet> <reportdir> [args...]; echoes the verdict line
  local r="$1" rd="$2"; shift 2
  rm -rf "$rd"
  CLEAN_BIN="$BIN" CLEAN_MATHLIB_DIR="$ML" SRCELAB_RATCHET="$r" \
  SRCELAB_REPORT_DIR="$rd" SRCELAB_GATE_MEM_GIB_MIN=0 \
  "$GATE" "$@" 2>&1
}

ARMED='d["armed"]=True; d["armed_commit"]="deadbeef"; '
PIN_SELF='d["corpus"]={"rev":REV,"toolchain":"leanprover/lean4:v4.99.0-fake"}; '
PIN_OTHER='d["corpus"]={"rev":"0123456789abcdef0123456789abcdef01234567","toolchain":"leanprover/lean4:v4.99.0-fake"}; '

# ---- CONTROL: the pinned corpus measures and enforces ---------------------
# Without this a guard that refuses EVERYTHING would pass every arm below.
mk "$TMP/r_control.json" "${ARMED}${PIN_SELF}"'
for v in d["files"].values(): v["success_baseline"]=1'
OUT="$(run "$TMP/r_control.json" "$TMP/rep_control")"
if printf '%s\n' "$OUT" | grep -q '^SRCELAB_GATE=measured$'; then
  note "control: the PINNED corpus measures and enforces"
else
  broke "the control does not measure on its own pinned corpus — every arm below is vacuous"
fi

# ---- 1. a foreign corpus is refused, and NOT as a regression -------------
mk "$TMP/r_foreign.json" "${ARMED}${PIN_OTHER}"'
for v in d["files"].values(): v["success_baseline"]=9999'
OUT="$(run "$TMP/r_foreign.json" "$TMP/rep_foreign")"
NREP=0
for f in "$TMP/rep_foreign"/srcelab-*.json; do [ -e "$f" ] && NREP=$((NREP+1)); done
if ! printf '%s\n' "$OUT" | grep -q '^SRCELAB_GATE=skipped:corpus-mismatch$'; then
  broke "a foreign corpus was not refused (baselines of 9999 should be uncomparable, not a regression)"
elif printf '%s\n' "$OUT" | grep -q 'ratchet-regression'; then
  broke "a foreign corpus reported ratchet-regression — a cross-corpus comparison read as a code regression"
elif [ "$NREP" -ne 0 ]; then
  broke "the corpus pre-flight did not fail fast: the measurement was spent before the refusal"
else
  note "1. a foreign corpus skips corpus-mismatch, reports no regression, spends no measurement"
fi

# ---- 2. an armed ratchet with NO corpus pin fails closed -----------------
mk "$TMP/r_unpinned.json" "${ARMED}"'
d.pop("corpus", None)
for v in d["files"].values(): v["success_baseline"]=1'
OUT="$(run "$TMP/r_unpinned.json" "$TMP/rep_unpinned")"
if printf '%s\n' "$OUT" | grep -q '^SRCELAB_GATE=failed:corpus-unpinned$'; then
  note "2. an armed ratchet with no corpus pin fails closed"
else
  broke "an armed ratchet with no corpus identity did not fail closed — its baselines are counts of nothing identifiable"
fi

# ---- 3. the rebase exemption is NARROW ----------------------------------
# On the ratchet's OWN corpus the monotonic-up rule still binds: only an
# authorised --repin-corpus may re-base, because counts across corpora are not
# comparable and that exemption must not leak onto the matching-corpus path.
mk "$TMP/r_lower.json" "${ARMED}${PIN_SELF}"'
for v in d["files"].values(): v["success_baseline"]=9999'
OUT="$(run "$TMP/r_lower.json" "$TMP/rep_lower" --update)"
STILL="$(python3 -c '
import json,sys
d=json.load(open(sys.argv[1]))
print("yes" if all(v["success_baseline"]==9999 for v in d["files"].values()) else "no")' "$TMP/r_lower.json")"
if printf '%s\n' "$OUT" | grep -q '^SRCELAB_GATE=failed:ratchet-regression$' && [ "$STILL" = "yes" ]; then
  note "3. monotonic-up still binds on the pinned corpus; the rebase exemption did not leak"
else
  broke "monotonic-up lowering refusal did not hold on the pinned corpus — the corpus-rebase exemption leaked onto the matching path"
fi

# ---- 4. a foreign corpus cannot LAUNDER a baseline through --update ------
mk "$TMP/r_launder.json" "${ARMED}${PIN_OTHER}"'
for v in d["files"].values(): v["success_baseline"]=9999'
run "$TMP/r_launder.json" "$TMP/rep_launder" --update >/dev/null 2>&1
STILL="$(python3 -c '
import json,sys
d=json.load(open(sys.argv[1]))
ok = all(v["success_baseline"]==9999 for v in d["files"].values())
ok = ok and d["corpus"]["rev"]=="0123456789abcdef0123456789abcdef01234567"
print("yes" if ok else "no")' "$TMP/r_launder.json")"
if [ "$STILL" = "yes" ]; then
  note "4. --update on a foreign corpus re-arms nothing and does not move the pin"
else
  broke "--update on a foreign corpus moved the pin or the baselines without --repin-corpus — the mint can launder its own basis"
fi

if [ "$FAILED" -ne 0 ]; then
  echo "SRCELAB_CORPUS_DEMO=broken" >&2
  exit 1
fi
echo "SRCELAB_CORPUS_DEMO=ok (4 properties + control)"
