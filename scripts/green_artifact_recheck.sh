#!/usr/bin/env bash
# Re-verify every checked-in GREEN artifact against the CURRENT binary.
#
# WHY THIS EXISTS. A `reports/*-green.json` records that a `.lean` corpus checked
# clean at some commit, under some binary. Nothing re-ran it afterwards. On
# 2026-08-19 `scripts/mtype_green.sh` was found RED — MType.lean checked 32/49
# against a gate demanding 49/49 — and the source had not changed since
# 216ac5209. The regression was in the ELABORATOR, introduced somewhere in the
# 60 commits after the artifact was pinned, and it sat undetected for a week
# because no gate re-ran the claim.
#
# The full green scripts are slow (mtype's cert export alone is ~145 s), which is
# why they were not in the pre-push path. But the part that ROTTED is
# `clean check`, and that takes well under a second per file. This re-runs
# exactly that part and compares against the count the artifact recorded.
#
# Fail-closed: a missing binary, a missing artifact, an unparsable count, or a
# count that differs from the pin all FAIL. "Could not check" is never "green".
#
# Usage: scripts/green_artifact_recheck.sh [--bin path/to/clean]
set -euo pipefail

BIN="target/release/clean"
if [ "${1:-}" = "--bin" ]; then BIN="${2:?--bin needs a path}"; fi

if [ ! -x "$BIN" ]; then
  echo "GREEN_RECHECK=fail reason=no-binary path=$BIN" >&2
  echo "  build it first: targo --unverified build --locked --release -p clean" >&2
  exit 1
fi

# artifact : json-path-to-count : lean source
CASES=(
  "reports/mtype-core-green.json:declarations_checked:data/graduation/clean-mtype/proof/MType.lean"
  "reports/mtype-core-green.json:indexed_core.declarations_checked:data/graduation/clean-mtype/proof/MTypeIndexed.lean"
  "reports/coind-core-green.json:declarations_checked:data/graduation/clean-coind/proof/Coind.lean"
  "reports/coind-full-green.json:declarations_checked:data/graduation/clean-coind/proof/CoindFull.lean"
  "reports/streams-green.json:declarations_checked:data/graduation/clean-streams/proof/Streams.lean"
)

# ── COVERAGE: the CASES table must name every green artifact in the tree ─────
#
# CLAUDE.md's landing rule carries a corollary: "a green artifact
# (reports/*-green.json) is a DATED MEASUREMENT, not a standing claim —
# scripts/green_artifact_recheck.sh re-runs the cheap leg of each one in the
# full local gate, and new green artifacts must be added to its CASES table
# when minted."
#
# Until 2026-09-15 that last clause was enforced by NOBODY. CASES is a
# hand-typed bash array; nothing compared it to the set of artifacts on disk.
# Coverage happened to be complete (5 entries over the 4 artifacts that exist),
# so the gap was invisible — but the day someone mints reports/foo-green.json
# and forgets this table, the recheck skips it in silence and the corollary
# above reads as true while being false for that artifact. A rule whose
# compliance nothing measures is a convention, not a gate.
#
# Refuse, rather than warn: an uncovered green artifact is exactly the standing
# claim the corollary exists to forbid.
uncovered=""
for artifact in reports/*-green.json; do
  [ -e "$artifact" ] || continue
  case " ${CASES[*]} " in
    *" $artifact:"*|*":$artifact:"*) ;;
    *)
      if ! printf '%s\n' "${CASES[@]}" | grep -q "^${artifact}:"; then
        uncovered="$uncovered $artifact"
      fi
      ;;
  esac
done
if [ -n "$uncovered" ]; then
  echo "GREEN_RECHECK=fail uncovered green artifact(s):$uncovered" >&2
  echo "  Each reports/*-green.json is a DATED MEASUREMENT that this gate re-runs" >&2
  echo "  the cheap leg of; one that is not in CASES is re-run by nothing, and its" >&2
  echo "  green stands as an unchecked claim. Add it to CASES with its count key" >&2
  echo "  and Lean source (CLAUDE.md, *Landing rule: no capability without its" >&2
  echo "  caller*), or delete the artifact." >&2
  exit 1
fi


rc=0
for case in "${CASES[@]}"; do
  artifact="${case%%:*}"; rest="${case#*:}"
  key="${rest%%:*}"; src="${rest#*:}"

  if [ ! -f "$artifact" ]; then
    echo "GREEN_RECHECK=fail artifact=$artifact reason=missing"; rc=1; continue
  fi
  if [ ! -f "$src" ]; then
    echo "GREEN_RECHECK=fail artifact=$artifact source=$src reason=missing-source"; rc=1; continue
  fi

  pinned="$(python3 - "$artifact" "$key" <<'PY'
import json, sys
d = json.load(open(sys.argv[1]))
for part in sys.argv[2].split('.'):
    d = d.get(part) if isinstance(d, dict) else None
    if d is None:
        print(""); raise SystemExit(0)
print(d)
PY
)"
  if [ -z "$pinned" ]; then
    echo "GREEN_RECHECK=fail artifact=$artifact key=$key reason=unreadable-pin"; rc=1; continue
  fi

  # `clean check` prints "  N passed, M failed".
  out="$("$BIN" check "$src" --prelude builtin 2>&1 || true)"
  passed="$(printf '%s\n' "$out" | sed -n 's/^ *\([0-9][0-9]*\) passed.*/\1/p' | tail -1)"
  failed="$(printf '%s\n' "$out" | sed -n 's/.*, *\([0-9][0-9]*\) failed.*/\1/p' | tail -1)"

  if [ -z "$passed" ]; then
    echo "GREEN_RECHECK=fail source=$src reason=no-count-in-output"; rc=1; continue
  fi
  if [ "${failed:-0}" != "0" ] || [ "$passed" != "$pinned" ]; then
    echo "GREEN_RECHECK=fail source=$src pinned=$pinned now=${passed}passed/${failed:-?}failed artifact=$artifact"
    rc=1
    continue
  fi
  echo "GREEN_RECHECK=ok source=$src ${passed}/${pinned}"
done

# ── Kernel Arena round artifacts (reports/kernel-arena-battery/round-*.json) ──
#
# A round artifact (minted by crates/clean-olean/tests/kernel_arena_battery.rs)
# records how `clean olean replay --from-export` ended on every test of a
# vendored Kernel Arena round. Its cheap leg is the BAD half: every must-reject
# test is a small export, so each is re-run here through the current release
# binary and must still be REJECTED. The bad half is chosen by the archive's
# own `bad/` directory (inside the sha256-pinned archive), never by the
# artifact's `outcome` field, and must be all 71 of the round's bad tests. A
# reject is read from the `--json` report the binary prints (its `exit` field
# and a refusal it names), not from the exit status alone: exit 1 is also what
# an unclassified error exits. The good half (perf exports among them) is the
# battery's own run.
ARENA_FIXTURES="crates/clean-olean/tests/fixtures/kernel_arena"
for artifact in reports/kernel-arena-battery/round-*.json; do
  [ -e "$artifact" ] || continue
  round="$(python3 - "$artifact" <<'PY'
import json, sys
print(json.load(open(sys.argv[1]))["round"])
PY
)"
  archive="$ARENA_FIXTURES/round-$round/lean-arena-round-$round-tests.tar.gz"
  if [ ! -f "$archive" ]; then
    echo "GREEN_RECHECK=fail artifact=$artifact reason=missing-archive path=$archive"; rc=1; continue
  fi
  scratch="$(mktemp -d)"
  # The archive is untrusted data: checked against the artifact's sha256, read
  # with tarfile in memory, its regular files written under fresh names, and
  # nothing in it executed. Prints `<path> <recorded ending>` per bad test.
  if ! python3 -I - "$artifact" "$archive" "$scratch" > "$scratch/bad.txt" <<'PY'
import hashlib, json, sys, tarfile
ROUND_BAD = 71
artifact = json.load(open(sys.argv[1]))
blob = open(sys.argv[2], "rb").read()
if hashlib.sha256(blob).hexdigest() != artifact["archive"]["sha256"]:
    sys.exit("archive sha256 differs from the artifact's")
rows = {r["path"]: r for r in artifact["tests"]}
seen = 0
with tarfile.open(sys.argv[2], "r:gz") as tar:
    for member in tar.getmembers():
        if not member.isfile() or not member.name.startswith("bad/"):
            continue
        row = rows.get(member.name)
        if row is None:
            sys.exit(f"{member.name}: a bad test with no row in the artifact")
        if row["outcome"] != "reject" or row["clean"] != "reject":
            sys.exit(f"{member.name}: the artifact records outcome {row['outcome']}, clean {row['clean']}")
        data = tar.extractfile(member).read()
        out = sys.argv[3] + "/" + member.name.replace("/", "__")
        open(out, "wb").write(data)
        print(out, row["clean"])
        seen += 1
if seen != ROUND_BAD:
    sys.exit(f"{seen} bad tests in the archive, the round has {ROUND_BAD}")
PY
  then
    echo "GREEN_RECHECK=fail artifact=$artifact reason=unreadable-archive-or-artifact"; rc=1; rm -rf "$scratch"; continue
  fi
  checked=0
  arena_failed=0
  while read -r file recorded; do
    set +e
    "$BIN" olean replay --from-export "$file" --json > "$scratch/report.json" 2>/dev/null
    code=$?
    set -e
    now="$(python3 -I - "$scratch/report.json" "$code" <<'PY'
import json, sys
try:
    lines = [l for l in open(sys.argv[1]).read().splitlines() if l.strip()]
    report = json.loads(lines[-1])
except Exception:
    print(f"no-report-exit-{sys.argv[2]}")
    sys.exit(0)
exit_class = report.get("exit")
codes = {"accept": 0, "reject": 1, "decline": 2}
if codes.get(exit_class) != int(sys.argv[2]) or report.get("exit_code") != int(sys.argv[2]):
    print(f"inconsistent-{exit_class}-exit-{sys.argv[2]}")
elif exit_class == "reject" and not (report.get("reader_error") or report.get("first_refusal")):
    print("reject-without-a-refusal")
else:
    print(exit_class)
PY
)"
    if [ "$now" = "accept" ] || [ "$now" != "$recorded" ]; then
      echo "GREEN_RECHECK=fail artifact=$artifact test=$(basename "$file") recorded=$recorded now=$now"
      rc=1
      arena_failed=$((arena_failed + 1))
    fi
    checked=$((checked + 1))
  done < "$scratch/bad.txt"
  rm -rf "$scratch"
  if [ "$checked" -eq 0 ]; then
    echo "GREEN_RECHECK=fail artifact=$artifact reason=no-bad-tests"; rc=1; continue
  fi
  if [ "$arena_failed" -eq 0 ]; then
    echo "GREEN_RECHECK=ok artifact=$artifact bad-tests=$checked"
  fi
done

if [ "$rc" -ne 0 ]; then
  echo "" >&2
  echo "A checked-in green artifact no longer reproduces. Either a regression" >&2
  echo "landed, or the artifact is stale — regenerate with the owning script" >&2
  echo "(scripts/mtype_green.sh, scripts/coind_green.sh, scripts/streams_green.sh)" >&2
  echo "once it is genuinely green." >&2
fi
exit "$rc"
