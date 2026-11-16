#!/bin/sh
# Measure how much of a stamped Mathlib corpus is actually USABLE from a Clean
# proof at `TrustGate::Strict`, and PASS/FAIL against a floor.
#
#   scripts/mathlib_usage_report.sh [--work <dir>] [--sample <n>] [--floor <pct>]
#                                   [--seed <n>] [--names <file>] [--jobs <n>]
#                                   [--keep <dir>]
#
#   --work    <dir>  chunked-stamp work dir (default ~/ml-full); expects
#                    <dir>/shards/**.mathverse and <dir>/evidence/kv_*.json
#   --sample  <n>    how many names to probe                      (default 60)
#   --floor   <pct>  minimum USAGE percentage to PASS             (default 80)
#   --seed    <n>    sampling seed; same seed = same names        (default 20260731)
#   --names   <file> probe exactly these names (overrides sample/seed) — use for
#                    a BEFORE/AFTER comparison on a fixed set
#   --jobs    <n>    probe concurrency, in PROCESSES               (default 1)
#
# MINTING IS NOT USAGE. The stamp reports `kernel_verified` — the count of
# constants whose values Clean's kernel accepted. That is a MINTING count. What a
# user cares about is whether citing the name CLOSES A GOAL, which additionally
# requires the whole transitive closure to be admissible at Strict. On one Mathlib
# module those numbers were 362 minted versus 47 hand-written lemmas usable.
# Conflating them has produced two overstated claims in this project, so this
# script reports USAGE and says so on every line.
#
# ONE PROCESS PER NAME, ALWAYS. `--jobs` runs separate PROCESSES concurrently; it
# never batches names into one process. Batching is UNSOUND here — the per-thread
# `MathverseEnvironment` memo carries state between citations and corrupts later
# verdicts, so a batched probe returns wrong answers while looking faster.
set -eu

REPO="${CLEAN_REPO:-$HOME/clean}"
WORK="${WORK:-$HOME/ml-full}"   # NOT /tmp — see mathlib_stamp_chunked.sh
SAMPLE=60
FLOOR=80
SEED=20260731
NAMES=""
# DEFAULT 1, AND RAISE IT ONLY AGAINST A MEASURED FOOTPRINT. Each probe holds
# the corpus as ANONYMOUS memory, not a shared mapping: against full Mathlib,
# measured RSS was 27-33 GB PER PROCESS. The old default of 6 was therefore
# ~4x physical on a 36 GB machine, and on 2026-08-01 it took the box down with
# a watchdog panic (free pages: 910, compressor pinned at its segment limit).
# Concurrency here multiplies memory, so the safe default is serial.
JOBS=1
KEEP=""

while [ $# -gt 0 ]; do
  case "$1" in
    --work)   WORK="$2";   shift 2 ;;
    --sample) SAMPLE="$2"; shift 2 ;;
    --floor)  FLOOR="$2";  shift 2 ;;
    --seed)   SEED="$2";   shift 2 ;;
    --names)  NAMES="$2";  shift 2 ;;
    --jobs)   JOBS="$2";   shift 2 ;;
    --keep)   KEEP="$2";   shift 2 ;;
    *) echo "unknown arg: $1" >&2; exit 2 ;;
  esac
done

PROBE="$REPO/target/release/examples/mathverse_mathlib_citation"
SHARDS="$WORK/shards"
EVID="$WORK/evidence"
FAIL=0
say() { printf '%s\n' "$*"; }
ok()  { say "PASS  $*"; }
bad() { say "FAIL  $*"; FAIL=1; }
die() { say "FAIL  $*"; exit 1; }

[ -x "$PROBE" ] || die "probe binary missing: $PROBE
      cargo build --offline --release -p clean-cli --example mathverse_mathlib_citation"
[ -d "$SHARDS" ] || die "no shard dir at $SHARDS"

OUT=$(mktemp -d); trap 'rm -rf "$OUT"' EXIT
# NOTE: `[ ... ] && { ... }` here would be a silent-exit bug under `set -e` —
# with KEEP empty the test returns 1, and as the last command in the list the
# shell exits with no output at all. Cost me a debugging cycle; use `if`.
if [ -n "$KEEP" ]; then mkdir -p "$KEEP"; OUT="$KEEP"; trap - EXIT; fi

say "== 1. corpus =="
NSHARD=$(find "$SHARDS" -name '*.mathverse' | wc -l | tr -d ' ')
[ "$NSHARD" -gt 0 ] || die "no .mathverse shards under $SHARDS"
say "      $NSHARD shards under $SHARDS"

# Union manifest over per-chunk subdirs; `path` is manifest-relative, which is
# what LibraryLoader::load_shard resolves against.
python3 - "$SHARDS" <<'PY' || die "could not build the union manifest"
import struct, json, os, sys, glob
d = sys.argv[1]
shards = []
for p in sorted(glob.glob(os.path.join(d, "**", "*.mathverse"), recursive=True)):
    h = struct.unpack_from('<12I', open(p, 'rb').read(64), 0)
    shards.append({"path": os.path.relpath(p, d), "content_hash": "local-probe-not-verified",
                   "constant_count": h[7], "expr_count": 0, "source": "lean4"})
json.dump({"version": 1, "base_shards": shards, "delta_shards": [],
           "total_constants": sum(s["constant_count"] for s in shards), "total_exprs": 0},
          open(os.path.join(d, "manifest.json"), "w"), indent=2)
print(f"      union manifest: {len(shards)} shards, "
      f"{sum(s['constant_count'] for s in shards):,} constants")
PY

say ""
say "== 2. name set (MINTING side) =="
ALL="$OUT/all_names.txt"
if [ -n "$NAMES" ]; then
  cp "$NAMES" "$ALL"
  say "      fixed set from $NAMES: $(wc -l < "$ALL" | tr -d ' ') names"
else
  python3 - "$EVID" "$ALL" "$SEED" "$SAMPLE" <<'PY' || die "could not build the name set"
import json, glob, os, random, sys
evid, out, seed, n = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
names, minted = set(), 0
for p in sorted(glob.glob(os.path.join(evid, "kv_*.json"))):
    try:
        d = json.load(open(p))
    except Exception:
        continue
    minted += d.get("kernel_verified", 0)
    names.update(d.get("kernel_verified_names", []))
names = sorted(names)
print(f"      minted KernelVerified (sum over chunks): {minted:,}")
print(f"      distinct names available to probe:       {len(names):,}")
if not names:
    raise SystemExit("no kernel_verified_names found — has any chunk finished?")
random.Random(seed).shuffle(names)
open(out, "w").write("\n".join(names[:n]) + "\n")
PY
  say "      sampled $(wc -l < "$ALL" | tr -d ' ') (seed $SEED)"
fi

say ""
say "== 3. USAGE — goals actually closed at TrustGate::Strict =="
say "      one PROCESS per name, $JOBS at a time; rc=0 (GOAL CLOSED) is the only pass"
i=0
while IFS= read -r n || [ -n "$n" ]; do
  [ -z "$n" ] && continue
  i=$((i+1))
  (
    if MATHVERSE_BY_NAME=1 MATHVERSE_PROBE_NAME="$n" MATHVERSE_SHARD_DIR="$SHARDS" \
         "$PROBE" > "$OUT/$i.out" 2>&1 && grep -q "GOAL CLOSED" "$OUT/$i.out"; then
      echo "CLOSED|$n" >> "$OUT/results.txt"
    else
      why=$(grep -oE 'Unknown constant: [^ ,"]*|does not agree in TYPE|not KernelVerified|below Strict|stub substitution|premise search' "$OUT/$i.out" 2>/dev/null | head -1)
      echo "FAILED|$n|${why:-unclassified}" >> "$OUT/results.txt"
    fi
  ) 2>/dev/null &
  while [ "$(jobs -rp | wc -l)" -ge "$JOBS" ]; do wait -n 2>/dev/null || wait; done
done < "$ALL"
wait

TOT=$(wc -l < "$ALL" | tr -d ' ')
# `grep -c` PRINTS 0 and EXITS 1 on no match, so `|| echo 0` appended a SECOND
# zero and CLOSED became "0\n0" — which broke the f-string below with a
# SyntaxError. The script therefore crashed on exactly the result it exists to
# report: a 0% usage run. Measured 2026-08-02 against the 700-module corpus,
# where all three sampled names failed and the report died instead of saying so.
CLOSED=$(grep -c '^CLOSED' "$OUT/results.txt" 2>/dev/null || true)
[ -n "$CLOSED" ] || CLOSED=0
PCT=$(python3 -c "print(f'{100*$CLOSED/$TOT:.1f}')")
say "      usable  $CLOSED/$TOT  ($PCT%)   <- a USAGE count, not a minting count"
say ""
say "      failure reasons:"
grep '^FAILED' "$OUT/results.txt" 2>/dev/null | awk -F'|' '{print $3}' | sort | uniq -c | sort -rn | head -8 | sed 's/^/        /'

say ""
if python3 -c "import sys; sys.exit(0 if $PCT >= $FLOOR else 1)"; then
  ok "usage $PCT% >= floor $FLOOR%"
else
  bad "usage $PCT% < floor $FLOOR%"
fi

say ""
if [ "$FAIL" = 0 ]; then say "ALL CHECKS PASSED  ($CLOSED/$TOT usable, $PCT%)"; else say "SOME CHECKS FAILED"; fi
if [ -n "$KEEP" ]; then say "  per-name output kept in $KEEP"; fi
exit "$FAIL"
