#!/usr/bin/env bash
# Non-vacuous KernelVerified gate.
#
# RE-STAMPS the pinned, reproducible slice (data/kv_ratchet_slice.txt) with the
# clean kernel on every run and enforces, against committed baselines:
#   1. KV ratchet     — kernel_verified must not drop below the baseline in
#                       data/mathlib_kv_ratchet.json, and heuristic_kernel_verified
#                       must be 0 (soundness floor). [`clean mathverse ratchet check`]
#   2. Elision subset — every constant the statically-sound `--closure-elide opaque`
#                       run kernel-verified must still be verified under the
#                       production-default `opaque-and-theorem` run (eliding theorem
#                       values may only ADD KernelVerified, never drop one).
#                       [`clean mathverse elision-gate`]
#   0. Completeness  — in BOTH stamps, no slice constant failed or fell back to an
#                       axiom (`failed == 0`, `axiom_fallback == 0`, no olean
#                       failed to convert). Checked before 1 and 2, and on ANY
#                       corpus: it needs no baseline, so it holds the slice to
#                       "every constant re-checks" even where the count cannot be
#                       compared.
#
# ## The corpus pin (2026-10-07)
#
# The count in 1 is a property of the CORPUS as much as of Clean: it is how many
# constants the slice's two modules declare, all of them KernelVerified. The 702
# this gate was armed with on 2026-06-24 recorded no Mathlib revision, so it could
# not be reproduced anywhere -- the first measured run since (Mathlib 43ad0e9d,
# Lean v4.30.0-rc2) stamped 686 of 686 constants KernelVerified, 0 failed, 0
# fallback, and the ratchet called that a regression. A count is now compared only
# against the corpus it was minted on: data/kv_ratchet_corpus.json pins the
# sha256 of every slice .olean (plus the Mathlib rev and toolchain, for humans),
# and a corpus whose slice bytes differ runs the completeness floor and the
# elision subset but SKIPS the count comparison (`skipped:corpus-mismatch`,
# a FAILURE under KV_GATE_REQUIRE_MEASURED). Re-minting the count on a new corpus
# moves the pin and the baseline together, in one reviewed commit.
#
# This is what makes the gate NON-VACUOUS: it re-measures a real (small, fixed,
# OOM-safe, deterministic) slice rather than reading a static committed summary.
# A baseline of N>0 over a re-stamped slice catches a refactor that silently drops
# a KernelVerified verdict; a static summary or a 0 baseline would catch nothing.
#
# SKIP-green (exit 0) when the `clean` binary or the Mathlib checkout is absent, so
# clones without the corpus still pass. bash-3.2 safe.
#
# ## The verdict line (why a green exit code is not evidence)
#
# There are SEVEN skip-green paths below, and at least two of them fire routinely on
# an ordinary dev machine: the corpus lives under data/raw/mathlib4 and is commonly
# a symlink into /tmp (deleted by tmp cleanup), and the RAM admission check defers
# whenever the box is under 8GiB free — which concurrent builds cause constantly.
# So `exit 0` alone means ANY of: verified; no binary; no corpus; partial corpus;
# empty slice; a corpus other than the pinned one (the count was not compared);
# or simply that something else was using memory.
#
# Exit status therefore cannot distinguish a measurement from a deferral, and no
# automation (or release checklist, or blog post) should treat it as if it could.
# Every run now emits exactly one machine-readable verdict line on stdout:
#
#     KV_GATE=measured                 the slice was actually re-stamped and held
#     KV_GATE=skipped:<reason>         nothing was measured; <reason> says why
#     KV_GATE=failed:<reason>          a real regression (exit 1)
#
# Set KV_GATE_VERDICT_FILE=<path> to also write that line to a file.
#
# Set KV_GATE_REQUIRE_MEASURED=1 to make every skip a FAILURE instead. Any run
# whose result is going to be published — a release gate, a reproduction of the
# Mathlib KernelVerified numbers — must set it, so that "the gate was green"
# cannot silently mean "the gate measured nothing".
set -uo pipefail
cd "$(cd "$(dirname "$0")/.." && pwd)" || exit 1

SLICE=data/kv_ratchet_slice.txt
RATCHET=data/mathlib_kv_ratchet.json
CORPUS_PIN=data/kv_ratchet_corpus.json
ML=data/raw/mathlib4
MLLIB="$ML/.lake/build/lib/lean"
MLROOT="$MLLIB/Mathlib"

REQUIRE_MEASURED="${KV_GATE_REQUIRE_MEASURED:-0}"
case "$REQUIRE_MEASURED" in 1|true|TRUE|yes|YES) REQUIRE_MEASURED=1;; *) REQUIRE_MEASURED=0;; esac

# verdict <line>: emit the single machine-readable result line (stdout, and the
# optional KV_GATE_VERDICT_FILE). Called exactly once per run, on every path.
verdict() {
  echo "KV_GATE=$1"
  [ -n "${KV_GATE_VERDICT_FILE:-}" ] && printf 'KV_GATE=%s\n' "$1" > "$KV_GATE_VERDICT_FILE"
  return 0
}

# skip <reason-slug> <human text>: nothing was measured. Green by default so that
# clones without the corpus still pass; RED under KV_GATE_REQUIRE_MEASURED, because
# a publication run asserting a measurement must not accept a deferral.
skip() {
  if [ "$REQUIRE_MEASURED" = 1 ]; then
    echo "KV ratchet gate: FAIL — KV_GATE_REQUIRE_MEASURED is set but nothing was measured: $2." >&2
    verdict "skipped:$1"
    exit 1
  fi
  echo "SKIP: KV ratchet gate — $2."
  verdict "skipped:$1"
  exit 0
}

fail() { echo "KV ratchet gate: FAIL — $2" >&2; verdict "failed:$1"; exit 1; }

[ -f "$SLICE" ]    || skip no-slice-manifest "no slice manifest at $SLICE"
[ -d "$MLLIB" ]    || skip no-corpus "no Mathlib checkout at $MLLIB"

# Resolve the `clean` binary this gate is about to re-stamp KernelVerified with,
# and REFUSE one that cannot be shown to be built from this checkout.
#
# The three-line fallback that used to sit here (release, then debug, then
# `command -v clean`) had no freshness check at all, and the comment above it
# named the exact hazard -- "a stale PATH binary would re-stamp with the wrong
# kernel and yield a wrong count (false pass/fail)" -- without guarding it. The
# moment a corpus landed, this gate would have ratcheted a committed soundness
# baseline against whatever binary was lying in target/. Measured 2026-09-15:
# target/release/clean here was built 2026-08-27 and carries a build sha that
# resolves to no commit in this clone.
#
# The resolution and the check now live in one place with both callers, because
# scripts/kv_invariance_gate.sh carried the identical three lines and ITS
# registry row claims soundness and is already demonstrated.
#
# ORDER MATTERS, IN BOTH DIRECTIONS, and this sits between the two kinds of
# check above and below it.
#
# It is placed AFTER the slice and corpus checks, because those answer "is there
# anything to measure at all?" and their answer here is no. Refusing a stale
# binary on a tree that has no corpus would redden every lane for a binary the
# gate was never going to run, which is a false alarm and teaches people to
# ignore it.
#
# It is placed BEFORE the low-memory check, because that one is a DEFERRAL of
# work the gate does intend to do. A correctness refusal must outrank a
# deferral, or a stale binary on a loaded box arrives as a green
# `skipped:low-memory` -- the gate declining for a reason that has nothing to do
# with the thing that is actually wrong.
#
# Sourced by the relative path, like the sibling stamp_mem_governor.sh below:
# this script cd's to the repo root at the top and there is no $REPO_ROOT here.
# shellcheck source=scripts/lib/clean_binary_under_test.sh
. scripts/lib/clean_binary_under_test.sh
resolve_clean_binary_under_test
case "$?" in
  0) CLEAN_BIN="$CLEAN_BIN_UNDER_TEST" ;;
  2) skip no-binary "$CLEAN_BIN_REASON" ;;
  3) fail stale-binary "$CLEAN_BIN_REASON" ;;
  *) fail stale-binary "the binary-under-test resolver returned an unexpected status" ;;
esac

# LEAN_PATH: Mathlib lib + the pinned toolchain core + every Lake package lib.
TC="$(tr -d ' \t\r\n' < "$ML/lean-toolchain" | sed 's#/#--#; s#:#---#')"
CORE="$HOME/.elan/toolchains/$TC/lib/lean"
LP="$MLLIB"
[ -d "$CORE" ] && LP="$LP:$CORE"
for p in "$ML"/.lake/packages/*/.lake/build/lib/lean; do
  [ -d "$p" ] && LP="$LP:$p"
done
export LEAN_PATH="$LP"

# Resolve the slice's relative module paths to absolute oleans.
TARGETS=""
while IFS= read -r line; do
  case "$line" in ''|\#*) continue;; esac
  f="$MLROOT/$line"
  [ -f "$f" ] || skip partial-corpus "slice module missing from checkout: $line"
  TARGETS="$TARGETS $f"
done < "$SLICE"
[ -n "$TARGETS" ] || skip empty-slice "slice manifest is empty"

# Is this the corpus the count baseline was minted on? Compared by CONTENT: the
# set of slice paths must equal the pin's, and every slice .olean's sha256 must
# equal its pinned digest. Decided here, acted on only after the stamps: a
# mismatched corpus still runs the completeness floor and the elision subset,
# which need no baseline, and skips only the count comparison. An unreadable or
# malformed pin is a FAILURE, never a reason to compare blind.
[ -f "$CORPUS_PIN" ] || fail corpus-pin "no corpus pin at $CORPUS_PIN -- the count baseline in $RATCHET cannot be tied to a corpus"
CORPUS_STATE="$(python3 - "$CORPUS_PIN" "$SLICE" "$MLROOT" <<'PY'
import hashlib, json, sys
pin_path, slice_path, mlroot = sys.argv[1:4]
try:
    pin = json.load(open(pin_path, encoding="utf-8"))
    pinned = pin["slice_sha256"]
    assert isinstance(pinned, dict) and pinned
except Exception as exc:  # noqa: BLE001 -- the shell turns this into a FAILURE
    print(f"malformed {pin_path}: {exc}")
    sys.exit(2)
rows = [l.strip() for l in open(slice_path, encoding="utf-8")]
rows = [l for l in rows if l and not l.startswith("#")]
if sorted(rows) != sorted(pinned):
    print(f"mismatch: the slice lists {sorted(rows)}, the pin covers {sorted(pinned)}")
    sys.exit(0)
for rel in rows:
    h = hashlib.sha256(open(f"{mlroot}/{rel}", "rb").read()).hexdigest()
    if h != pinned[rel]:
        print(f"mismatch: {rel} is sha256:{h[:12]}, pinned sha256:{pinned[rel][:12]} "
              f"(Mathlib {pin.get('mathlib_rev', '?')[:12]})")
        sys.exit(0)
print("match")
PY
)" || fail corpus-pin "$CORPUS_STATE"

# Lightweight OOM admission. Deliberately NOT the heavy-stamp global lock
# (scripts/lib/stamp_mem_governor.sh): that lock is held ~continuously by the
# corpus-stamp automation, so taking it would make this gate hang or perma-skip.
# A 2-module slice (~2GiB) needs no heavy-stamp mutual exclusion; we only refuse to
# pile on when the box is ALREADY under memory pressure (e.g. a corpus stamp is
# mid-run), turning a potential OOM into a clean skip. Sourcing the lib only sets
# var defaults + defines functions (no lock/trap at source time).
if [ -r scripts/lib/stamp_mem_governor.sh ]; then
  # shellcheck source=/dev/null
  . scripts/lib/stamp_mem_governor.sh
  _avail="$(stamp_available_gib 2>/dev/null || echo 999)"
  case "$_avail" in ''|*[!0-9]*) _avail=999;; esac
  [ "$_avail" -lt 8 ] && skip low-memory "only ${_avail}GiB free RAM (a corpus stamp may be running); deferring the slice stamp"
fi

OUT="$(mktemp -d "${TMPDIR:-/tmp}/kv_ratchet_gate.XXXXXX")"
trap 'rm -rf "$OUT"' EXIT

# A FRESH out-dir per stamp avoids stale-shard contamination (the cause of the
# 2026-06-24 false "provenance UnexpectedEnd" scare). --single-pass for the slice.
stamp() {  # <elision> <summary-out> <manifest-out>
  # shellcheck disable=SC2086
  "$CLEAN_BIN" mathverse stamp-verified $TARGETS \
    --out-dir "$OUT/shards_$1" \
    --closure-root "$MLLIB" \
    --closure-elide "$1" \
    --single-pass \
    --manifest "$3" \
    --json > "$2" 2> "$OUT/stamp_$1.err" \
    || { echo "stamp ($1) errored:" >&2; tail -5 "$OUT/stamp_$1.err" >&2; return 1; }
}

echo "  re-stamping pinned slice (opaque-and-theorem + opaque)..."
stamp opaque-and-theorem "$OUT/summary_oat.json" "$OUT/kv_oat.json" || fail stamp-oat "production-default stamp of the pinned slice"
stamp opaque             "$OUT/summary_op.json"  "$OUT/kv_op.json"  || fail stamp-opaque "statically-sound (opaque) stamp of the pinned slice"

# 0. Completeness, on any corpus: no slice constant failed or fell back to an
#    axiom in EITHER stamp, and every olean converted.
for _mode in oat op; do
  _gap="$(python3 - "$OUT/summary_$_mode.json" <<'PY'
import json, sys
try:
    s = json.load(open(sys.argv[1], encoding="utf-8"))
    bad = {k: s[k] for k in ("failed", "axiom_fallback") if s[k] != 0}
    if s["oleans_failed"]:
        bad["oleans_failed"] = s["oleans_failed"]
except Exception as exc:  # noqa: BLE001 -- an unreadable summary is a gap
    print(f"unreadable stamp summary {sys.argv[1]}: {exc}")
    sys.exit(0)
if bad:
    print(f"{bad} of {s.get('total')} slice constants")
PY
)"
  [ -z "$_gap" ] || fail slice-incomplete "the $_mode stamp did not kernel-verify every slice constant: $_gap"
done

# 1. KV ratchet (monotonic-UP + heuristic==0 soundness floor) on the oat summary,
#    only against the corpus the baseline was minted on (see "The corpus pin").
if [ "$CORPUS_STATE" = match ]; then
  "$CLEAN_BIN" mathverse ratchet check --summary "$OUT/summary_oat.json" --ratchet "$RATCHET" \
    || fail ratchet-regression "re-stamping the pinned slice dropped KernelVerified below the baseline (or heuristic_kernel_verified != 0); see $RATCHET + $SLICE"
fi

# 2. Elision subset gate: KV(opaque) must be subset-of KV(opaque-and-theorem).
"$CLEAN_BIN" mathverse elision-gate "$OUT/kv_op.json" "$OUT/kv_oat.json" \
  || fail elision-subset "opaque-and-theorem dropped a KernelVerified constant that the statically-sound opaque run kept"

[ "$CORPUS_STATE" = match ] \
  || skip corpus-mismatch "every slice constant re-checked and the elision subset held, but the corpus is not the one $RATCHET was minted on ($CORPUS_STATE), so the KernelVerified COUNT was not compared; re-mint the pin and the baseline together on a new corpus, never one without the other"

echo "  KV ratchet gate: PASS (slice re-stamped; ratchet + elision subset hold)."
verdict measured
