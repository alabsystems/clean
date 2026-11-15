#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Self-test of scripts/lean_export_mint.sh (`--selftest` runs this file;
# scripts/check_script_selftests.sh runs it with every scripts/test_*.sh).
# No network, no real build, no Lean: the toolchains are fake directories under
# a temp ELAN_HOME whose `lean` is a shell script; the exporter (bundled, or
# built by the fake toolchain's `lake`) is a shell script that writes synthetic
# NDJSON and logs its argv and environment; lean4export is a temp git repo
# served over file:// (LEAN_EXPORT_MINT_EXPORTER_REPO); the gate is a fake that
# logs its reservations and weight queries (LEAN_EXPORT_MINT_HEAVY_GATE), or,
# for the reservation rules, the real heavy_gate.sh's `weight` and resolver
# over a scratch peak log. Shims on the publish step (an `mv` on PATH and a
# python in front of the python half) plant what another run would leave there
# between the last check and the publish; between the export's placement and
# its sidecar's, where no shim reaches, the script's own python half runs with
# os.link and os.rename wrapped by the test. The one real export is the vendored
# arena archive's Init.Prelude, read by the record check. Each arm asserts the
# exit code AND the named reason, so an arm cannot pass on a different refusal.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TOOL="$HERE/lean_export_mint.sh"
ARENA="$HERE/../crates/clean-olean/tests/fixtures/kernel_arena/round-2026-09/lean-arena-round-2026-09-tests.tar.gz"
unset HEAVY_GATE_HELD LEAN_EXPORT_MINT_LIB LEAN_PATH LEAN_EXPORT_MINT_EXPORTER_REPO LEAN_EXPORT_MINT_PYTHON \
  LEAN_EXPORT_MINT_LOCK_WAIT LEAN_EXPORT_MINT_CACHE FAKE_GATE_BASIS FAKE_GATE_WEIGHT_FAIL FAKE_PY_FAIL_VERB \
  FAKE_GATE_RC FAKE_GATE_FSIZE FAKE_GATE_CHMOD CACHE_UNDER_TEST LCACHE_UNDER_TEST TMPDIR_UNDER_TEST \
  FAKE_GATE_AUTO_GB FAKE_GATE_FLOOR FAKE_GATE_FLOOR_FAIL FAKE_PLANT FAKE_PLANT_AT FAKE_PY_DROP FAKE_PEAK_GB FAKE_SHA \
  GATE_UNDER_TEST HEAVY_GATE_DIR HEAVY_GATE_PHYS_GB HEAVY_GATE_BUDGET_GB HEAVY_GATE_QUIET HEAVY_GATE_AUTO_WINDOW \
  HEAVY_GATE_AUTO_FACTOR HEAVY_GATE_AUTO_FLOOR_GB HEAVY_GATE_AUTO_FALLBACK_GB FAKE_GATE_RESERVE FAKE_GATE_HELD \
  FAKE_GATE_PRE_RUN CUT CUT_AT CUT_OTHER CUT_LOG B_PARTIAL TOOL_UNDER_CUT
td=$(mktemp -d "${TMPDIR:-/tmp}/lean_export_mint_selftest.XXXXXX") || exit 1
td=$(cd "${td:?}" && pwd -P) || exit 1
[ -n "$td" ] && [ -d "$td" ] || exit 1
# chflags: an arm makes a file immutable (uchg), which rm cannot remove.
trap 'chflags -R nouchg -- "${td:?}" 2>/dev/null; chmod -R u+w -- "${td:?}" 2>/dev/null; rm -rf -- "${td:?}"' EXIT
GH=0123456789abcdef0123456789abcdef01234567
pass=0; fails=0
ok() { echo "  selftest ok: $1"; pass=$((pass + 1)); }
bad() { echo "  selftest FAILED: $1"; fails=$((fails + 1)); }
lib() { ( LEAN_EXPORT_MINT_LIB=1; . "$TOOL"; "$@" ) >"$td/stdout" 2>"$td/stderr"; RC=$?; }
pin_gh() { ( LEAN_EXPORT_MINT_LIB=1; . "$TOOL"; pinned_githash "$1" ); }
sha() { python3 -I -c 'import hashlib,sys; print(hashlib.sha256(open(sys.argv[1],"rb").read()).hexdigest())' "$1"; }
pair_sha() {  # <out>: "<sha256 of the export> <the sha256 its sidecar records>"
  printf '%s %s' "$(sha "$1" 2>/dev/null)" \
    "$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["export"]["sha256"])' "$1.sidecar.json" 2>/dev/null)"
}

# A fake elan toolchain: `lean` (banner, githash), a fake exporter template its
# `lake` builds and its bundled `leanexport` copies, and the exporter's default
# body. The githash defaults to the tag's pin. Prints the toolchain dir.
fake_toolchain() {  # <tc> [<banner version>] [<githash>] [bundled]
  local tc=$1 ver=${2:-${1#v}} gh=${3:-} d
  [ -n "$gh" ] || gh=$(pin_gh "$tc"); [ -n "$gh" ] || gh=$GH
  d="$td/elan/toolchains/leanprover--lean4---$tc"
  mkdir -p "$d/bin" "$d/libexec"
  printf '#!/bin/sh\ncase "$1" in\n  --version) echo "Lean (version %s, arm64-apple-darwin, commit %s, Release)" ;;\n  --githash) echo "%s" ;;\n  *) exit 64 ;;\nesac\n' \
    "$ver" "$gh" "$gh" >"$d/bin/lean"
  { printf '#!/bin/sh\nD=%s\n' "'$d'"; cat <<'SH'
FAKE_NAME=lean4export FAKE_FORMAT=3.1.0 FAKE_VERSION=unset FAKE_GH=unset FAKE_RC=0 FAKE_BODY= FAKE_TOUCH= FAKE_PROBE=
FAKE_SIGNAL= FAKE_MKDIR= FAKE_LIKE_LEAN=
. "$D/fake.conf"
[ -z "$FAKE_PROBE" ] || { [ -e "$FAKE_PROBE" ] && echo present || echo absent; } >"$D/probe.log"
printf '%s\n' "$*" >"$D/argv.log"
printf 'LEAN_SYSROOT=%s\nLEAN_ABORT_ON_PANIC=%s\nLEAN_PATH=%s\nPATH=%s\nCANARY=%s\n' \
  "${LEAN_SYSROOT:-}" "${LEAN_ABORT_ON_PANIC:-}" "${LEAN_PATH:-}" "$PATH" "${MINT_SELFTEST_CANARY:-}" >"$D/env.log"
[ -z "$FAKE_SIGNAL" ] || kill "-$FAKE_SIGNAL" $$
[ "$FAKE_RC" = 0 ] || exit "$FAKE_RC"
[ -z "$FAKE_TOUCH" ] || echo planted >"$FAKE_TOUCH"
[ -z "$FAKE_MKDIR" ] || mkdir -p "$FAKE_MKDIR"
# FAKE_LIKE_LEAN: exit 0 whatever became of the output, as Lean does when its
# last flush fails. (Its stdout is the writer's pipe, so no file limit reaches it.)
printf '{"meta":{"exporter":{"name":"%s","version":"3.1.0"},"format":{"version":"%s"},"lean":{"githash":"%s","version":"%s"}}}\n' \
  "$FAKE_NAME" "$FAKE_FORMAT" "$FAKE_GH" "$FAKE_VERSION"
cat "${FAKE_BODY:-$D/body.ndjson}" 2>/dev/null
[ -z "$FAKE_LIKE_LEAN" ] || exit 0
SH
  } >"$d/libexec/lean4export-fake"
  { printf '#!/bin/sh\nD=%s\n' "'$d'"; cat <<'SH'
FAKE_LAKE=ok
[ ! -f "$D/lake.conf" ] || . "$D/lake.conf"
printf '%s\n' "$*" >"$D/lake.log"
printf 'PWD=%s\nLEAN_SYSROOT=%s\nPATH=%s\nCANARY=%s\nLEAN_PATH=%s\n' "$PWD" "${LEAN_SYSROOT:-}" "$PATH" \
  "${MINT_SELFTEST_CANARY:-}" "${LEAN_PATH:-}" >"$D/lake.env"
[ "$FAKE_LAKE" != nobin ] || exit 0
mkdir -p .lake/build/bin && cp "$D/libexec/lean4export-fake" .lake/build/bin/lean4export && chmod +x .lake/build/bin/lean4export
case "$FAKE_LAKE" in
  fail) exit 1 ;;
  modify) echo '-- edited by the build' >>Main.lean ;;
  race) mkdir -p "${PWD%.partial.*}" ;;
  stampdir) mkdir .mint-built ;;
esac
exit 0
SH
  } >"$d/bin/lake"
  chmod +x "$d/bin/lean" "$d/bin/lake" "$d/libexec/lean4export-fake"
  if [ "${4:-}" = bundled ]; then cp "$d/libexec/lean4export-fake" "$d/bin/leanexport"; fi
  printf 'FAKE_VERSION=%s\nFAKE_GH=%s\n' "$ver" "$gh" >"$d/fake.conf"
  cat >"$d/body.ndjson" <<'NDJSON'
{"in":1,"str":{"pre":0,"str":"Nat"}}
{"in":2,"str":{"pre":1,"str":"zero"}}
{"in":3,"str":{"pre":1,"str":"succ"}}
{"in":4,"str":{"pre":1,"str":"rec"}}
{"in":5,"str":{"pre":1,"str":"add"}}
{"in":6,"str":{"pre":1,"str":"lt"}}
{"il":1,"succ":0}
{"ie":0,"sort":1}
{"inductive":{"types":[{"name":1}],"ctors":[{"name":2},{"name":3}],"recs":[{"name":4}]}}
{"def":{"name":5}}
NDJSON
  printf '%s\n' "$d"
}

mkdir -p "$td/tmp"   # every run's TMPDIR: the gate's start marker lands there
run() {  # <tool args>...: sets RC, and $td/{stdout,stderr}
  : >"$td/gate.log"
  TMPDIR="${TMPDIR_UNDER_TEST:-$td/tmp}" ELAN_HOME="$td/elan" LEAN_EXPORT_MINT_CACHE="${CACHE_UNDER_TEST:-$td/cache}" \
  LEAN_EXPORT_MINT_HEAVY_GATE="${GATE_UNDER_TEST:-$td/fakegate.sh}" GATE_LOG="$td/gate.log" MINT_SELFTEST_CANARY=leaked \
    bash "$TOOL" "$@" >"$td/stdout" 2>"$td/stderr" </dev/null
  RC=$?
}

expect() {  # <arm> <rc> <stderr needle>
  if [ "$RC" -eq "$2" ] && { [ -z "$3" ] || grep -qF -- "$3" "$td/stderr"; }; then ok "$1"
  else bad "$1 (want rc=$2 and '$3'; got rc=$RC: $(head -c 300 "$td/stderr"))"; fi
}
expect1() {  # <arm> <rc> <stderr needle>: expect, and the needle's refusal is the run's only one
  if [ "$(grep -c 'LEAN_EXPORT_MINT=refused' "$td/stderr")" = 1 ]; then expect "$@"
  else bad "$1 (want one refusal line; got: $(grep 'LEAN_EXPORT_MINT=refused' "$td/stderr" | head -c 400))"; fi
}

sidecar_has() {  # <arm> <sidecar> <JSON>: each field named equals the value given ("k!": exactly)
  if python3 -I - "$2" "$3" >"$td/sc.check" 2>&1 <<'PY'
import json, sys
s, want = json.load(open(sys.argv[1])), json.loads(sys.argv[2])
def diff(w, g, at):
    if not isinstance(w, dict):
        return [] if w == g else [f"{at}: want {w!r}, got {g!r}"]
    if not isinstance(g, dict):
        return [f"{at}: want an object, got {g!r}"]
    out = []
    for k, v in w.items():
        if k.endswith("!"):
            got = g.get(k[:-1], "<absent>")
            out += [] if v == got else [f"{at}.{k[:-1]}: want exactly {v!r}, got {got!r}"]
        else:
            out += diff(v, g.get(k, "<absent>"), f"{at}.{k}")
    return out
problems = diff(want, s, "")
sys.exit("; ".join(problems) if problems else 0)
PY
  then ok "$1"; else bad "$1: $(cat "$td/sc.check")"; fi
}

cat >"$td/fakegate.sh" <<'SH'
#!/bin/sh
# Logs `run <weight> <label> -- <first word>`, and each weight query, which it
# answers as heavy_gate.sh does (`<gb>\t<basis>`): an auto:<class>:<fallback>
# with FAKE_GATE_AUTO_GB (default the fallback) and FAKE_GATE_BASIS (default
# unseen), an explicit weight with FAKE_GATE_FLOOR, the label's floor (default
# none). FAKE_GATE_WEIGHT_FAIL fails every query, FAKE_GATE_FLOOR_FAIL the
# explicit ones; FAKE_GATE_RC is a gate that fails before the job starts (75:
# heavy_gate's small-box refusal), FAKE_GATE_FSIZE a file size limit on the job
# alone (KiB: the tool runs this with bash), and FAKE_GATE_CHMOD a directory
# made read-only as the job starts. The job runs as heavy_gate.sh runs it, with
# HEAVY_GATE_HELD=<gb>:<label>: <gb> is what the weight query answers for its
# spec, or FAKE_GATE_RESERVE (a reservation under it), or the whole value is
# FAKE_GATE_HELD.
case "$1" in
  weight) printf '%s\n' "$*" >>"$GATE_LOG"
          [ -z "${FAKE_GATE_WEIGHT_FAIL:-}" ] || exit 70
          case "$2" in
            auto:*) c=${2#auto:}; c=${c%:*}
                    printf '%s\t%s\n' "${FAKE_GATE_AUTO_GB:-${2##*:}}" \
                      "${FAKE_GATE_BASIS:-unseen class $c: no measured run yet, fallback ${2##*:} GB}" ;;
            *) [ -z "${FAKE_GATE_FLOOR_FAIL:-}" ] || exit 70
               if [ "${FAKE_GATE_FLOOR:-0}" -gt "$2" ]; then
                 printf '%s\texplicit weight %s raised to its label class floor\n' "$FAKE_GATE_FLOOR" "$2"
               else printf '%s\texplicit weight\n' "$2"; fi ;;
          esac
          exit 0 ;;
  run) printf '%s %s %s %s %s\n' "$1" "$2" "$3" "$4" "$5" >>"$GATE_LOG"
       [ -z "${FAKE_GATE_RC:-}" ] || exit "$FAKE_GATE_RC"
       case "$2" in
         auto:*) gb=${FAKE_GATE_AUTO_GB:-${2##*:}} ;;
         *) gb=$2; [ "${FAKE_GATE_FLOOR:-0}" -le "$gb" ] || gb=$FAKE_GATE_FLOOR ;;
       esac
       held="${FAKE_GATE_RESERVE:-$gb}:$3" ;;
  *) exit 64 ;;
esac
shift 3
[ "$1" = "--" ] && shift
[ -z "${FAKE_GATE_FSIZE:-}" ] || ulimit -f "$FAKE_GATE_FSIZE"
[ -z "${FAKE_GATE_CHMOD:-}" ] || chmod 555 "$FAKE_GATE_CHMOD"
HEAVY_GATE_HELD=${FAKE_GATE_HELD:-$held} exec "$@"
SH
# The real gate's reservation rules without its admission: `weight` IS
# scripts/heavy_gate.sh over a scratch HEAVY_GATE_DIR; `run` resolves its weight
# with the real scripts/heavy_gate_weights.sh, logs `run <spec> <label> GB=<gb>
# CLASS=<class>`, runs the job, and appends the peak line heavy_gate.sh's
# `_peak_report` writes (peak FAKE_PEAK_GB), with `class=` only when the weight
# was auto: (heavy_gate.sh `run`: `cls=$CLASS`; `_peak_report`: `[ -n "$cls" ]
# && tail="$tail class=$cls"`; an arm below holds the gate to both lines). The
# job sees HEAVY_GATE_HELD=<gb>:<label>, as heavy_gate.sh's `run` sets it.
# FAKE_GATE_PRE_RUN is a peak line another run files just before this run's
# weight is resolved.
cat >"$td/resolvergate.sh" <<SH
#!/bin/bash
REAL="$HERE"
SH
cat >>"$td/resolvergate.sh" <<'SH'
case "$1" in
  weight) exec bash "$REAL/heavy_gate.sh" "$@" ;;
  run) GATE_DIR=$HEAVY_GATE_DIR; PEAKLOG=$GATE_DIR/peaks.log
       [ -z "${FAKE_GATE_PRE_RUN:-}" ] || printf '%s\n' "$FAKE_GATE_PRE_RUN" >>"$PEAKLOG"
       . "$REAL/heavy_gate_weights.sh"
       HEAVY_GATE_QUIET=1 _resolve_weight "$2" "$3"
       label=$3; spec=$2; shift 3; [ "$1" = "--" ] && shift
       printf 'run %s %s GB=%s CLASS=%s\n' "$spec" "$label" "$GB" "$CLASS" >>"$GATE_LOG"
       HEAVY_GATE_HELD="$GB:$label" "$@"; rc=$?
       tail=" rc=$rc"; [ -n "$CLASS" ] && tail="$tail class=$CLASS"
       printf '%s %s reserved=%s peak_gb=%s pct=50 dur=0m01s%s\n' "$(date -u +%FT%TZ)" "$label" "$GB" \
         "${FAKE_PEAK_GB:-1.00}" "$tail" >>"$PEAKLOG"
       exit "$rc" ;;
  *) exit 64 ;;
esac
SH
# What another run leaves at FAKE_PLANT_AT just before this run's publish step,
# whichever program performs it: `dir` (an empty directory), `file`, or
# `copy:<dir>` (a finished build). Once: nothing is planted over what is there.
cat >"$td/plant.sh" <<'SH'
#!/bin/sh
[ -n "${FAKE_PLANT_AT:-}" ] && [ ! -e "$FAKE_PLANT_AT" ] || exit 0
case "${FAKE_PLANT:-}" in
  dir) mkdir -p "$FAKE_PLANT_AT" ;;
  file) echo planted >"$FAKE_PLANT_AT" ;;
  copy:*) cp -R "${FAKE_PLANT#copy:}" "$FAKE_PLANT_AT" ;;
esac
SH
cat >"$td/fakepy.sh" <<'SH'
#!/bin/sh
# python3, except that the step named $FAKE_PY_FAIL_VERB exits $FAKE_PY_FAIL_RC
# (the verb follows the program: `-I -c <program> <verb>`); before the publish
# steps (`rename`, `publish <partial> ...`) plant.sh plants, and FAKE_PY_DROP
# (export or sidecar) removes that partial file, so its placement fails.
if [ -n "${FAKE_PY_FAIL_VERB:-}" ] && [ "${4:-}" = "$FAKE_PY_FAIL_VERB" ]; then exit "${FAKE_PY_FAIL_RC:-1}"; fi
case "${4:-}" in
  rename|publish) "$(dirname "$0")/plant.sh" ;;
esac
if [ "${4:-}" = publish ]; then
  case "${FAKE_PY_DROP:-}" in
    export) rm -f -- "$5" ;;
    sidecar) rm -f -- "$5.sidecar" ;;
  esac
fi
exec python3 "$@"
SH
mkdir -p "$td/mvshim"
cat >"$td/mvshim/mv" <<'SH'
#!/bin/sh
# mv, after plant.sh when its target is FAKE_PLANT_AT: the publish step of a
# script that moves with mv meets the same late arrival as the python half's.
for last; do :; done
[ "$last" != "${FAKE_PLANT_AT:-}" ] || "$(dirname "$0")/../plant.sh"
exec /bin/mv "$@"
SH
chmod +x "$td/fakegate.sh" "$td/resolvergate.sh" "$td/plant.sh" "$td/fakepy.sh" "$td/mvshim/mv"
# A python whose inline sha256 program (sha256_of) fails, prints no sha256
# (FAKE_SHA=garbage), or prints the true sha256 and then fails (FAKE_SHA=late);
# every other program runs.
cat >"$td/shafail.sh" <<'SH'
#!/bin/sh
case "${3:-}" in
  "import hashlib,sys"*) if [ "${FAKE_SHA:-}" = garbage ]; then echo not-a-sha256; exit 0; fi
                         if [ "${FAKE_SHA:-}" = late ]; then python3 "$@"; exit 1; fi
                         echo "shafail: injected failure" >&2; exit 1 ;;
esac
exec python3 "$@"
SH
chmod +x "$td/shafail.sh"

# ── usage (exit 2) ────────────────────────────────────────────────────────────
run --module Init.Prelude;                                   expect "no --toolchain is a usage error" 2 "--toolchain is required"
run --toolchain v4.30.0-rc2;                                 expect "no --module is a usage error" 2 "at least one --module"
run --toolchain 4.30.0-rc2 --module Init.Prelude;            expect "a toolchain spelled without its v is refused" 2 "is not spelled"
run --toolchain v4.30.0-rc2 --module -x;                     expect "a module name starting with '-' is refused" 2 "bad module name"
run --toolchain v4.30.0-rc2 --module Init --decl 'a b' --out x; expect "a declaration name with whitespace is refused" 2 "bad declaration name"
run --toolchain v4.30.0-rc2 --module Init --decl Nat.add;    expect "--decl without --out is refused" 2 "--decl needs an explicit --out"
run --toolchain v4.30.0-rc2 --module Init --gate-gb 4g;      expect "a non-numeric --gate-gb is refused" 2 "whole number of GB"
run --toolchain v4.30.0-rc2 --module Init --gate-gb 00;      expect "a --gate-gb of 0 (it reserves nothing) is refused" 2 "whole number of GB above 0"
run --toolchain v4.30.0-rc2 --module Init --gate-gb 010;     expect "a --gate-gb with a leading 0 is refused: heavy_gate's arithmetic reads 010 as octal 8" 2 "--gate-gb '010' starts with 0"
run --toolchain v4.30.0-rc2 --module Init --gate-gb 08;      expect "... and 08, which heavy_gate's arithmetic refuses" 2 "--gate-gb '08' starts with 0"
run --toolchain v4.30.0-rc2 --module Init --gate-gb 10000;   expect "a --gate-gb over 9999 GB is refused" 2 "--gate-gb '10000' is over 9999 GB"
run --toolchain v4.30.0-rc2 --module Init --gate-gb 9223372036854775808; expect "... and 2^63, where the shell's comparison fails and once reserved 0 GB" 2 "is over 9999 GB"
run --toolchain v4.30.0-rc2 --module;                        expect "an option with no value is refused" 2 "--module needs a value"
run --toolchain v4.30.0-rc2 --module Init --bogus;           expect "an unknown argument is refused" 2 "unknown argument"
LEAN_EXPORT_MINT_LOCK_WAIT=soon run --toolchain v4.30.0-rc2 --module Init; expect "a non-numeric lock wait is refused" 2 "LEAN_EXPORT_MINT_LOCK_WAIT"
LEAN_EXPORT_MINT_PYTHON="$td/no-such-python3" run --toolchain v4.30.0-rc2 --module Init; expect "a python that is not there is refused" 1 "reason=no-python"
run --toolchain v4.30.0-rc2 --module Init --out "$td" --force; expect "--out naming an existing directory is refused, --force or not" 2 "is a directory"
run --toolchain v4.30.0-rc2 --module Init --out "$td/newdir/"; expect "--out ending in / is refused" 2 "ends in '/'"

# ── the toolchain and its pins ────────────────────────────────────────────────
run --toolchain v4.30.0-rc2 --module Init.Prelude;           expect "a toolchain that is not installed is refused" 1 "reason=toolchain-not-installed v4.30.0-rc2: no executable"
d=$(fake_toolchain v4.30.0-rc2); printf '#!/bin/sh\nexit 3\n' >"$d/bin/lean"
run --toolchain v4.30.0-rc2 --module Init.Prelude;           expect "a lean that cannot say its version is refused" 1 "lean --version failed"
rm -rf -- "${td:?}/elan"
fake_toolchain v4.30.0-rc2 4.30.0 >/dev/null
run --toolchain v4.30.0-rc2 --module Init.Prelude;           expect "a toolchain dir holding another Lean is refused" 1 "reason=toolchain-version-mismatch"
rm -rf -- "${td:?}/elan"
fake_toolchain v4.31.0 4.31.0 not-a-hash >/dev/null
run --toolchain v4.31.0 --module Init.Prelude;               expect "an unreadable githash is refused" 1 "reason=toolchain-githash-unreadable"
fake_toolchain v4.32.1 >/dev/null
run --toolchain v4.32.1 --module Init.Prelude;               expect "a toolchain with no pinned lean4export tag (v4.32.1) is refused" 1 "reason=no-pinned-exporter-commit"
fake_toolchain v4.30.0-rc2 4.30.0-rc2 "$GH" >/dev/null
run --toolchain v4.30.0-rc2 --module Init.Prelude;           expect "a toolchain whose githash is not its tag's pin is refused" 1 "reason=toolchain-githash-mismatch"
fake_toolchain v4.35.0-rc2 4.35.0-rc2 "$GH" bundled >/dev/null
run --toolchain v4.35.0-rc2 --module Init.Prelude;           expect "a bundled toolchain whose githash is not its tag's pin is refused" 1 "reason=toolchain-githash-mismatch"
fake_toolchain v4.37.0 4.37.0 "$GH" bundled >/dev/null
run --toolchain v4.37.0 --module Init.Prelude;               expect "a bundled toolchain with no pin row is refused" 1 "reason=no-pinned-lean-githash"
fake_toolchain v4.35.0-rc1 >/dev/null
run --toolchain v4.35.0-rc1 --module Init.Prelude;           expect "v4.35.0-rc1 is bundled: no bin/leanexport is refused" 1 "reason=bundled-exporter-missing"
run --toolchain v4.35.0-rc1 --module Init.Prelude --out "$td/nd2/x.ndjson"
[ "$RC" -eq 1 ] && [ ! -e "$td/nd2" ] && ok "a missing bundled exporter is refused before --out's directory is made" \
  || bad "missing leanexport with a new --out dir: rc=$RC, $(ls -d "$td/nd2" 2>&1)"
fake_toolchain v4.36.0-rc1 >/dev/null
run --toolchain v4.36.0-rc1 --module Init.Prelude;           expect "v4.36.0-rc1 without bin/leanexport is refused" 1 "reason=bundled-exporter-missing"
fake_toolchain v4.34.0 4.34.0 "" bundled >/dev/null
mkdir -p "$td/cache/lean4export/v4.34.0@076e8e57707e813375e8f9da8bf989799ace9680"
run --toolchain v4.34.0 --module Init.Prelude;               expect "v4.34.0 uses the pinned repo build, not a leanexport it ships" 1 "reason=exporter-commit-mismatch"
CACHE_UNDER_TEST="$HERE/../.lean-export-mint-selftest-cache"
run --toolchain v4.34.0 --module Init.Prelude; CACHE_UNDER_TEST=""
expect "a cache inside the repo is refused" 1 "reason=cache-inside-repo"
[ ! -e "$HERE/../.lean-export-mint-selftest-cache" ] && ok "the refused in-repo cache was not created" \
  || bad "the refused in-repo cache was created"
LEAN_EXPORT_MINT_PYTHON="$td/fakepy.sh" FAKE_PY_FAIL_VERB=inside FAKE_PY_FAIL_RC=70 run --toolchain v4.34.0 --module Init.Prelude
expect "a path check that crashes is refused as such, not as a cache inside the repo" 1 "reason=cache-check-failed"

# ── the pin table, and an exporter checkout (the functions, sourced) ──────────
pin_is() {  # <arm> <function> <tag> <want>
  lib "$2" "$3"
  if [ "$RC" -eq 0 ] && [ "$(cat "$td/stdout")" = "$4" ]; then ok "$1"; else bad "$1: '$(cat "$td/stdout")' rc=$RC"; fi
}
pin_is "v4.30.0-rc2 pins lean4export 12581a6b6" pinned_commit v4.30.0-rc2 12581a6b680d8478175596338eb2d53383a323e3
pin_is "v4.30.0-rc2 pins Lean 3dc1a088b" pinned_githash v4.30.0-rc2 3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc
pin_is "v4.28.0 pins Lean 7e01a1bf5" pinned_githash v4.28.0 7e01a1bf5c70fc6167d49c345d3bf80596e9a79b
pin_is "bundled v4.35.0 pins Lean eb6cafb72" pinned_githash v4.35.0 eb6cafb7290e8bd5f2937522d8d804f58f02bafc
pin_is "a bundled toolchain has no repo pin" pinned_commit v4.35.0 ""
pin_is "v4.32.1 (no lean4export tag) has no pin" pinned_githash v4.32.1 ""
sed -n "/<<'PINS'\$/,/^PINS\$/p" "$TOOL" | sed '1d;$d' >"$td/pins.txt"
python3 -I - "$td/pins.txt" >"$td/pins.check" 2>&1 <<'PY' && ok "every pin row is <tag> <lean4 sha> <lean4export sha, or - from v4.35.0-rc1>" || bad "pin table: $(cat "$td/pins.check")"
import re, sys
rows = [l.split() for l in open(sys.argv[1]) if l.strip()]
bad = [r for r in rows if len(r) != 3 or not re.fullmatch(r"v4\.\d+\.\d+(-rc\d+)?", r[0])
       or not re.fullmatch(r"[0-9a-f]{40}", r[1])
       or (int(r[0].split(".")[1]) >= 35) != (r[2] == "-")
       or (r[2] != "-" and not re.fullmatch(r"[0-9a-f]{40}", r[2]))]
tags = [r[0] for r in rows]
if len(set(tags)) != len(tags): bad.append("duplicate tag")
if len(rows) != 32: bad.append(f"{len(rows)} rows, not 32")
sys.exit(f"{bad}" if bad else 0)
PY
co="$td/co"; mkdir -p "$co"
printf 'leanprover/lean4:v4.30.0-rc2\n' >"$co/lean-toolchain"; printf 'def main := pure ()\n' >"$co/Main.lean"
git -C "$co" init -q && git -C "$co" add -A \
  && git -C "$co" -c core.hooksPath=/dev/null -c user.name=t -c user.email=t@t -c commit.gpgsign=false commit -qm fixture
head=$(git -C "$co" rev-parse HEAD)
lib check_checkout "$co" v4.30.0-rc2 "$head";                [ "$RC" -eq 0 ] && ok "the pinned, clean, matching checkout passes" || bad "a good checkout was refused: $(cat "$td/stderr")"
other=$(printf '%s' "$head" | tr '0-9a-f' '1-9a-f0')            # every digit differs
lib check_checkout "$co" v4.30.0-rc2 "$other";               expect "a checkout at another commit is refused" 1 "reason=exporter-commit-mismatch"
lib check_checkout "$td/elan" v4.30.0-rc2 "$head";           expect "a directory that is no checkout is refused" 1 "reason=exporter-commit-mismatch"
lib check_checkout "$co" v4.30.0 "$head";                    expect "an exporter whose lean-toolchain names another Lean is refused" 1 "reason=exporter-toolchain-mismatch"
printf 'def main := IO.println "x"\n' >"$co/Main.lean"
lib check_checkout "$co" v4.30.0-rc2 "$head";                expect "an edited checkout is refused" 1 "reason=exporter-checkout-modified"
git -C "$co" checkout -q -- Main.lean
cp -R "$co" "$td/co-badindex"; printf 'not an index' >"$td/co-badindex/.git/index"
lib check_checkout "$td/co-badindex" v4.30.0-rc2 "$head";  expect "a checkout git cannot read the status of is refused" 1 "git status failed"
cache="$td/rcache"; mkdir -p "$cache/lean4export"; cp -R "$co" "$cache/lean4export/v4.30.0-rc2@$head"
cdir="$cache/lean4export/v4.30.0-rc2@$head"; mkdir -p "$cdir/.lake/build/bin"
printf '#!/bin/sh\n' >"$cdir/.lake/build/bin/lean4export"; chmod +x "$cdir/.lake/build/bin/lean4export"
cached() { lib eval 'CACHE="'"$cache"'"; repo_exporter v4.30.0-rc2 /nonexistent '"$head"' && echo "$EXPORTER" && echo "$EXPORTER_FROM"'; }
cached;                                                      expect "a cached build with no build stamp is refused" 1 "reason=cached-exporter-unbuilt"
printf 'binary_sha256 %s\n' "$(sha "$cdir/.lake/build/bin/lean4export")" >"$cdir/.mint-built"
cached
[ "$RC" -eq 0 ] && [ "$(sed -n 1p "$td/stdout")" = "$cdir/.lake/build/bin/lean4export" ] && ok "an intact cached build is used without a fetch" \
  || bad "an intact cached build was not used (rc=$RC: $(cat "$td/stderr"))"
[ "$(sed -n 2p "$td/stdout")" = https://github.com/leanprover/lean4export ] && ok "a build stamp with no repo line was fetched from upstream" \
  || bad "a stamp with no repo line reads repo '$(sed -n 2p "$td/stdout")'"
good=$(sha "$cdir/.lake/build/bin/lean4export")
LEAN_EXPORT_MINT_PYTHON="$td/shafail.sh" cached
expect1 "a cached build whose binary cannot be hashed is refused as such, not as tampered" 1 "reason=exporter-hash-failed hashing $cdir/.lake/build/bin/lean4export"
FAKE_SHA=garbage LEAN_EXPORT_MINT_PYTHON="$td/shafail.sh" cached
expect1 "... and so is a hash that is no sha256" 1 "reason=exporter-hash-failed hashing $cdir/.lake/build/bin/lean4export gave 'not-a-sha256', not a sha256"
FAKE_SHA=late LEAN_EXPORT_MINT_PYTHON="$td/shafail.sh" cached
expect1 "... and so is a hasher that printed the right sha256 and then failed" 1 "reason=exporter-hash-failed hashing $cdir/.lake/build/bin/lean4export failed (exit 1)"
printf 'binary_sha256 \n' >"$cdir/.mint-built"
cached;                                                      expect1 "a build stamp with an empty sha256 is malformed, not a tampered binary" 1 "reason=cached-exporter-stamp-malformed"
LEAN_EXPORT_MINT_PYTHON="$td/shafail.sh" cached
expect1 "... also when the binary cannot be hashed either: an empty hash matches nothing" 1 "reason=cached-exporter-stamp-malformed"
printf 'binary_sha256 %s\n' "${good%?}" >"$cdir/.mint-built"
cached;                                                      expect1 "a build stamp whose sha256 is 63 digits is malformed" 1 "reason=cached-exporter-stamp-malformed"
printf 'binary_sha256 %s\nbinary_sha256 %s\n' "$good" "$good" >"$cdir/.mint-built"
cached;                                                      expect1 "a build stamp with two sha256 lines is malformed" 1 "reason=cached-exporter-stamp-malformed"
printf 'binary_sha256 %s\n' "$good" >"$cdir/.mint-built"
printf '#!/bin/sh\necho swapped\n' >"$cdir/.lake/build/bin/lean4export"
cached;                                                      expect "a cached binary that is not the one built is refused" 1 "reason=cached-exporter-tampered"

# ── fetch, build and publish, end to end (main, sourced; the pin -> the fixture) ─
repo_lane() {  # <main args>...: main with v4.30.0-rc2's lean4export pin replaced by $PIN_UNDER_TEST
  : >"$td/gate.log"
  ( export TMPDIR="$td/tmp" ELAN_HOME="$td/elan" LEAN_EXPORT_MINT_CACHE="${LCACHE_UNDER_TEST:-$td/lcache}" \
           LEAN_EXPORT_MINT_HEAVY_GATE="${GATE_UNDER_TEST:-$td/fakegate.sh}" \
           GATE_LOG="$td/gate.log" MINT_SELFTEST_CANARY=leaked LEAN_EXPORT_MINT_EXPORTER_REPO="$URL_UNDER_TEST"
    LEAN_EXPORT_MINT_LIB=1; . "$TOOL"
    pinned_commit() { [ "$1" != v4.30.0-rc2 ] || printf '%s\n' "$PIN_UNDER_TEST"; }
    main "$@" ) >"$td/stdout" 2>"$td/stderr" </dev/null
  RC=$?
}
mkfix() {  # <dir> <lean-toolchain line>: a one-commit lean4export stand-in tagged v4.30.0-rc2; prints its commit
  mkdir -p "$1"
  printf '%s\n' "$2" >"$1/lean-toolchain"; printf 'def main := pure ()\n' >"$1/Main.lean"
  git -C "$1" init -q && git -C "$1" add -A \
    && git -C "$1" -c core.hooksPath=/dev/null -c user.name=t -c user.email=t@t -c commit.gpgsign=false commit -qm fixture \
    && git -C "$1" tag v4.30.0-rc2 && git -C "$1" config uploadpack.allowAnySHA1InWant true \
    && git -C "$1" rev-parse HEAD
}
rm -rf -- "${td:?}/elan"
tc30=$(fake_toolchain v4.30.0-rc2)
FIX=$(mkfix "$td/l4e" 'leanprover/lean4:v4.30.0-rc2')
PIN_UNDER_TEST=$FIX; NOWHERE="file://$td/no-such-repo"; URL_UNDER_TEST=$NOWHERE
bdir="$td/lcache/lean4export/v4.30.0-rc2@$FIX"
fresh() { rm -rf -- "${td:?}/lcache"; rm -f -- "${tc30:?}/lake.log" "${tc30:?}/lake.conf"; }
lake_mode() { printf 'FAKE_LAKE=%s\n' "$1" >"$tc30/lake.conf"; }
no_partials() {  # <arm>: no partial checkout and no lock beside the published builds
  if [ -z "$(ls "$td/lcache/lean4export" 2>/dev/null | grep -e '\.partial\.' -e '\.lock$')" ]; then ok "$1"
  else bad "$1: $(ls "$td/lcache/lean4export")"; fi
}
fresh
repo_lane --toolchain v4.30.0-rc2 --module Init.Prelude --out /dev/null/x.ndjson; expect "an --out whose directory cannot be made is refused before any fetch" 1 "reason=out-unwritable cannot create"
mkdir -p "$td/ro"; chmod 555 "$td/ro"
repo_lane --toolchain v4.30.0-rc2 --module Init.Prelude --out "$td/ro/x.ndjson"; expect "an --out in a read-only directory is refused before any fetch" 1 "reason=out-unwritable $td/ro"
chmod 755 "$td/ro"
: >"$td/pre.ndjson"
repo_lane --toolchain v4.30.0-rc2 --module Init.Prelude --out "$td/pre.ndjson"; expect "an existing --out is refused before any fetch" 1 "reason=out-exists"
: >"$td/pre2.ndjson.sidecar.json"
repo_lane --toolchain v4.30.0-rc2 --module Init.Prelude --out "$td/pre2.ndjson"; expect "an existing sidecar beside --out is refused too" 1 "reason=out-exists"
repo_lane --toolchain v4.30.0-rc2 --module Mathlib.Order.Basic --out "$td/m.ndjson"; expect "an unmeasured non-core mint class is refused before any fetch" 1 "reason=gate-weight-unseen"
[ ! -e "$td/lcache/lean4export" ] && ok "nothing was fetched for a refused --out or reservation" || bad "a refused run reached the fetch"
repo_lane --toolchain v4.30.0-rc2 --module Mathlib.Order.Basic --out "$td/newdir/sub/m.ndjson"
expect "a refused reservation is refused before --out's directory is made" 1 "reason=gate-weight-unseen"
[ ! -e "$td/newdir" ] && ok "... and that directory is not made" || bad "the refused run made $(find "$td/newdir" 2>/dev/null | head -3)"
mkdir -p "$td/rocache"; chmod 555 "$td/rocache"; URL_UNDER_TEST="file://$td/l4e"
LCACHE_UNDER_TEST="$td/rocache/c" repo_lane --toolchain v4.30.0-rc2 --module Init.Prelude --out "$td/r.ndjson"
expect "an exporter build cache that cannot be made is refused by name" 1 "reason=cache-unwritable cannot create $td/rocache/c/lean4export, the exporter build cache"
chmod 755 "$td/rocache"; mkdir -p "$td/rocache/c/lean4export"; chmod 555 "$td/rocache/c/lean4export"
LCACHE_UNDER_TEST="$td/rocache/c" repo_lane --toolchain v4.30.0-rc2 --module Init.Prelude --out "$td/r.ndjson"
expect "a build cache that holds no room for a checkout is refused by name" 1 "reason=cache-unwritable cannot create $td/rocache/c/lean4export/v4.30.0-rc2@"
chmod 755 "$td/rocache/c/lean4export"; URL_UNDER_TEST=$NOWHERE
repo_lane --toolchain v4.30.0-rc2 --module Init.Prelude --out "$td/r.ndjson"; expect "a repo ls-remote cannot read is refused" 1 "reason=exporter-fetch-failed git ls-remote"
URL_UNDER_TEST="file://$td/l4e"
printf 'news\n' >"$td/l4e/NEWS"; git -C "$td/l4e" add NEWS \
  && git -C "$td/l4e" -c core.hooksPath=/dev/null -c user.name=t -c user.email=t@t -c commit.gpgsign=false commit -qm moved \
  && git -C "$td/l4e" tag -f v4.30.0-rc2 >/dev/null 2>&1
repo_lane --toolchain v4.30.0-rc2 --module Init.Prelude --out "$td/r.ndjson"; expect "a tag the remote has moved off the pin is refused" 1 "reason=exporter-tag-moved"
[ ! -e "$tc30/lake.log" ] && [ ! -e "$td/lcache/lean4export" ] && ok "a moved tag is refused before anything is fetched or built" || bad "a moved tag was fetched or built"
git -C "$td/l4e" tag -f v4.30.0-rc2 "$FIX" >/dev/null 2>&1
cp -R "$td/l4e" "$td/l4e-broken"; tree=$(git -C "$td/l4e-broken" rev-parse "$FIX^{tree}")
tree=${tree:?}; rm -f -- "${td:?}/l4e-broken/.git/objects/${tree:0:2}/${tree:2}"
URL_UNDER_TEST="file://$td/l4e-broken"; fresh
repo_lane --toolchain v4.30.0-rc2 --module Init.Prelude --out "$td/r.ndjson"; expect "a fetch that fails after ls-remote is refused" 1 "reason=exporter-fetch-failed git fetch"
no_partials "a failed fetch leaves no partial checkout"
FIX2=$(mkfix "$td/l4e-other" 'leanprover/lean4:v4.30.0')
URL_UNDER_TEST="file://$td/l4e-other"; PIN_UNDER_TEST=$FIX2; fresh
repo_lane --toolchain v4.30.0-rc2 --module Init.Prelude --out "$td/r.ndjson"; expect "a fetched lean4export made for another Lean is refused" 1 "reason=exporter-toolchain-mismatch"
[ ! -e "$tc30/lake.log" ] && ok "... before it is built" || bad "a lean4export made for another Lean was built"
URL_UNDER_TEST="file://$td/l4e"; PIN_UNDER_TEST=$FIX
fresh; lake_mode fail
repo_lane --toolchain v4.30.0-rc2 --module Init.Prelude --out "$td/r.ndjson"; expect "a lake build that exits nonzero is refused, binary or not" 1 "exited 1 (the partial checkout"
[ ! -e "$bdir" ] && ok "a failed build is not published" || bad "a failed build was published"
[ -n "$(ls "$td/lcache/lean4export" | grep '\.partial\.')" ] && ok "a failed build's checkout is kept for inspection" \
  || bad "the failed build's checkout was removed: $(ls "$td/lcache/lean4export")"
fresh; lake_mode nobin
repo_lane --toolchain v4.30.0-rc2 --module Init.Prelude --out "$td/r.ndjson"; expect "a lake build that writes no binary is refused" 1 "exited 0 and wrote no .lake/build/bin/lean4export"
fresh; lake_mode modify
repo_lane --toolchain v4.30.0-rc2 --module Init.Prelude --out "$td/r.ndjson"; expect "a build that edits a tracked file is refused" 1 "reason=exporter-checkout-modified"
[ ! -e "$bdir" ] && ok "a modified checkout is not published" || bad "a modified checkout was published"
no_partials "a checkout its build modified is removed"
fresh; lake_mode stampdir
repo_lane --toolchain v4.30.0-rc2 --module Init.Prelude --out "$td/r.ndjson"; expect "a build stamp that cannot be written is refused by name" 1 "reason=cache-unwritable cannot write the build stamp"
[ ! -e "$bdir" ] && ok "a build with no stamp is not published" || bad "a build with no stamp was published"
no_partials "a build whose stamp cannot be written leaves no partial checkout"
fresh; lake_mode ok
FAKE_GATE_RC=75 repo_lane --toolchain v4.30.0-rc2 --module Init.Prelude --out "$td/r.ndjson"
expect "a build the gate refuses (a small box, exit 75) is a gate refusal, not a failed build" 1 "reason=gate-refused heavy_gate refused lean-export-build"
[ ! -e "$tc30/lake.log" ] && ok "... and lake never ran" || bad "lake ran under a refused reservation"
no_partials "a refused build reservation leaves no partial checkout"
fresh; lake_mode race
repo_lane --toolchain v4.30.0-rc2 --module Init.Prelude --out "$td/r.ndjson"; expect "a build another run published unfinished meanwhile is checked, not trusted" 1 "reason=exporter-commit-mismatch"
no_partials "the run that lost the publish discards its own checkout"
fresh; lake_mode ok; mkdir -p "$bdir.lock"; echo $$ >"$bdir.lock/owner"
LEAN_EXPORT_MINT_LOCK_WAIT=0 repo_lane --toolchain v4.30.0-rc2 --module Init.Prelude --out "$td/r.ndjson"
expect "a build is not published while a live run holds the cache lock" 1 "reason=exporter-cache-locked"
[ -d "$bdir.lock" ] && [ "$(cat "$bdir.lock/owner")" = $$ ] && [ ! -e "$bdir" ] && ok "a live run's lock is left alone, and nothing is published" \
  || bad "the held lock: $(ls "$td/lcache/lean4export")"
[ -z "$(ls "$td/lcache/lean4export" | grep '\.partial\.')" ] && ok "the refused publish leaves no partial checkout" \
  || bad "the refused publish left: $(ls "$td/lcache/lean4export")"
fresh; lake_mode ok; mkdir -p "$bdir.lock"; echo 1 >"$bdir.lock/owner"
LEAN_EXPORT_MINT_LOCK_WAIT=0 repo_lane --toolchain v4.30.0-rc2 --module Init.Prelude --out "$td/r.ndjson"
expect "a lock held by another user's live process (pid 1) is waited for" 1 "reason=exporter-cache-locked"
[ "$(cat "$bdir.lock/owner" 2>/dev/null)" = 1 ] && [ ! -e "$bdir" ] && ok "... and left alone: kill -0 fails on pid 1, /bin/ps does not" \
  || bad "pid 1's lock: $(ls "$td/lcache/lean4export")"
# A ps on PATH that answers "no such process" (exit 1, nothing printed) for
# any pid, a live one included: only /bin/ps may speak for the owner.
mkdir -p "$td/psshim"; printf '#!/bin/sh\nexit 1\n' >"$td/psshim/ps"; chmod +x "$td/psshim/ps"
fresh; lake_mode ok; mkdir -p "$bdir.lock"; echo $$ >"$bdir.lock/owner"
PATH="$td/psshim:$PATH" LEAN_EXPORT_MINT_LOCK_WAIT=0 repo_lane --toolchain v4.30.0-rc2 --module Init.Prelude --out "$td/r2.ndjson"
expect "a live owner's lock is waited for when PATH's ps calls it gone: /bin/ps reads the owner" 1 "reason=exporter-cache-locked"
[ "$(cat "$bdir.lock/owner" 2>/dev/null)" = $$ ] && [ ! -e "$bdir" ] && ok "... and that lock is left alone" \
  || bad "the live lock under a failing ps: $(ls "$td/lcache/lean4export")"
verdict_is() {  # <arm> <want> <pid> <ps exit status> <ps output>
  lib ps_verdict "$3" "$4" "$5"
  if [ "$RC" -eq 0 ] && [ "$(cat "$td/stdout")" = "$2" ]; then ok "$1"; else bad "$1: '$(cat "$td/stdout")' rc=$RC $(cat "$td/stderr")"; fi
}
verdict_is "ps exiting 1 with no output: the pid has no process (gone)" gone 4242 1 ""
verdict_is "ps exiting 1 with an error: not known, so the lock is waited for" unknown 4242 1 "ps: sysctl: Operation not permitted"
verdict_is "ps exiting 2: not known" unknown 4242 2 ""
verdict_is "a ps that cannot run (127): not known" unknown 4242 127 ""
verdict_is "ps printing the pid: alive" alive 4242 0 "  4242"
verdict_is "ps printing another pid: not known" unknown 4242 0 " 4243"
verdict_is "ps exiting 0 with no output: not known" unknown 4242 0 ""
sh -c 'exit 0' & gone=$!; wait "$gone"
lib owner_state "$gone"; [ "$(cat "$td/stdout")" = gone ] && ok "/bin/ps reads a reaped pid as gone" || bad "owner_state $gone: $(cat "$td/stdout" "$td/stderr")"
lib owner_state 1; [ "$(cat "$td/stdout")" = alive ] && ok "... and pid 1 as alive" || bad "owner_state 1: $(cat "$td/stdout" "$td/stderr")"
fresh; lake_mode ok; sh -c 'exit 0' & gone=$!; wait "$gone"
mkdir -p "$bdir.lock"; echo "$gone" >"$bdir.lock/owner"
LEAN_EXPORT_MINT_LOCK_WAIT=0 repo_lane --toolchain v4.30.0-rc2 --module Init.Prelude --out "$td/rs.ndjson"
[ "$RC" -eq 0 ] && grep -qF "left by pid $gone, which is gone" "$td/stderr" && [ -d "$bdir" ] && ok "a lock whose owner process is gone is removed and the build published" \
  || bad "the stale lock: rc=$RC $(cat "$td/stderr") $(ls "$td/lcache/lean4export")"
no_partials "... leaving no lock and no partial checkout"
fresh; lake_mode ok
FAKE_PLANT_AT="$bdir" FAKE_PLANT=file PATH="$td/mvshim:$PATH" LEAN_EXPORT_MINT_PYTHON="$td/fakepy.sh" \
  repo_lane --toolchain v4.30.0-rc2 --module Init.Prelude --out "$td/r3.ndjson"
expect1 "a publish whose rename fails (a file appeared at the build's path) is refused by name" 1 "reason=cache-publish-failed cannot rename"
[ "$(cat "$bdir" 2>/dev/null)" = planted ] && ok "... nothing is published over it" || bad "a failed rename published $bdir"
no_partials "... and the EXIT trap drops the lock it held and the partial checkout"
fresh; lake_mode ok
LEAN_EXPORT_MINT_PYTHON="$td/fakepy.sh" FAKE_PY_FAIL_VERB=rename FAKE_PY_FAIL_RC=70 \
  repo_lane --toolchain v4.30.0-rc2 --module Init.Prelude --out "$td/r4.ndjson"
expect1 "a rename step that crashes is refused as such" 1 "reason=cache-publish-failed the rename of"
no_partials "... leaving no lock and no partial checkout"
LEAN_EXPORT_MINT_PYTHON="$td/fakepy.sh" FAKE_PY_FAIL_VERB=rename FAKE_PY_FAIL_RC=0 \
  repo_lane --toolchain v4.30.0-rc2 --module Init.Prelude --out "$td/r5.ndjson"
expect1 "a rename step that answers neither placed nor exists is refused" 1 "answered ''"
fresh; lake_mode ok
LEAN_EXPORT_MINT_PYTHON="$td/shafail.sh" repo_lane --toolchain v4.30.0-rc2 --module Init.Prelude --out "$td/r6.ndjson"
expect1 "a build whose binary cannot be hashed is refused before its stamp is written" 1 "reason=exporter-hash-failed hashing"
[ ! -e "$bdir" ] && ok "... and is not published (an empty sha256 in a stamp made the next run call it tampered)" \
  || bad "a build with no hash was published: $(cat "$bdir/.mint-built" 2>/dev/null)"
no_partials "... leaving no lock and no partial checkout"
fresh; lake_mode ok
repo_lane --toolchain v4.30.0-rc2 --module Init.Prelude --lean-path /some/project/lib --out "$td/lp.ndjson"
[ "$RC" -eq 0 ] && grep -qx 'LEAN_PATH=' "$tc30/lake.env" && grep -qx 'LEAN_PATH=/some/project/lib' "$tc30/env.log" \
  && ok "--lean-path reaches the exporter and not the cached exporter's build" \
  || bad "--lean-path: rc=$RC lake $(grep LEAN_PATH "$tc30/lake.env") exporter $(grep LEAN_PATH "$tc30/env.log")"
fresh; lake_mode ok; printf 'FAKE_PROBE=%s\n' "$bdir.lock" >>"$tc30/fake.conf"
repo_lane --toolchain v4.30.0-rc2 --module Init.Prelude --out "$td/rl.ndjson"
[ "$(cat "$tc30/probe.log" 2>/dev/null)" = absent ] && ok "the cache lock is dropped once the build is published, before the mint" || bad "lock during the mint: $(cat "$tc30/probe.log" 2>/dev/null)"
[ "$RC" -eq 0 ] && grep -q '^LEAN_EXPORT_MINT=ok ' "$td/stdout" && [ -s "$td/rl.ndjson" ] && ok "a fresh fetch and build mints" \
  || bad "the fresh repo mint failed (rc=$RC: $(cat "$td/stderr"))"
sidecar_has "the sidecar names the repo the build fetched from, the tag, the commit and the built binary" "$td/rl.ndjson.sidecar.json" \
  "{\"exporter!\": {\"kind\": \"lean4export-repo\", \"repo\": \"file://$td/l4e\", \"tag\": \"v4.30.0-rc2\", \"commit\": \"$FIX\", \"binary_sha256\": \"$(sha "$bdir/.lake/build/bin/lean4export")\"}, \"lean_githash\": \"$(pin_gh v4.30.0-rc2)\"}"
grep -qx 'run auto:lean-export-build:6 lean-export-build -- .*' "$td/gate.log" && ok "the build reserves auto:lean-export-build:6" || bad "gate log: $(cat "$td/gate.log")"
grep -qx 'build lean4export' "$tc30/lake.log" && grep -qx "LEAN_SYSROOT=$tc30" "$tc30/lake.env" && grep -q "^PATH=$tc30/bin:" "$tc30/lake.env" \
  && grep -qx 'CANARY=' "$tc30/lake.env" && grep -q "^PWD=$bdir\.partial\." "$tc30/lake.env" \
  && ok "lake builds lean4export in the partial checkout, under the toolchain's env -i" || bad "lake: $(cat "$tc30/lake.log" "$tc30/lake.env")"
grep -qx "repo file://$td/l4e" "$bdir/.mint-built" && ok "the build stamp records the repo URL" || bad "stamp: $(cat "$bdir/.mint-built")"
grep -qx "binary_sha256 $(sha "$bdir/.lake/build/bin/lean4export")" "$bdir/.mint-built" && ok "the build stamp records the binary's sha256" \
  || bad "stamp: $(cat "$bdir/.mint-built")"
no_partials "publishing leaves no partial checkout and no lock"
cp -R "$bdir" "$td/refbuild"   # a finished build, as another run would publish it
URL_UNDER_TEST=$NOWHERE; rm -f -- "${tc30:?}/lake.log"
repo_lane --toolchain v4.30.0-rc2 --module Init.Prelude --out "$td/rl2.ndjson"
[ "$RC" -eq 0 ] && [ ! -e "$tc30/lake.log" ] && ! grep -q 'lean-export-build' "$td/gate.log" && ok "the published build is reused: no fetch, no build" \
  || bad "the reuse: rc=$RC $(cat "$td/stderr")"
sidecar_has "a reused build's sidecar names the repo its stamp records" "$td/rl2.ndjson.sidecar.json" "{\"exporter\": {\"repo\": \"file://$td/l4e\"}}"
URL_UNDER_TEST="file://$td/l4e"; fresh
git -C "$td/l4e" -c tag.gpgsign=false -c user.name=t -c user.email=t@t tag -f -a -m annotated v4.30.0-rc2 "$FIX" >/dev/null 2>&1
repo_lane --toolchain v4.30.0-rc2 --module Init.Prelude --out "$td/rl3.ndjson"
[ "$RC" -eq 0 ] && ok "an annotated tag is read peeled, as its commit" || bad "annotated tag: rc=$RC $(cat "$td/stderr")"
# Two runs that both removed one stale lock both publish: the second's publish
# step meets the first's finished build (planted just before it).
fresh; lake_mode ok
FAKE_PLANT_AT="$bdir" FAKE_PLANT="copy:$td/refbuild" PATH="$td/mvshim:$PATH" LEAN_EXPORT_MINT_PYTHON="$td/fakepy.sh" \
  repo_lane --toolchain v4.30.0-rc2 --module Init.Prelude --out "$td/rr.ndjson"
[ "$RC" -eq 0 ] && [ -f "$bdir/.mint-built" ] && [ -z "$(ls -A "$bdir" | grep '\.partial\.')" ] \
  && ok "a build another run publishes just before this run's publish is used, and this checkout is not nested inside it" \
  || bad "the publish race: rc=$RC $(ls -A "$bdir" 2>&1 | tr '\n' ' ') $(head -c 300 "$td/stderr")"
no_partials "... and this run's own checkout is discarded"
# The third re-review's probe P5: an unmeasured Mathlib class, --gate-gb 40, and
# another Mathlib mint completing under the class (peak 6.00 GB) while this
# run's exporter builds. Asked only before the fetch, the class read unmeasured
# and the mint reserved auto:<class>:40, which then resolved to 8 GB.
hgb="$td/hgb"; mkdir -p "$hgb"; fresh
printf 'printf "%%s lean-export-mint-Mathlib reserved=8 peak_gb=6.00 pct=75 dur=1m00s rc=0 class=lean-export-mint-Mathlib\\n" 2026-10-28T00:00:00Z >>%s\nFAKE_LAKE=ok\n' \
  "$hgb/peaks.log" >"$tc30/lake.conf"
HEAVY_GATE_DIR="$hgb" HEAVY_GATE_PHYS_GB=128 GATE_UNDER_TEST="$td/resolvergate.sh" \
  repo_lane --toolchain v4.30.0-rc2 --module Mathlib.Order.Basic --gate-gb 40 --out "$td/mb.ndjson"
[ "$RC" -eq 0 ] && grep -qx 'run 40 lean-export-mint-Mathlib GB=40 CLASS=' "$td/gate.log" \
  && ok "a class measured while the exporter builds takes the measured rule: --gate-gb 40 is an explicit 40 GB, not auto: at 8" \
  || bad "class measured during the build: rc=$RC $(cat "$td/gate.log") $(head -c 300 "$td/stderr")"
sidecar_has "... and the sidecar records the weight and the 40 GB heavy_gate reserved" "$td/mb.ndjson.sidecar.json" \
  '{"gate": {"weight": "40", "reserved_gb": 40, "label": "lean-export-mint-Mathlib"}}'
lake_mode ok

# ── the export check, on synthetic NDJSON (the python half, sourced) ──────────
M='{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"},"lean":{"githash":"'$GH'","version":"4.30.0-rc2"}}}'
R='{"in":1,"str":{"pre":0,"str":"Nat"}}'
meta() {  # <arm> <rc> <needle> <file contents> [<decl>...]
  local arm=$1 want=$2 needle=$3
  printf '%s' "$4" >"$td/m.ndjson"; shift 4
  lib py meta "$td/m.ndjson" 4.30.0-rc2 3.1.0 "$GH" lean4export "$@"
  expect "$arm" "$want" "$needle"
}
v() { printf '%s\n%s\n' "$(printf '%s' "$M" | sed "$1")" "$R"; }
line() { printf '%s\n%s\n%s' "$M" "$R" "$1"; }   # the meta line, a name, then <record> (the caller adds its newline)
RD='{"axiom":{"name":1}}'
meta "the reader's shape at 4.30.0-rc2 / 3.1.0 passes" 0 "" "$M"$'\n'"$R"$'\n'"$RD"$'\n'
grep -qF '"version":"4.30.0-rc2"' "$td/stdout" && ok "the parsed meta is printed" || bad "no parsed meta on stdout"
meta "an export whose last record is a name, cut at a line boundary, is refused" 65 \
  "reason=export-truncated the last record (line 2) is a 'in' primitive" "$M"$'\n'"$R"$'\n'
meta "... and one whose last record is an expression after a declaration" 65 \
  "reason=export-truncated the last record (line 4) is a 'ie' primitive" "$M"$'\n'"$R"$'\n'"$RD"$'\n''{"ie":0,"sort":1}'$'\n'
meta "another Lean version is refused" 65 "reason=meta-lean-version-mismatch" "$(v 's/"4.30.0-rc2"/"4.30.0"/')"$'\n'
meta "format 3.1.1 is not 3.1.0" 65 "reason=meta-format-mismatch" "$(v 's/"format":{"version":"3.1.0"}/"format":{"version":"3.1.1"}/')"$'\n'
meta "another githash is refused" 65 "reason=meta-githash-mismatch" "$(v "s/$GH/${GH%?}9/")"$'\n'
meta "another exporter is refused" 65 "reason=meta-exporter-mismatch" "$(v 's/"name":"lean4export"/"name":"leanchecker"/')"$'\n'
meta "an extra top-level key is malformed" 65 "reason=meta-malformed" "$(v 's/}}}$/}},"x":1}/')"$'\n'
meta "a missing meta.lean.githash is malformed" 65 "reason=meta-malformed" "$(v "s/\"githash\":\"$GH\",//")"$'\n'
meta "a duplicate key is malformed" 65 "reason=meta-malformed" "$(v 's/"name":"lean4export",/"name":"lean4export","name":"lean4export",/')"$'\n'
meta "a non-string version is malformed" 65 "reason=meta-malformed" "$(v 's/"format":{"version":"3.1.0"}/"format":{"version":3}/')"$'\n'
meta "a first line that is not JSON is malformed" 65 "reason=meta-malformed" "{meta"$'\n'"$R"$'\n'
meta "an export with no complete first line is malformed" 65 "reason=meta-malformed" "$M"
meta "an export with only its meta line is empty" 65 "reason=export-empty" "$M"$'\n'
lib py meta "$td/no-such.ndjson" 4.30.0-rc2 3.1.0 "$GH" lean4export
expect "a check that crashes exits 70, which is neither a pass nor a refusal" 70 "the meta step crashed"
cat >"$td/allkinds.ndjson" <<'NDJSON'
{"in":1,"str":{"pre":0,"str":"Nat"}}
{"in":2,"num":{"pre":1,"i":2}}
{"il":1,"succ":0}
{"il":2,"param":1}
{"il":3,"max":[1,2]}
{"il":4,"imax":[1,2]}
{"ie":0,"sort":1}
{"ie":1,"bvar":0}
{"ie":2,"const":{"name":1,"us":[]}}
{"ie":3,"app":{"fn":2,"arg":1}}
{"ie":4,"lam":{"name":1,"type":0,"body":1,"binderInfo":"default"}}
{"ie":5,"forallE":{"name":1,"type":0,"body":0,"binderInfo":"implicit"}}
{"ie":6,"letE":{"name":1,"type":0,"value":2,"body":1,"nondep":false}}
{"ie":7,"proj":{"typeName":1,"idx":0,"struct":1}}
{"ie":8,"natVal":"12345678901234567890"}
{"ie":9,"strVal":"x"}
{"ie":10,"mdata":{"expr":1,"data":{}}}
{"axiom":{"name":1,"levelParams":[],"type":0,"isUnsafe":false}}
{"def":{"name":1,"levelParams":[],"type":0,"value":1,"hints":"abbrev","safety":"safe","all":[1]}}
{"thm":{"name":1,"levelParams":[],"type":0,"value":1,"all":[1]}}
{"opaque":{"name":1,"levelParams":[],"type":0,"value":1,"isUnsafe":false,"all":[1]}}
{"quot":{"name":1,"levelParams":[],"type":0,"kind":"type"}}
{"inductive":{"types":[{"name":1}],"ctors":[{"name":2}],"recs":[]}}
NDJSON
meta "every record kind the front door reads passes" 0 "" "$M"$'\n'"$(cat "$td/allkinds.ndjson")"$'\n'
meta "a cut-off last record is refused, not shortened" 65 "reason=export-truncated line 3" "$M"$'\n'"$R"$'\n''{"in":2,"str":{"pre":1,"str":"ad'
meta "a complete last record without its newline is refused" 65 "reason=export-truncated line 2" "$M"$'\n'"$R"
meta "a later line that is not JSON is malformed" 65 "reason=export-malformed line 3 does not parse" "$(line '{"in":2,')"$'\n'
meta "a blank line is malformed" 65 "reason=export-malformed line 3 does not parse" "$M"$'\n'"$R"$'\n'$'\n'"$R"$'\n'
meta "a later line with a duplicate key is malformed" 65 "reason=export-malformed line 3 does not parse" "$(line '{"in":2,"in":3}')"$'\n'
meta "a JSON array is malformed" 65 "reason=export-malformed line 3 is a JSON list" "$(line '[1,2]')"$'\n'
meta "an unknown one-key record is malformed" 65 "which is no declaration kind" "$(line '{"ctor":{"name":1}}')"$'\n'
meta "a declaration whose value is no object is malformed" 65 "is a def record whose value is not an object" "$(line '{"def":3}')"$'\n'
meta "two keys with no primitive table are malformed" 65 "a primitive has exactly one of" "$(line '{"str":1,"pre":2}')"$'\n'
meta "two primitive tables in one record are malformed" 65 "a primitive has exactly one of" "$(line '{"in":2,"il":2}')"$'\n'
meta "a string index is malformed" 65 "which is not an index" "$(line '{"in":"2","str":{"pre":1,"str":"a"}}')"$'\n'
meta "a boolean index is malformed" 65 "which is not an index" "$(line '{"il":true,"succ":0}')"$'\n'
meta "an unknown primitive variant is malformed" 65 "of kind 'lit', not one of" "$(line '{"ie":3,"lit":{}}')"$'\n'
meta "a record with three keys is malformed" 65 "has 3 keys" "$(line '{"in":2,"str":{"pre":1,"str":"a"},"x":1}')"$'\n'
meta "an inductive whose types is no list is malformed" 65 "whose 'types' is not a list of objects" "$(line '{"inductive":{"types":3,"ctors":[],"recs":[]}}')"$'\n'
meta "a declaration named by a string, not an index, is malformed" 65 "declaring the name 'Nat', which is not an index" "$(line '{"def":{"name":"Nat"}}')"$'\n'
D="$(cat "$tc30/body.ndjson")"$'\n'
meta "--decl finds a def, a constructor, a recursor and a type" 0 "" "$M"$'\n'"$D" Nat.add Nat.succ Nat.rec Nat
meta "--decl of a name only in the name table is refused" 65 "reason=decl-not-exported the export has no declaration record for ['Nat.lt']" "$M"$'\n'"$D" Nat.add Nat.lt
meta "--decl of an absent name is refused by name" 65 "for ['Unsafe.thing']" "$M"$'\n'"$D" Unsafe.thing
Q="$D"'{"in":7,"str":{"pre":1,"str":"a.b"}}'$'\n''{"axiom":{"name":7}}'$'\n''{"in":8,"num":{"pre":1,"i":2}}'$'\n''{"thm":{"name":8}}'$'\n'
meta "--decl reads «» as the exporter does, and a numeric component" 0 "" "$M"$'\n'"$Q" 'Nat.«a.b»' Nat.2
meta "--decl Nat.a.b is not Nat.«a.b»" 65 "for ['Nat.a.b']" "$M"$'\n'"$Q" Nat.a.b
mkdir -p "$td/arena"
if tar -xzf "$ARENA" -C "$td/arena" good/init-prelude.ndjson 2>"$td/tar.err"; then
  lib py meta "$td/arena/good/init-prelude.ndjson" 4.29.1 3.1.0 f72c35b3f637c8c6571d353742168ab66cc22c00 lean4export \
    Nat Nat.succ Nat.rec Nat.add Eq.refl Quot.mk
  expect "a real lean4export export (the arena's Init.Prelude, 4.29.1) passes the record and --decl checks" 0 ""
  lib py meta "$td/arena/good/init-prelude.ndjson" 4.29.1 3.1.0 f72c35b3f637c8c6571d353742168ab66cc22c00 lean4export Nat.add Nat.addd
  expect "... and a name it does not declare is refused" 65 "for ['Nat.addd']"
else bad "the vendored arena archive did not extract: $(cat "$td/tar.err")"; fi
printf '%s\n%s\n' "$M" "$R" >"$td/s.ndjson"
( LEAN_EXPORT_MINT_LIB=1; . "$TOOL"
  MINT_SCRIPT="$TOOL" MINT_REPO_ROOT="$td" MINT_TOOLCHAIN=v4.30.0-rc2 MINT_TCDIR="$td/tc" MINT_GITHASH=$GH MINT_BANNER=b \
  MINT_KIND=k MINT_REPO=r MINT_TAG=t MINT_COMMIT=c MINT_OUT_NAME=s.ndjson MINT_META='{}' MINT_GATE_SCRIPT="$td/fakegate.sh" \
  MINT_GATE_LABEL=l MINT_GATE_WEIGHT=w \
    py sidecar "$td/s.ndjson" "$td/s.sidecar" env -i "HOME=/h" "TMPDIR=/t" "PATH=$td/tc/bin:/bin" "LEAN_PATH=$td/tc/lib:/x" \
      --cmd "$td/fakegate.sh" Init -- X ) >"$td/stdout" 2>"$td/stderr"
( LEAN_EXPORT_MINT_LIB=1; . "$TOOL"
  MINT_SCRIPT="$TOOL" MINT_REPO_ROOT="$td" MINT_TOOLCHAIN=v4.30.0-rc2 MINT_TCDIR="$td/tc" MINT_GITHASH=$GH MINT_BANNER=b \
  MINT_KIND=k MINT_REPO=r MINT_TAG=t MINT_COMMIT=c MINT_OUT_NAME=s.ndjson MINT_META='{}' MINT_GATE_SCRIPT="" \
  MINT_GATE_LABEL=l MINT_GATE_WEIGHT=w \
    py sidecar "$td/s.ndjson" "$td/s2.sidecar" env "HOME=/h" --cmd "$td/fakegate.sh" Init ) >"$td/stdout" 2>"$td/stderr"
sidecar_has "an exporter argv without env -i is recorded as not cleared" "$td/s2.sidecar" '{"environment_cleared": false, "environment!": {"HOME": "<home>"}, "gate": {"script": null}}'
sidecar_has "the sidecar reads the environment back from the exporter's argv, and an in-repo gate script is repo-relative" "$td/s.sidecar" \
  '{"gate": {"script": "fakegate.sh"}, "environment_cleared": true, "environment!": {"HOME": "<home>", "TMPDIR": "<tmpdir>", "PATH": "<toolchain dir>/bin:/bin", "LEAN_PATH": "<toolchain dir>/lib:/x"}, "modules!": ["Init"], "decls!": ["X"], "options!": []}'

# ── end to end, on a fake bundled toolchain ───────────────────────────────────
rm -rf -- "${td:?}/elan" "${td:?}/cache"
tcd=$(fake_toolchain v4.35.0 4.35.0 "" bundled)
GH35=$(pin_gh v4.35.0)
conf35() { printf 'FAKE_VERSION=4.35.0\nFAKE_GH=%s\n%s' "$GH35" "${1:-}" >"$tcd/fake.conf"; }
run --toolchain v4.35.0 --module Init.Prelude
out="$td/cache/exports/v4.35.0/Init.Prelude.ndjson"
[ "$RC" -eq 0 ] && grep -q '^LEAN_EXPORT_MINT=ok ' "$td/stdout" && [ -s "$out" ] && [ -s "$out.sidecar.json" ] \
  && ok "a bundled mint writes the export and its sidecar" || bad "the bundled mint failed (rc=$RC: $(cat "$td/stderr"))"
python3 -I - "$out" "$TOOL" "$GH35" >"$td/sidecar.check" 2>&1 <<'PY' && ok "the sidecar records toolchain, exporter, command, sha256, meta and date" || bad "sidecar: $(cat "$td/sidecar.check")"
import hashlib, json, re, sys
out, tool, gh = sys.argv[1:]
s = json.load(open(out + ".sidecar.json"))
sha = lambda p: hashlib.sha256(open(p, "rb").read()).hexdigest()
first = open(out).readline().rstrip("\n")
want = {"toolchain": "v4.35.0", "lean_githash": gh, "minted_by": "scripts/lean_export_mint.sh",
        "command": ["leanexport", "Init.Prelude"], "modules": ["Init.Prelude"], "decls": [],
        "meta_line": first, "script_sha256": sha(tool)}
bad = [k for k, v in want.items() if s.get(k) != v]
ex = s["exporter"]
if (ex["kind"], ex["commit"], ex["repo"], ex["tag"]) != ("bundled-leanexport", gh, "https://github.com/leanprover/lean4", "v4.35.0"):
    bad.append("exporter")
if s["export"]["sha256"] != sha(out) or s["export"]["file"] != "Init.Prelude.ndjson" or s["export"]["lines"] != 11:
    bad.append("export")
if s["meta"]["meta"]["lean"]["version"] != "4.35.0" or s["meta"]["meta"]["format"]["version"] != "3.1.0":
    bad.append("meta")
if not re.fullmatch(r"\d{4}-\d\d-\d\dT\d\d:\d\d:\d\dZ", s["generated"]) or not re.fullmatch(r"[0-9a-f]{64}", ex["binary_sha256"]):
    bad.append("generated/binary_sha256")
sys.exit(f"wrong: {bad}" if bad else 0)
PY
sidecar_has "the sidecar records the options, the environment the exporter ran under and the gate" "$out.sidecar.json" \
  "{\"options!\": [], \"environment_cleared\": true, \"environment!\": {\"HOME\": \"<home>\", \"TMPDIR\": \"<tmpdir>\", \"PATH\": \"<toolchain dir>/bin:/usr/bin:/bin\", \"LEAN_SYSROOT\": \"<toolchain dir>\", \"LEAN_ABORT_ON_PANIC\": \"1\"}, \"gate!\": {\"script\": \"$td/fakegate.sh\", \"script_sha256\": \"$(sha "$td/fakegate.sh")\", \"label\": \"lean-export-mint-Init\", \"weight\": \"auto:lean-export-mint-Init:5\", \"reserved_gb\": 5, \"held\": \"\"}, \"exporter\": {\"binary_sha256\": \"$(sha "$tcd/bin/leanexport")\"}}"
gate_log_is() {  # <arm> <rc> <line>...: the gate saw exactly these queries and reservations, in order
  local arm=$1 want_rc=$2 want got; shift 2
  want=$(printf '%s|' "$@"); got=$(sed 's/ -- .*$//' "$td/gate.log" | tr '\n' '|')
  if [ "$RC" -eq "$want_rc" ] && [ "$got" = "$want" ]; then ok "$arm"
  else bad "$arm: rc=$RC, the gate saw '$got', want '$want' $(head -c 200 "$td/stderr")"; fi
}
gate_log_is "an Init mint asks the gate its class's weight before the fetch, then that and its label's floor just before it reserves auto:lean-export-mint-Init:5" 0 \
  "weight auto:lean-export-mint-Init:5" "weight auto:lean-export-mint-Init:5" "weight 0 lean-export-mint-Init" "run auto:lean-export-mint-Init:5 lean-export-mint-Init"
grep -qx "LEAN_SYSROOT=$tcd" "$tcd/env.log" && grep -qx 'LEAN_ABORT_ON_PANIC=1' "$tcd/env.log" \
  && grep -q "^PATH=$tcd/bin:" "$tcd/env.log" && ok "the exporter runs with LEAN_SYSROOT, PATH and LEAN_ABORT_ON_PANIC set to the toolchain" \
  || bad "exporter env: $(cat "$tcd/env.log")"
grep -qx 'CANARY=' "$tcd/env.log" && ok "the exporter inherits nothing else (env -i)" || bad "the caller's environment leaked: $(grep CANARY "$tcd/env.log")"
run --toolchain v4.35.0 --module Init.Prelude;               expect "an existing export is not replaced" 1 "reason=out-exists"
run --toolchain v4.35.0 --module Init.Prelude --force
[ "$RC" -eq 0 ] && [ "$(pair_sha "$out")" = "$(sha "$out") $(sha "$out")" ] && [ ! -e "$out.lock" ] \
  && [ "$(ls "$(dirname "$out")" | grep -c '^Init\.Prelude\.ndjson')" = 2 ] \
  && ok "--force replaces the pair, leaving no partial or aside name and no lock" || bad "--force: rc=$RC $(ls "$(dirname "$out")") $(cat "$td/stderr")"
run --toolchain v4.35.0 --export-unsafe --module Init.Prelude --decl Nat.add --decl Nat.succ \
    --lean-path /a --lean-path /b --gate-gb 9 --out "$td/d.ndjson"
[ "$RC" -eq 0 ] && [ "$(cat "$tcd/argv.log")" = "--export-unsafe Init.Prelude -- Nat.add Nat.succ" ] \
  && ok "options, modules and declarations reach the exporter in its order" || bad "argv: $(cat "$tcd/argv.log") rc=$RC $(cat "$td/stderr")"
grep -qx 'LEAN_PATH=/a:/b' "$tcd/env.log" && ok "--lean-path becomes LEAN_PATH" || bad "LEAN_PATH: $(grep LEAN_PATH "$tcd/env.log")"
gate_log_is "--gate-gb on a class no run has completed under reserves auto:<class>:9: 9 GB, the peak filed under the class" 0 \
  "weight auto:lean-export-mint-Init:9" "weight auto:lean-export-mint-Init:9" "weight 0 lean-export-mint-Init" "run auto:lean-export-mint-Init:9 lean-export-mint-Init"
sidecar_has "the sidecar records --export-unsafe, the declarations, LEAN_PATH and the reservation --gate-gb made" "$td/d.ndjson.sidecar.json" \
  '{"options!": ["--export-unsafe"], "modules!": ["Init.Prelude"], "decls!": ["Nat.add", "Nat.succ"], "environment": {"LEAN_PATH": "/a:/b"}, "gate": {"weight": "auto:lean-export-mint-Init:9", "label": "lean-export-mint-Init", "reserved_gb": 9}}'
export HEAVY_GATE_HELD=outer
run --toolchain v4.35.0 --module Mathlib --out "$td/held.ndjson"; unset HEAVY_GATE_HELD
[ "$RC" -eq 0 ] && [ ! -s "$td/gate.log" ] && ok "an enclosing HEAVY_GATE_HELD reservation is honoured: no reservation, no weight query" \
  || bad "held: rc=$RC gate=$(cat "$td/gate.log") $(cat "$td/stderr")"
sidecar_has "a held mint records the outer reservation and no gate script" "$td/held.ndjson.sidecar.json" \
  '{"gate!": {"script": null, "script_sha256": null, "label": "lean-export-mint-Mathlib", "weight": "auto:lean-export-mint-Mathlib:5", "reserved_gb": null, "held": "outer"}}'
run --toolchain v4.35.0 --module Mathlib.Order.Basic --out "$td/g1.ndjson"; expect "an unmeasured Mathlib mint class needs --gate-gb" 1 "reason=gate-weight-unseen"
gate_log_is "... asked of the gate, and nothing reserved" 1 "weight auto:lean-export-mint-Mathlib:5"
run --toolchain v4.35.0 --module Mathlib.Order.Basic --gate-gb 20 --out "$td/g2.ndjson"
gate_log_is "--gate-gb mints an unmeasured class as auto:<class>:20, so its peak is filed where auto: reads it" 0 \
  "weight auto:lean-export-mint-Mathlib:20" "weight auto:lean-export-mint-Mathlib:20" "weight 0 lean-export-mint-Mathlib" "run auto:lean-export-mint-Mathlib:20 lean-export-mint-Mathlib"
MEASURED='class lean-export-mint-Mathlib: max peak 11.40 GB over the last 1 completed run(s); ceil(1.3 x 11.40) = 15 GB (floor 1)'
FAKE_GATE_BASIS=$MEASURED FAKE_GATE_AUTO_GB=15 run --toolchain v4.35.0 --module Mathlib --out "$td/g3.ndjson"
gate_log_is "a measured class mints on its derived weight" 0 \
  "weight auto:lean-export-mint-Mathlib:5" "weight auto:lean-export-mint-Mathlib:5" "weight 0 lean-export-mint-Mathlib" "run auto:lean-export-mint-Mathlib:5 lean-export-mint-Mathlib"
FAKE_GATE_BASIS=$MEASURED FAKE_GATE_AUTO_GB=15 FAKE_GATE_FLOOR=15 run --toolchain v4.35.0 --module Mathlib --out "$td/g3b.ndjson"
gate_log_is "... and on it still when the label's floor ties it" 0 \
  "weight auto:lean-export-mint-Mathlib:5" "weight auto:lean-export-mint-Mathlib:5" "weight 0 lean-export-mint-Mathlib" "run auto:lean-export-mint-Mathlib:5 lean-export-mint-Mathlib"
FAKE_GATE_BASIS=$MEASURED FAKE_GATE_AUTO_GB=15 FAKE_GATE_FLOOR=39 run --toolchain v4.35.0 --module Mathlib --out "$td/g3c.ndjson"
gate_log_is "a label whose explicit runs peaked above the class's auto: weight reserves its floor (39 GB, not 15)" 0 \
  "weight auto:lean-export-mint-Mathlib:5" "weight auto:lean-export-mint-Mathlib:5" "weight 0 lean-export-mint-Mathlib" "run 39 lean-export-mint-Mathlib"
FAKE_GATE_BASIS=$MEASURED FAKE_GATE_AUTO_GB=15 run --toolchain v4.35.0 --module Mathlib --gate-gb 20 --out "$td/g3d.ndjson"
gate_log_is "--gate-gb on a measured class is an explicit weight (the gate raises it to the label's floor)" 0 \
  "weight auto:lean-export-mint-Mathlib:20" "weight auto:lean-export-mint-Mathlib:20" "weight 0 lean-export-mint-Mathlib" "run 20 lean-export-mint-Mathlib"
FAKE_GATE_FLOOR=39 run --toolchain v4.35.0 --module Mathlib --gate-gb 20 --out "$td/g3e.ndjson"
gate_log_is "--gate-gb on an unmeasured class whose label's floor is higher reserves auto:<class>:<floor>" 0 \
  "weight auto:lean-export-mint-Mathlib:20" "weight auto:lean-export-mint-Mathlib:20" "weight 0 lean-export-mint-Mathlib" "run auto:lean-export-mint-Mathlib:39 lean-export-mint-Mathlib"
FAKE_GATE_FLOOR=8 run --toolchain v4.35.0 --module Init.Prelude --out "$td/g3f.ndjson"
gate_log_is "an unmeasured core class whose label's floor is above 5 GB reserves auto:<class>:<floor>" 0 \
  "weight auto:lean-export-mint-Init:5" "weight auto:lean-export-mint-Init:5" "weight 0 lean-export-mint-Init" "run auto:lean-export-mint-Init:8 lean-export-mint-Init"
KILLED='class lean-export-mint-Mathlib: no completed run; 1 killed run(s) peaked at 0.30 GB, which may raise the 5 GB fallback and never lower it'
FAKE_GATE_BASIS=$KILLED run --toolchain v4.35.0 --module Mathlib --out "$td/g3g.ndjson"
expect "a class whose only runs failed or were killed is unmeasured: a Mathlib mint needs --gate-gb" 1 "reason=gate-weight-unseen"
gate_log_is "... and nothing is reserved" 1 "weight auto:lean-export-mint-Mathlib:5"
FAKE_GATE_BASIS=$KILLED FAKE_GATE_AUTO_GB=20 run --toolchain v4.35.0 --module Mathlib --gate-gb 20 --out "$td/g3h.ndjson"
gate_log_is "... and its --gate-gb mint reserves auto:<class>:20, filed under the class" 0 \
  "weight auto:lean-export-mint-Mathlib:20" "weight auto:lean-export-mint-Mathlib:20" "weight 0 lean-export-mint-Mathlib" "run auto:lean-export-mint-Mathlib:20 lean-export-mint-Mathlib"
FAKE_GATE_WEIGHT_FAIL=1 run --toolchain v4.35.0 --module Mathlib --out "$td/g4.ndjson"; expect "a gate that cannot say a class's weight is refused" 1 "reason=gate-weight-unknown"
FAKE_GATE_WEIGHT_FAIL=1 run --toolchain v4.35.0 --module Init.Prelude --out "$td/g4b.ndjson"; expect "... a core mint's too" 1 "reason=gate-weight-unknown"
FAKE_GATE_FLOOR_FAIL=1 run --toolchain v4.35.0 --module Init.Prelude --out "$td/g4c.ndjson"
expect "a gate that cannot say the label's floor is refused" 1 "reason=gate-weight-unknown '$td/fakegate.sh weight 0 lean-export-mint-Init'"
[ ! -e "$td/g4c.ndjson" ] && ! grep -q '^run' "$td/gate.log" && ok "... before anything is reserved or minted" || bad "floor failure: $(cat "$td/gate.log")"
run --toolchain v4.35.0 --module Std.Data --out "$td/g5.ndjson"
gate_log_is "a Std mint whose class is unseen takes the core fallback" 0 \
  "weight auto:lean-export-mint-Std:5" "weight auto:lean-export-mint-Std:5" "weight 0 lean-export-mint-Std" "run auto:lean-export-mint-Std:5 lean-export-mint-Std"
run --toolchain v4.35.0 --module Init.Prelude --module Mathlib.Order.Basic --out "$td/c1.ndjson"
expect "a Mathlib module after an Init one still needs the Mathlib class measured" 1 "reason=gate-weight-unseen no lean-export-mint-Mathlib mint"
gate_log_is "... asked of the gate under the Mathlib class, and nothing reserved" 1 "weight auto:lean-export-mint-Mathlib:5"
run --toolchain v4.35.0 --module Init.Prelude --module Mathlib.Order.Basic --gate-gb 20 --out "$td/c2.ndjson"
gate_log_is "... and its run is filed under the Mathlib class, not Init's" 0 \
  "weight auto:lean-export-mint-Mathlib:20" "weight auto:lean-export-mint-Mathlib:20" "weight 0 lean-export-mint-Mathlib" "run auto:lean-export-mint-Mathlib:20 lean-export-mint-Mathlib"
FAKE_GATE_BASIS='class lean-export-mint-Batteries-Mathlib: max peak 9.00 GB over the last 1 completed run(s)' FAKE_GATE_AUTO_GB=12 \
  run --toolchain v4.35.0 --module Mathlib.Order.Basic --module Batteries.Data --module Init.Core --module Mathlib.Logic --out "$td/c3.ndjson"
gate_log_is "every non-core root names the class, each once and sorted" 0 "weight auto:lean-export-mint-Batteries-Mathlib:5" "weight auto:lean-export-mint-Batteries-Mathlib:5" \
  "weight 0 lean-export-mint-Batteries-Mathlib" "run auto:lean-export-mint-Batteries-Mathlib:5 lean-export-mint-Batteries-Mathlib"
run --toolchain v4.35.0 --module Std.Data --module Init.Prelude --out "$td/c4.ndjson"
gate_log_is "an all-core mint is named by every core root" 0 \
  "weight auto:lean-export-mint-Init-Std:5" "weight auto:lean-export-mint-Init-Std:5" "weight 0 lean-export-mint-Init-Std" "run auto:lean-export-mint-Init-Std:5 lean-export-mint-Init-Std"
# Measured only on heavy_gate's own words for this class (the third re-review's probe 4).
FAKE_GATE_BASIS='class lean-export-mint-Mathlib: no run on record yet, fallback 5 GB' run --toolchain v4.35.0 --module Mathlib.Order.Basic --out "$td/w1.ndjson"
expect1 "a weight answer in words heavy_gate never wrote reads as unmeasured: a Mathlib mint needs --gate-gb" 1 "reason=gate-weight-unseen"
FAKE_GATE_BASIS='class lean-export-mint-Batteries: max peak 9.00 GB over the last 1 completed run(s)' FAKE_GATE_AUTO_GB=12 \
  run --toolchain v4.35.0 --module Mathlib.Order.Basic --out "$td/w2.ndjson"
expect1 "... and so does a measured answer about another class" 1 "reason=gate-weight-unseen"
# What heavy_gate reserved is read by the job, which does not start under what the answers settled.
conf35; rm -f -- "${tcd:?}/argv.log"
FAKE_GATE_BASIS=$MEASURED FAKE_GATE_AUTO_GB=15 FAKE_GATE_RESERVE=10 run --toolchain v4.35.0 --module Mathlib --gate-gb 20 --out "$td/r1.ndjson"
expect1 "a reservation under the explicit --gate-gb the answers settled is refused" 1 \
  "reason=gate-under-reserved heavy_gate reserved 10 GB for lean-export-mint-Mathlib at 20, under the 20 GB its answers settled"
[ ! -e "$tcd/argv.log" ] && [ ! -e "$td/r1.ndjson" ] && ok "... and the exporter never ran" || bad "under-reserved: the exporter ran ($(cat "$tcd/argv.log" 2>/dev/null))"
FAKE_GATE_BASIS=$MEASURED FAKE_GATE_AUTO_GB=15 FAKE_GATE_RESERVE=10 run --toolchain v4.35.0 --module Mathlib --out "$td/r2.ndjson"
expect1 "... and one under the class's auto: weight" 1 \
  "reason=gate-under-reserved heavy_gate reserved 10 GB for lean-export-mint-Mathlib at auto:lean-export-mint-Mathlib:5, under the 15 GB"
FAKE_GATE_BASIS=$MEASURED FAKE_GATE_AUTO_GB=15 FAKE_GATE_FLOOR=39 FAKE_GATE_RESERVE=20 run --toolchain v4.35.0 --module Mathlib --out "$td/r3.ndjson"
expect1 "... and one under the label's floor" 1 "reason=gate-under-reserved heavy_gate reserved 20 GB for lean-export-mint-Mathlib at 39, under the 39 GB"
FAKE_GATE_RESERVE=4 run --toolchain v4.35.0 --module Init.Prelude --out "$td/r4.ndjson"
expect1 "... and one under an unmeasured class's fallback" 1 \
  "reason=gate-under-reserved heavy_gate reserved 4 GB for lean-export-mint-Init at auto:lean-export-mint-Init:5, under the 5 GB"
FAKE_GATE_HELD=garbage run --toolchain v4.35.0 --module Init.Prelude --out "$td/r5.ndjson"
expect1 "a gate that does not say what it reserved is refused" 1 "reason=gate-failed heavy_gate did not say what it reserved for lean-export-mint-Init"
[ ! -e "$tcd/argv.log" ] && ok "... and the exporter never ran" || bad "unsaid: the exporter ran"
# The same rules against the real gate's `weight` and resolver (resolvergate.sh),
# over a scratch peak log: what a --gate-gb run files is what the next run reads.
grep -qF '_resolve_weight "${2-}" "$label"; gb=$GB; cls=$CLASS' "$HERE/heavy_gate.sh" \
  && grep -qF '[ -n "$cls" ] && tail="$tail class=$cls"' "$HERE/heavy_gate.sh" \
  && ok "heavy_gate.sh files class= for an auto: weight alone, as resolvergate.sh models it" \
  || bad "heavy_gate.sh no longer files peaks as resolvergate.sh models; re-read its run and _peak_report"
grep -qF 'HEAVY_GATE_HELD="${gb}:${label}" "$@"' "$HERE/heavy_gate.sh" \
  && ok "heavy_gate.sh runs the job with HEAVY_GATE_HELD=<gb>:<label>, which the mint's job reads, as both fake gates model it" \
  || bad "heavy_gate.sh no longer sets HEAVY_GATE_HELD=<gb>:<label> for its job; re-read its run"
hg="$td/hg"; mkdir -p "$hg"
real_gate() { HEAVY_GATE_DIR="$hg" HEAVY_GATE_PHYS_GB=128 GATE_UNDER_TEST="$td/resolvergate.sh" run "$@"; }
real_gate --toolchain v4.35.0 --module Mathlib.Order.Basic --out "$td/h1.ndjson"
expect1 "with the real resolver, an unmeasured Mathlib mint is refused" 1 "reason=gate-weight-unseen"
FAKE_PEAK_GB=11.40 real_gate --toolchain v4.35.0 --module Mathlib.Order.Basic --gate-gb 20 --out "$td/h2.ndjson"
[ "$RC" -eq 0 ] && grep -qx 'run auto:lean-export-mint-Mathlib:20 lean-export-mint-Mathlib GB=20 CLASS=lean-export-mint-Mathlib' "$td/gate.log" \
  && grep -q ' lean-export-mint-Mathlib reserved=20 peak_gb=11.40 .* rc=0 class=lean-export-mint-Mathlib$' "$hg/peaks.log" \
  && ok "... its --gate-gb 20 mint reserves 20 GB and files its peak under the class" \
  || bad "real --gate-gb: rc=$RC $(cat "$td/gate.log") | $(cat "$hg/peaks.log") $(head -c 200 "$td/stderr")"
real_gate --toolchain v4.35.0 --module Mathlib.Order.Basic --out "$td/h3.ndjson"
[ "$RC" -eq 0 ] && grep -qx 'run auto:lean-export-mint-Mathlib:5 lean-export-mint-Mathlib GB=15 CLASS=lean-export-mint-Mathlib' "$td/gate.log" \
  && ok "... after which the class is measured: the next mint needs no --gate-gb and reserves ceil(1.3 x 11.40) = 15 GB" \
  || bad "real measured: rc=$RC $(cat "$td/gate.log") $(head -c 300 "$td/stderr")"
FAKE_PEAK_GB=30.00 real_gate --toolchain v4.35.0 --module Mathlib --gate-gb 40 --out "$td/h4.ndjson"
[ "$RC" -eq 0 ] && grep -qx 'run 40 lean-export-mint-Mathlib GB=40 CLASS=' "$td/gate.log" \
  && ok "... a --gate-gb 40 mint on the measured class is an explicit weight, filed under its label alone" \
  || bad "real explicit: rc=$RC $(cat "$td/gate.log") $(head -c 300 "$td/stderr")"
real_gate --toolchain v4.35.0 --module Mathlib --out "$td/h5.ndjson"
[ "$RC" -eq 0 ] && grep -qx 'run 39 lean-export-mint-Mathlib GB=39 CLASS=' "$td/gate.log" \
  && ok "... and the next mint reserves the label's floor, ceil(1.3 x 30.00) = 39 GB, not the class's auto: 15 GB" \
  || bad "real floor: rc=$RC $(cat "$td/gate.log") $(head -c 300 "$td/stderr")"
printf '%s lean-export-mint-Batteries reserved=5 peak_gb=0.30 pct=6 dur=0m01s rc=65 class=lean-export-mint-Batteries\n' \
  "$(date -u +%FT%TZ)" >>"$hg/peaks.log"
real_gate --toolchain v4.35.0 --module Batteries.Data --out "$td/h6.ndjson"
expect1 "with the real resolver, a class whose only run failed is unmeasured" 1 "reason=gate-weight-unseen no lean-export-mint-Batteries mint"
FAKE_PEAK_GB=6.00 real_gate --toolchain v4.35.0 --module Batteries.Data --gate-gb 8 --out "$td/h7.ndjson"
[ "$RC" -eq 0 ] && grep -qx 'run auto:lean-export-mint-Batteries:8 lean-export-mint-Batteries GB=8 CLASS=lean-export-mint-Batteries' "$td/gate.log" \
  && ok "... and its --gate-gb 8 mint measures it under the class" || bad "real killed: rc=$RC $(cat "$td/gate.log") $(head -c 300 "$td/stderr")"
# Probe B3's own log: three completed --gate-gb 20 mints as 8809b1fdc ran them,
# a plain 20 GB, so filed under the label alone (no class=).
hg2="$td/hg2"; mkdir -p "$hg2"
for p in 11.40 11.60 11.50; do
  printf '%s lean-export-mint-Mathlib reserved=20 peak_gb=%s pct=57 dur=9m00s rc=0\n' "$(date -u +%FT%TZ)" "$p" >>"$hg2/peaks.log"
done
b3_gate() { HEAVY_GATE_DIR="$hg2" HEAVY_GATE_PHYS_GB=128 GATE_UNDER_TEST="$td/resolvergate.sh" run "$@"; }
b3_gate --toolchain v4.35.0 --module Mathlib.Order.Basic --out "$td/b3a.ndjson"
expect1 "over probe B3's log (three completed label-only --gate-gb runs) the class is still unmeasured" 1 "reason=gate-weight-unseen"
FAKE_PEAK_GB=11.40 b3_gate --toolchain v4.35.0 --module Mathlib.Order.Basic --gate-gb 5 --out "$td/b3b.ndjson"
[ "$RC" -eq 0 ] && grep -qx 'run auto:lean-export-mint-Mathlib:16 lean-export-mint-Mathlib GB=16 CLASS=lean-export-mint-Mathlib' "$td/gate.log" \
  && [ "$(grep -c ' rc=0 class=lean-export-mint-Mathlib$' "$hg2/peaks.log")" = 1 ] \
  && ok "... a --gate-gb 5 mint there reserves auto:<class>:16 (ceil(1.3 x 11.60), the label's floor) and files its peak under the class" \
  || bad "B3 --gate-gb: rc=$RC $(cat "$td/gate.log") | $(tail -1 "$hg2/peaks.log") $(head -c 200 "$td/stderr")"
b3_gate --toolchain v4.35.0 --module Mathlib.Order.Basic --out "$td/b3c.ndjson"
[ "$RC" -eq 0 ] && grep -qx 'run 16 lean-export-mint-Mathlib GB=16 CLASS=' "$td/gate.log" \
  && ok "... after which the refusal lifts, and the next mint reserves the label's 16 GB floor over the class's 15" \
  || bad "B3 measured: rc=$RC $(cat "$td/gate.log") $(head -c 300 "$td/stderr")"
# Another Mathlib mint completes under the class just before this one's
# reservation is resolved, after its last weight query: the reservation
# resolves to that run's derived 8 GB, under the --gate-gb 40 this mint settled.
hgu="$td/hgu"; mkdir -p "$hgu"; rm -f -- "${tcd:?}/argv.log"
FAKE_GATE_PRE_RUN="2026-10-28T00:00:00Z lean-export-mint-Mathlib reserved=8 peak_gb=6.00 pct=75 dur=1m00s rc=0 class=lean-export-mint-Mathlib" \
  HEAVY_GATE_DIR="$hgu" HEAVY_GATE_PHYS_GB=128 GATE_UNDER_TEST="$td/resolvergate.sh" \
  run --toolchain v4.35.0 --module Mathlib.Order.Basic --gate-gb 40 --out "$td/u.ndjson"
expect1 "with the real resolver, a class measured between the last weight query and the reservation is refused, not minted at 8 GB" 1 \
  "reason=gate-under-reserved heavy_gate reserved 8 GB for lean-export-mint-Mathlib at auto:lean-export-mint-Mathlib:40, under the 40 GB"
[ ! -e "$tcd/argv.log" ] && [ ! -e "$td/u.ndjson" ] && ok "... and the exporter never ran" || bad "pre-run class: the exporter ran"
no_trace() {  # <arm>: nothing at <out> and no partial files beside it
  if [ ! -e "$td/e.ndjson" ] && [ -z "$(ls "$td" | grep '^e\.ndjson')" ]; then ok "$1"; else bad "$1: $(ls "$td" | grep '^e\.ndjson')"; fi
}
conf35 'FAKE_RC=3'
run --toolchain v4.35.0 --module Init.Prelude --out "$td/e.ndjson"; expect "an exporter failure is refused" 1 "reason=exporter-failed leanexport Init.Prelude exited 3"
no_trace "a failed mint leaves nothing behind"
conf35 'FAKE_SIGNAL=ABRT'
run --toolchain v4.35.0 --module Init.Prelude --out "$td/e.ndjson"; expect "an exporter killed by a signal (a panic under LEAN_ABORT_ON_PANIC) is named so" 1 "reason=exporter-failed leanexport Init.Prelude was killed by signal 6"
no_trace "a killed exporter leaves nothing behind"
conf35 'FAKE_RC=75'
run --toolchain v4.35.0 --module Init.Prelude --out "$td/e.ndjson"; expect "an exporter's own exit 75 under the gate is the exporter's failure, not the gate's" 1 "reason=exporter-failed leanexport Init.Prelude exited 75"
conf35; rm -f -- "${tcd:?}/argv.log"
FAKE_GATE_RC=75 run --toolchain v4.35.0 --module Init.Prelude --out "$td/e.ndjson"
expect "a mint the gate refuses (a small box, exit 75) is a gate refusal" 1 "reason=gate-refused heavy_gate refused lean-export-mint-Init at auto:lean-export-mint-Init:5"
[ ! -e "$tcd/argv.log" ] && ok "... and the exporter never ran" || bad "the exporter ran under a refused reservation"
no_trace "a refused reservation leaves nothing behind"
FAKE_GATE_RC=3 run --toolchain v4.35.0 --module Init.Prelude --out "$td/e.ndjson"
expect "a gate that fails before the mint starts is named" 1 "reason=gate-failed heavy_gate exited 3 before lean-export-mint-Init started"
TMPDIR_UNDER_TEST="$td/no-such-tmp" run --toolchain v4.35.0 --module Init.Prelude --out "$td/e.ndjson"
expect "a gate start marker that cannot be made is refused before the gate runs" 1 "reason=gate-failed cannot make the gate's start marker"
! grep -q '^run' "$td/gate.log" && ok "... and nothing was reserved" || bad "gate log: $(cat "$td/gate.log")"
meta35=$(printf '{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"},"lean":{"githash":"%s","version":"4.35.0"}}}' "$GH35")
python3 -I - "$td/big.body" "${#meta35}" <<'PY' || bad "could not write the 4 KiB-boundary body"
import sys
out, meta_len = sys.argv[1], int(sys.argv[2]) + 1    # the meta line and its newline
head, tail = '{"in":1,"str":{"pre":0,"str":"', '"}}\n'
pad = 4096 - meta_len - len(head) - len(tail)        # the first record ends at byte 4096
lines = [head + "N" * pad + tail] + ['{"in":%d,"str":{"pre":1,"str":"n%d"}}\n' % (i, i) for i in range(2, 400)]
open(out, "w").write("".join(lines + ['{"def":{"name":1}}\n']))
PY
# This arm models a FULL DISK under the writer (a write error the writer must
# not ignore), not Lean under a file size limit. The 4 KiB limit is on the whole
# job, but only the python writer writes a file: CPython ignores SIGXFSZ, so
# the limit reaches it as a short write and then EFBIG, as a full disk's ENOSPC
# would, while the exporter writes a pipe the limit never reaches. Real Lean
# writing a file itself under `ulimit -f` dies by signal 25 (SIGXFSZ), and with
# SIGXFSZ ignored exits 0 with its tail lost (measured 2026-10-28, v4.30.0-rc2
# `lean --run`), which is why the exporter never writes the export.
conf35 "FAKE_BODY=$td/big.body"$'\n'"FAKE_LIKE_LEAN=1"
FAKE_GATE_FSIZE=4 run --toolchain v4.35.0 --module Init.Prelude --out "$td/e.ndjson"
expect "an export the disk takes only 4 KiB of (cut at a line boundary; the exporter exits 0) is refused" \
  1 "reason=export-write-failed"
no_trace "an export the writer could not finish is not left at --out"
conf35; mkdir -p "$td/rw"
FAKE_GATE_CHMOD="$td/rw" run --toolchain v4.35.0 --module Init.Prelude --out "$td/rw/x.ndjson"; chmod 755 "$td/rw"
expect "a partial export the writer cannot create is refused by name" 1 "reason=export-write-failed cannot open $td/rw/x.ndjson.partial."
LEAN_EXPORT_MINT_PYTHON="$td/fakepy.sh" FAKE_PY_FAIL_VERB=write FAKE_PY_FAIL_RC=70 run --toolchain v4.35.0 --module Init.Prelude --out "$td/e.ndjson"
expect "a writer that crashes is refused as such" 1 "reason=export-writer-failed"
no_trace "a crashed writer leaves no partial file"
printf 'FAKE_VERSION=4.34.0\nFAKE_GH=%s\n' "$GH35" >"$tcd/fake.conf"
run --toolchain v4.35.0 --module Init.Prelude --out "$td/e.ndjson"; expect "an export stating another Lean is refused" 1 "reason=meta-lean-version-mismatch"
no_trace "a refused export is not left at --out"
[ "$(grep -c 'LEAN_EXPORT_MINT=refused' "$td/stderr")" = 1 ] && ok "... with the check's one refusal line, no second one from the shell" \
  || bad "refusal lines: $(cat "$td/stderr")"
conf35
printf '%s\n%s\n' '{"in":1,"str":{"pre":0,"str":"Nat"}}' '{"in":2,"str":{"pre":1,"str":"zero"}}' >"$td/cut.body"
conf35 "FAKE_BODY=$td/cut.body"
run --toolchain v4.35.0 --module Init.Prelude --out "$td/e.ndjson"
expect "an export cut at a line boundary (every line whole, no declaration last) is refused" 1 "reason=export-truncated the last record (line 3)"
no_trace "an export cut at a line boundary is not left at --out"
printf '%s\n{"in":2,"str":{"pre":1,"str":"ad' "$R" >"$td/trunc.body"
conf35 "FAKE_BODY=$td/trunc.body"
run --toolchain v4.35.0 --module Init.Prelude --out "$td/e.ndjson"; expect "an export whose tail was lost, minted with exit 0, is refused" 1 "reason=export-truncated"
no_trace "a truncated export is not left at --out"
printf '%s\n{"oops":1}\n' "$R" >"$td/odd.body"
conf35 "FAKE_BODY=$td/odd.body"
run --toolchain v4.35.0 --module Init.Prelude --out "$td/e.ndjson"; expect "an export with a record the front door cannot read is refused" 1 "reason=export-malformed line 3"
no_trace "a malformed export is not left at --out"
conf35
run --toolchain v4.35.0 --module Init.Prelude --decl Nat.add --decl Unsafe.thing --out "$td/e.ndjson"
expect "a --decl the exporter skipped (as it skips unsafe constants) is refused by name" 1 "for ['Unsafe.thing']"
no_trace "an export missing a --decl is not left at --out"
LEAN_EXPORT_MINT_PYTHON="$td/fakepy.sh" FAKE_PY_FAIL_VERB=sidecar FAKE_PY_FAIL_RC=1 run --toolchain v4.35.0 --module Init.Prelude --out "$td/e.ndjson"
expect "a sidecar that cannot be written is refused" 1 "reason=sidecar-failed"
no_trace "a failed sidecar leaves no partial file"
LEAN_EXPORT_MINT_PYTHON="$td/fakepy.sh" FAKE_PY_FAIL_VERB=meta FAKE_PY_FAIL_RC=70 run --toolchain v4.35.0 --module Init.Prelude --out "$td/e.ndjson"
expect "an export check that crashes is refused, not passed" 1 "reason=export-check-failed"
no_trace "a crashed export check leaves no partial file"
LEAN_EXPORT_MINT_PYTHON="$td/fakepy.sh" FAKE_PY_FAIL_VERB=meta FAKE_PY_FAIL_RC=1 run --toolchain v4.35.0 --module Init.Prelude --out "$td/e.ndjson"
expect "an export check exiting 1 (an interpreter failure, not a refusal) is refused by name" 1 "reason=export-check-failed the export check of"
conf35 "FAKE_TOUCH=$td/race.ndjson"
run --toolchain v4.35.0 --module Init.Prelude --out "$td/race.ndjson"; expect "an export that appears at --out during the mint is not overwritten" 1 "reason=out-exists"
[ "$(cat "$td/race.ndjson")" = planted ] && [ -z "$(ls "$td" | grep '^race\.ndjson\.')" ] && ok "... and the mint's partial files are removed" \
  || bad "race: $(ls "$td" | grep '^race')"
conf35; mkdir -p "$td/sd.ndjson.sidecar.json"; rm -f -- "${tcd:?}/argv.log"
run --toolchain v4.35.0 --module Init.Prelude --out "$td/sd.ndjson" --force
expect "a directory where the sidecar goes is refused, --force or not" 1 "reason=out-is-directory $td/sd.ndjson.sidecar.json"
[ -z "$(ls "$td/sd.ndjson.sidecar.json")" ] && [ ! -e "$td/sd.ndjson" ] && [ ! -e "$tcd/argv.log" ] \
  && ok "... before anything is minted into it: the exporter never ran" \
  || bad "sidecar dir: $(ls "$td/sd.ndjson.sidecar.json") $(ls "$td" | grep '^sd')"
conf35 "FAKE_MKDIR=$td/late.ndjson"
run --toolchain v4.35.0 --module Init.Prelude --out "$td/late.ndjson" --force
expect "a directory that appears at --out during a --force mint is refused" 1 "reason=out-is-directory $td/late.ndjson is a directory"
[ -z "$(ls "$td/late.ndjson")" ] && ok "... and nothing is moved into it" || bad "moved into the late dir: $(ls "$td/late.ndjson")"
conf35 "FAKE_MKDIR=$td/late2.ndjson.sidecar.json"
run --toolchain v4.35.0 --module Init.Prelude --out "$td/late2.ndjson" --force
expect "a directory that appears at the sidecar's path during a --force mint is refused" 1 "reason=out-is-directory $td/late2.ndjson.sidecar.json"
[ -z "$(ls "$td/late2.ndjson.sidecar.json")" ] && [ ! -e "$td/late2.ndjson" ] && ok "... and neither file is placed" \
  || bad "late sidecar dir: $(ls "$td/late2.ndjson.sidecar.json") $(ls "$td" | grep '^late2')"
printf 'old\n' >"$td/k.ndjson"
conf35 "FAKE_MKDIR=$td/k.ndjson.sidecar.json"
run --toolchain v4.35.0 --module Init.Prelude --out "$td/k.ndjson" --force
expect1 "a directory at the sidecar's path during a --force mint is refused before the old export is replaced" 1 "reason=out-is-directory $td/k.ndjson.sidecar.json"
[ "$(cat "$td/k.ndjson")" = old ] && ! grep -qF 'appeared during the mint' "$td/stderr" \
  && ok "... which is left as it was, never set aside: the check under --out's lock refuses before the publish starts" \
  || bad "the old export: $(head -c 100 "$td/k.ndjson") $(head -c 400 "$td/stderr")"
conf35
# What appears at a target after the last check meets the publish itself.
planted() {  # <what> <at> <run args>...: run with plant.sh planting <what> at <at> before the publish step
  local what=$1 at=$2; shift 2
  FAKE_PLANT=$what FAKE_PLANT_AT=$at PATH="$td/mvshim:$PATH" LEAN_EXPORT_MINT_PYTHON="$td/fakepy.sh" run "$@"
}
no_partial() {  # <arm> <out>: no partial file of <out> is left
  if [ -z "$(ls "$(dirname "$2")" | grep -F "$(basename "$2").partial")" ]; then ok "$1"; else bad "$1: $(ls "$(dirname "$2")" | grep -F "$(basename "$2")")"; fi
}
planted dir "$td/p1.ndjson" --toolchain v4.35.0 --module Init.Prelude --out "$td/p1.ndjson" --force
expect1 "a directory made at --out after the last check is refused by a --force publish" 1 "reason=out-is-directory $td/p1.ndjson is a directory"
[ -d "$td/p1.ndjson" ] && [ -z "$(ls -A "$td/p1.ndjson")" ] && [ ! -e "$td/p1.ndjson.sidecar.json" ] \
  && ok "... and nothing is moved into it (rename(2) refuses a directory)" || bad "moved into: $(ls -A "$td/p1.ndjson") $(ls "$td" | grep '^p1')"
no_partial "... nor left beside it" "$td/p1.ndjson"
planted dir "$td/p2.ndjson" --toolchain v4.35.0 --module Init.Prelude --out "$td/p2.ndjson"
expect1 "... and by a publish without --force" 1 "reason=out-is-directory $td/p2.ndjson is a directory"
[ -z "$(ls -A "$td/p2.ndjson")" ] && ok "... nothing moved into it either" || bad "moved into: $(ls -A "$td/p2.ndjson")"
planted file "$td/p3.ndjson" --toolchain v4.35.0 --module Init.Prelude --out "$td/p3.ndjson"
expect1 "a file made at --out after the last check is not overwritten without --force" 1 "reason=out-exists $td/p3.ndjson appeared during the mint"
[ "$(cat "$td/p3.ndjson")" = planted ] && [ ! -e "$td/p3.ndjson.sidecar.json" ] && ok "... it is left as it was (link(2) refuses any target)" \
  || bad "p3: $(head -c 100 "$td/p3.ndjson") $(ls "$td" | grep '^p3')"
no_partial "... and no partial file is left" "$td/p3.ndjson"
planted dir "$td/p4.ndjson.sidecar.json" --toolchain v4.35.0 --module Init.Prelude --out "$td/p4.ndjson" --force
expect1 "a directory made at the sidecar's path after the last check is refused" 1 \
  "reason=out-is-directory $td/p4.ndjson.sidecar.json is a directory, not a file the mint can replace (it appeared during the mint; nothing was moved into it); nothing this run placed or set aside was left to undo"
[ -z "$(ls -A "$td/p4.ndjson.sidecar.json")" ] && [ ! -e "$td/p4.ndjson" ] && ok "... before the export is placed: --force sets the old pair aside first, and link(2) refuses the directory" \
  || bad "p4: $(ls -A "$td/p4.ndjson.sidecar.json") $(ls "$td" | grep '^p4')"
planted file "$td/p5.ndjson.sidecar.json" --toolchain v4.35.0 --module Init.Prelude --out "$td/p5.ndjson"
expect1 "a sidecar made after the last check is not overwritten without --force" 1 "reason=out-exists $td/p5.ndjson.sidecar.json appeared"
[ "$(cat "$td/p5.ndjson.sidecar.json")" = planted ] && [ ! -e "$td/p5.ndjson" ] && ok "... it is kept, and the export placed before it is taken back" \
  || bad "p5: $(ls "$td" | grep '^p5')"
no_partial "... leaving no partial file" "$td/p5.ndjson"
LEAN_EXPORT_MINT_PYTHON="$td/fakepy.sh" FAKE_PY_DROP=export run --toolchain v4.35.0 --module Init.Prelude --out "$td/e.ndjson"
expect1 "an export that cannot be placed is refused by name" 1 "reason=out-publish-failed cannot place the export"
no_trace "... and leaves nothing behind"
LEAN_EXPORT_MINT_PYTHON="$td/fakepy.sh" FAKE_PY_DROP=sidecar run --toolchain v4.35.0 --module Init.Prelude --out "$td/e.ndjson"
expect1 "a sidecar that cannot be placed is refused by name" 1 "reason=out-publish-failed cannot place the sidecar"
no_trace "... and the export it describes is removed with it"
printf 'old\n' >"$td/e.ndjson"; printf 'old\n' >"$td/e.ndjson.sidecar.json"
LEAN_EXPORT_MINT_PYTHON="$td/fakepy.sh" FAKE_PY_DROP=sidecar run --toolchain v4.35.0 --module Init.Prelude --out "$td/e.ndjson" --force
expect1 "a --force mint whose sidecar cannot be placed is refused" 1 \
  "reason=out-publish-failed cannot place the sidecar at $td/e.ndjson.sidecar.json (" 
grep -qF "); the export this run placed was removed, the old export was put back, the old sidecar was put back" "$td/stderr" \
  && [ "$(cat "$td/e.ndjson")" = old ] && [ "$(cat "$td/e.ndjson.sidecar.json")" = old ] && [ "$(ls "$td" | grep -c '^e\.ndjson')" = 2 ] \
  && ok "... and the old export and its sidecar are put back as they were, with no partial or aside name left" \
  || bad "the --force undo: $(ls "$td" | grep '^e\.ndjson' | tr '\n' ' ') $(head -c 400 "$td/stderr")"
rm -f -- "${td:?}/e.ndjson" "${td:?}/e.ndjson.sidecar.json"
printf 'orphan\n' >"$td/o.ndjson.sidecar.json"   # a sidecar with no export beside it
LEAN_EXPORT_MINT_PYTHON="$td/fakepy.sh" FAKE_PY_DROP=sidecar run --toolchain v4.35.0 --module Init.Prelude --out "$td/o.ndjson" --force
expect1 "a --force mint over a lone sidecar whose own sidecar cannot be placed is refused" 1 "reason=out-publish-failed cannot place the sidecar at $td/o.ndjson.sidecar.json"
[ ! -e "$td/o.ndjson" ] && [ "$(cat "$td/o.ndjson.sidecar.json" 2>/dev/null)" = orphan ] && ok "... and the lone sidecar is put back, beside nothing, as it was" \
  || bad "the lone sidecar: $(ls "$td" | grep '^o\.ndjson' | tr '\n' ' ')"
LEAN_EXPORT_MINT_PYTHON="$td/fakepy.sh" FAKE_PY_FAIL_VERB=publish FAKE_PY_FAIL_RC=70 run --toolchain v4.35.0 --module Init.Prelude --out "$td/e.ndjson"
expect1 "a publish step that crashes is refused as such" 1 "reason=out-publish-failed the publish of $td/e.ndjson exited 70"
no_trace "... and leaves no partial file"
# Another run replaces the export between this run's two placements. No shim
# outside the python half can act there, so the test runs the script's own
# python half (PY_SRC, as the script holds it) with os.link and os.rename
# wrapped: the placement at --out is followed by another run's rename over it.
( LEAN_EXPORT_MINT_LIB=1; . "$TOOL"; printf '%s' "$PY_SRC" ) >"$td/py_src.py"
cat >"$td/seam.py" <<'PY'
import os, sys
src, other, out = sys.argv[1], sys.argv[2], sys.argv[5]
real = {"link": os.link, "rename": os.rename}
calls = []
def wrap(name):
    def placed(a, b, *rest, **kw):
        real[name](a, b, *rest, **kw)
        if b == out and not calls:
            calls.append(b)
            real["rename"](other, b)   # another run's export, over the one just placed
    return placed
os.link, os.rename = wrap("link"), wrap("rename")
sys.argv = ["lean_export_mint"] + sys.argv[3:]
exec(compile(open(src).read(), src, "exec"), {"__name__": "__main__"})
PY
replaced() {  # <force 0|1>: publish $td/tb/x.ndjson; another run's export replaces this run's.
  # Without --force another sidecar is already at the sidecar's path (so this run's link fails);
  # under --force an old pair is there to be set aside, and this run's partial sidecar is gone
  # (so its link fails)
  rm -rf -- "${td:?}/tb"; mkdir -p "$td/tb"
  printf '%s\n%s\n' "$M" "$RD" >"$td/tb/x.ndjson.partial.1"
  if [ "$1" = 1 ]; then printf 'old run\n' >"$td/tb/x.ndjson"; printf 'old sidecar\n' >"$td/tb/x.ndjson.sidecar.json"
  else printf '{}\n' >"$td/tb/x.ndjson.partial.1.sidecar"; printf 'other sidecar\n' >"$td/tb/x.ndjson.sidecar.json"; fi
  printf 'other run\n' >"$td/tb/other"
  python3 -I "$td/seam.py" "$td/py_src.py" "$td/tb/other" publish "$td/tb/x.ndjson.partial.1" "$td/tb/x.ndjson" "$1" \
    >"$td/stdout" 2>"$td/stderr"
  RC=$?
}
replaced 0
expect1 "a sidecar that cannot be linked after another run replaced the export is refused" 65 \
  "reason=out-exists $td/tb/x.ndjson.sidecar.json appeared during the mint (pass --force to replace it); $td/tb/x.ndjson no longer holds the export this run placed"
[ "$(cat "$td/tb/x.ndjson" 2>/dev/null)" = "other run" ] && [ "$(cat "$td/tb/x.ndjson.sidecar.json")" = "other sidecar" ] \
  && ok "... and the other run's export and sidecar are left: the take-back removes only the inode this run placed" \
  || bad "the take-back removed another run's export: $(ls -A "$td/tb" | tr '\n' ' ')"
replaced 1
expect1 "... and under --force" 65 "reason=out-publish-failed cannot place the sidecar at $td/tb/x.ndjson.sidecar.json"
grep -qF "; $td/tb/x.ndjson no longer holds the export this run placed (another run replaced it), so it is left as it is, $td/tb/x.ndjson is taken, so the old export is kept at $td/tb/x.ndjson.partial.1.old, the old sidecar is kept at $td/tb/x.ndjson.partial.1.sidecar.old, since its export is not back at $td/tb/x.ndjson" "$td/stderr" \
  && ok "... which says where the old pair it could not put back is kept" || bad "the --force undo's words: $(head -c 600 "$td/stderr")"
[ "$(cat "$td/tb/x.ndjson" 2>/dev/null)" = "other run" ] && [ ! -e "$td/tb/x.ndjson.sidecar.json" ] \
  && [ "$(cat "$td/tb/x.ndjson.partial.1.old")" = "old run" ] && [ "$(cat "$td/tb/x.ndjson.partial.1.sidecar.old")" = "old sidecar" ] \
  && ok "... where the other run's export is left, and the old sidecar is not put back beside an export not its own" \
  || bad "the --force undo over another run's export: $(ls -A "$td/tb" | tr '\n' ' ')"
# A publish cut between the export's placement and the sidecar's (the third
# re-review's probe P2): the script's python half runs under cut.py with os.link
# and os.rename wrapped, and right after the placement at --out it is sent
# SIGTERM (term) or SIGKILL (kill), or SIGKILL with the script's shell
# (killboth), or another run's publish to the same --out runs (other). With
# CUT_AT=aside the cut comes instead right after the first link to an aside
# name, inside --force's set-aside of the old export (before its unlink).
cat >"$td/cut.py" <<'PY'
import os, signal, subprocess, sys
prog, argv = sys.argv[1], sys.argv[2:]    # argv: publish <partial> <out> <force>
out, how, at = argv[2], os.environ["CUT"], os.environ.get("CUT_AT", "out")
real = {"link": os.link, "rename": os.rename}
fired = []
def cut():
    if how == "term":
        os.kill(os.getpid(), signal.SIGTERM)
    elif how == "kill":
        os.kill(os.getpid(), signal.SIGKILL)
    elif how == "killboth":
        os.kill(os.getppid(), signal.SIGKILL)
        os.kill(os.getpid(), signal.SIGKILL)
    elif how == "other":
        with open(os.environ["CUT_LOG"], "w") as log:
            subprocess.run(["bash", os.environ["CUT_OTHER"], out], stdin=subprocess.DEVNULL, stdout=log, stderr=log)
def wrap(name):
    def placed(a, b, *rest, **kw):
        real[name](a, b, *rest, **kw)
        if (b == out if at == "out" else b.endswith(".old")) and not fired:
            fired.append(b)
            cut()
    return placed
os.link, os.rename = wrap("link"), wrap("rename")
sys.argv = ["lean_export_mint"] + argv
exec(compile(prog, "py_src", "exec"), {"__name__": "__main__"})
PY
cat >"$td/cutpy.sh" <<'SH'
#!/bin/sh
# python3, except that the publish step runs under cut.py, exec'd: its parent is the script's shell.
if [ "${4:-}" = publish ]; then prog=$3; shift 4; exec python3 -I "$(dirname "$0")/cut.py" "$prog" publish "$@"; fi
exec python3 "$@"
SH
cat >"$td/other.sh" <<'SH'
#!/bin/bash
# Another run's publish of its own pair ($B_PARTIAL) to --out ($1), taking --out's lock as the script does.
LEAN_EXPORT_MINT_LIB=1 LEAN_EXPORT_MINT_LOCK_WAIT=0 LEAN_EXPORT_MINT_PYTHON=python3
. "$TOOL_UNDER_CUT"
take_lock "$1.lock" out-locked
py publish "$B_PARTIAL" "$1" 1
SH
chmod +x "$td/cutpy.sh" "$td/other.sh"
cut_run() {  # <how> <run args>...
  local how=$1; shift
  CUT=$how LEAN_EXPORT_MINT_PYTHON="$td/cutpy.sh" run "$@"
}
k="$td/k2.ndjson"
conf35; run --toolchain v4.35.0 --module Init.Prelude --out "$k"; old=$(sha "$k")
{ cat "$tcd/body.ndjson"; echo '{"in":9,"str":{"pre":0,"str":"Extra"}}'; echo '{"axiom":{"name":9}}'; } >"$td/body2"
{ cat "$td/body2"; echo '{"in":10,"str":{"pre":0,"str":"More"}}'; echo '{"axiom":{"name":10}}'; } >"$td/body3"
conf35 "FAKE_BODY=$td/body2"
cut_run term --toolchain v4.35.0 --module Init.Prelude --out "$k" --force; new=$(sha "$k")
[ "$RC" -eq 0 ] && [ "$new" != "$old" ] && [ "$(pair_sha "$k")" = "$new $new" ] \
  && ok "a SIGTERM between a --force publish's placements cuts nothing: the new export ends beside its own sidecar" \
  || bad "the SIGTERM cut: rc=$RC pair '$(pair_sha "$k")' old $old $(head -c 300 "$td/stderr")"
no_partial "... and leaves no partial or aside name" "$k"
[ ! -e "$k.lock" ] && ok "... and drops --out's lock" || bad "the lock is left: $(ls -A "$k.lock")"
conf35 "FAKE_BODY=$td/body3"
cut_run kill --toolchain v4.35.0 --module Init.Prelude --out "$k" --force
expect1 "a publish step killed (SIGKILL) between its placements is refused, and the shell undoes it" 1 \
  "reason=out-publish-failed the publish of $k exited 137; the export this run placed was removed, the old export was put back, the old sidecar was put back"
[ "$(pair_sha "$k")" = "$new $new" ] && ok "... the old export back beside its own sidecar" || bad "the undone SIGKILL cut: pair '$(pair_sha "$k")', want '$new $new'"
no_partial "... with no partial or aside name left" "$k"
CUT_AT=aside cut_run kill --toolchain v4.35.0 --module Init.Prelude --out "$k" --force
expect1 "a publish step killed inside its set-aside (the old export linked aside, not yet unlinked) is refused, and the shell undoes it" 1 \
  "reason=out-publish-failed the publish of $k exited 137; the old export had not left $k"
[ "$(pair_sha "$k")" = "$new $new" ] && ok "... which leaves the old pair as it was" || bad "the set-aside cut: pair '$(pair_sha "$k")', want '$new $new'"
no_partial "... and drops the aside name, the old export's second name" "$k"
mkdir -p "$td/tmpk"
TMPDIR_UNDER_TEST="$td/tmpk" cut_run killboth --toolchain v4.35.0 --module Init.Prelude --out "$k" --force; cut=$(sha "$k")
[ "$RC" -eq 137 ] && [ "$cut" != "$new" ] && [ ! -e "$k.sidecar.json" ] \
  && ok "a publish killed with its shell (no undo) leaves the new export alone, never beside the old sidecar, set aside first" \
  || bad "the cut with no undo: rc=$RC $(ls "$td" | grep '^k2' | tr '\n' ' ')"
[ "$(ls "$td" | grep -c '^k2\.ndjson\.partial\.[0-9]*\.\(sidecar\.\)\{0,1\}old$')" = 2 ] && ok "... the old pair kept at its aside names" \
  || bad "the asides: $(ls "$td" | grep '^k2' | tr '\n' ' ')"
conf35
run --toolchain v4.35.0 --module Init.Prelude --out "$k" --force; cur=$(sha "$k")
[ "$RC" -eq 0 ] && grep -qF "removed $k.lock, left by pid" "$td/stderr" && [ "$(pair_sha "$k")" = "$cur $cur" ] \
  && ok "the next --force mint removes the lock the killed run left (its owner is gone) and publishes its own pair" \
  || bad "after the kill: rc=$RC pair '$(pair_sha "$k")' $(head -c 300 "$td/stderr")"
rm -f -- "${td:?}"/k2.ndjson.partial.*
mkdir "$k.lock" && echo $$ >"$k.lock/owner"
LEAN_EXPORT_MINT_LOCK_WAIT=0 run --toolchain v4.35.0 --module Init.Prelude --out "$k" --force
expect1 "a publish while another run holds --out's lock is refused when the wait runs out" 1 "reason=out-locked $k.lock is held (owner pid $$)"
[ "$(pair_sha "$k")" = "$cur $cur" ] && [ "$(cat "$k.lock/owner")" = $$ ] && ok "... and --out's pair and that run's lock are left as they were" \
  || bad "the held lock: pair '$(pair_sha "$k")' $(ls -A "$k.lock")"
no_partial "... and no partial name is left" "$k"
rm -rf -- "${k:?}.lock"
printf '%s\n%s\n' "$M" "$RD" >"$td/il.B"
printf '{"export": {"sha256": "%s"}}\n' "$(sha "$td/il.B")" >"$td/il.B.sidecar"
conf35 "FAKE_BODY=$td/body2"
B_PARTIAL="$td/il.B" TOOL_UNDER_CUT="$TOOL" CUT_OTHER="$td/other.sh" CUT_LOG="$td/other.log" \
  cut_run other --toolchain v4.35.0 --module Init.Prelude --out "$td/il.ndjson" --force; a=$(sha "$td/il.ndjson")
[ "$RC" -eq 0 ] && [ "$(pair_sha "$td/il.ndjson")" = "$a $a" ] && [ "$a" != "$(sha "$td/il.B")" ] \
  && grep -qF "reason=out-locked $td/il.ndjson.lock is held" "$td/other.log" \
  && ok "another run publishing to the same --out between this run's placements is held off by the lock: --out keeps this run's pair" \
  || bad "the interleaving: rc=$RC pair '$(pair_sha "$td/il.ndjson")' this run $a, other: $(head -c 300 "$td/other.log")"
conf35
# An old sidecar --force cannot set aside: immutable (chflags uchg), so link(2) fails with EPERM.
printf 'old\n' >"$td/im.ndjson"; printf 'old sidecar\n' >"$td/im.ndjson.sidecar.json"
chflags uchg "$td/im.ndjson.sidecar.json"
run --toolchain v4.35.0 --module Init.Prelude --out "$td/im.ndjson" --force
chflags nouchg "$td/im.ndjson.sidecar.json"
expect1 "a --force publish whose old sidecar cannot be set aside (immutable: link(2) fails, EPERM) is refused by name" 1 \
  "reason=out-publish-failed cannot set the old sidecar at $td/im.ndjson.sidecar.json aside ("
grep -qF "); the old export was put back" "$td/stderr" && [ "$(cat "$td/im.ndjson")" = old ] \
  && [ "$(cat "$td/im.ndjson.sidecar.json")" = "old sidecar" ] && [ "$(ls "$td" | grep -c '^im\.ndjson')" = 2 ] \
  && ok "... and the old export, set aside before it, is put back beside it, with no partial or aside name left" \
  || bad "the immutable sidecar: $(ls "$td" | grep '^im' | tr '\n' ' ') $(head -c 400 "$td/stderr")"
run --toolchain v4.35.0 --module Init.Prelude --out "$td/ok.ndjson"
[ "$RC" -eq 0 ] && [ -s "$td/ok.ndjson" ] && [ -s "$td/ok.ndjson.sidecar.json" ] && [ "$(ls "$td" | grep -c '^ok\.ndjson')" = 2 ] \
  && ok "a publish without --force leaves the export and its sidecar and no partial name" || bad "ok: rc=$RC $(ls "$td" | grep '^ok')"
[ -z "$(ls -A "$td/tmp")" ] && ok "no run left its gate start marker in TMPDIR" || bad "TMPDIR holds: $(ls -A "$td/tmp" | head -5)"

echo "lean_export_mint selftest: $pass passed, $fails failed"
[ "$fails" -eq 0 ]
