#!/usr/bin/env bash
# Compile `clean-kernel` with the Trust compiler and its trust-ir CODEGEN FLIP
# on, then ratchet the measured lowering/flip counts.
#
# This is the committed counterpart of the session-local driver that produced
# `data/crystal_a0_a6_probe.json`. Before it existed, the only trustc-invoking
# thing in this repo was `scripts/trust_verify_ratchet.sh`, which drives a
# DIFFERENT mechanism (`-Ztrust-verify`, the Level-0 verifier). Nothing in-tree
# exercised the path the crystal is about: THIR -> trust-ir -> derived-MIR
# differential -> codegen flip.
#
#   designs/2026-07-29-execution-plan-crystal.md §5
#   designs/2026-07-29-crystal-deployed-kernel-bridge.md §6.0
#
# `rust-toolchain.toml` selects `channel = "trust"` for ordinary repo builds.
# This script is an opt-in CODEGEN FLIP measurement, separate from ordinary
# unverified builds and the verification lane. Historical measurement:
# 2026-08-11 only 1.28 % of clean-kernel's `fn` bodies flipped (185 of
# 13,767 bodies; 153 codegen + 32 CTFE). Those dated counts do not describe
# the current compiler. This driver ratchets measurements under its pinned
# compiler identity.
#
# THE AXIS INVENTORY (added 2026-08-15 — read this before adding a measurement).
#
# This script used to ratchet FOUR numbers: `lowered`, `spliced`, `flip_events`,
# `mismatch`. The coverage artifact carries thirty-nine. That gap is not a
# hypothetical: trust `80c7e86f55` (2026-08-13) turned 38 `agreed` verdicts into
# `not-run` -- 36 interpreter + 2 seam, 21 of them flipping bodies -- and dropped
# the CTFE flip lane from 32/32 semantically backed to 11/32. It went unnoticed
# for two days, because ALL FOUR watched numbers were bit-identical across the
# regression (measured: lowered 9067, spliced 7571, derived-MIR agreed 1542,
# mismatch 0, flip events 209 on both sides). It was found only because an
# unrelated lane ran a same-HEAD A/B for a different reason.
#
# That was the THIRD time this class bit: `lowered`/`spliced` were once not
# columns in the review harness (hid three stub collapses), `markers_class` was
# not an axis (hid a fourth), and then this.
#
# So the axis list is now WRITTEN DOWN, in `scripts/trust_ir_axes.py::AXES`, with
# a direction for every axis the artifact carries -- including the ones
# deliberately NOT gated, each with its measured reason. Run
# `scripts/trust_ir_axes.py table` for the inventory. A gated axis missing from
# the baseline is RED, never a silent pass.
#
#   reports/crystal-38-lost-agreed-bisect-2026-08-15.md   the regression
#   reports/trust-ir-axis-gate-2026-08-15.md              this gate
#
# Usage:
#   scripts/trust_ir_build.sh                     # build + ratchet vs baseline
#   scripts/trust_ir_build.sh --negative-control   # -Ztrust-ir-flip=no; must be 0 flips
#   scripts/trust_ir_build.sh --tighten            # seed new axes / raise improving ones
#   scripts/trust_ir_build.sh --print-only         # measure, report, never fail on counts
#   scripts/trust_ir_build.sh --rebaseline         # NEW compiler only: every axis from this run
#
# `--tighten` (the old spelling `--update` still works) can only ever make the
# baseline STRICTER: it seeds an axis that has no baseline and raises one whose
# measurement is strictly better. It never lowers a baseline, so it is
# arithmetically incapable of turning a red axis green.
#
# THE COMPILER PIN (2026-10-08; docs/DECISIONS.md R25). The counts are a
# property of the compiler as much as of clean-kernel: the baseline recorded
# `lowered` 9068 over clean-kernel 71e1ce8be under an August trustc (stamp
# 94147b34f), and the same source measures 7329 under the sealed 321aaeda7.
# Until this date the baseline MIXED compilers (`--tighten` raised what a newer
# compiler improved and kept the older one's values for what it lowered), so
# the ratchet sat red on a comparison between two compilers --
# `reports/trust-ir-ratchet-verdict-2026-08-13.md` was the same class -- and
# could be demonstrated by nothing. The baseline now pins ONE
# compiler (`compiler`: sha256 of `trustc` and of the `librustc_driver` it
# loads), checked BEFORE the build:
#   * the ratchet and `--tighten` refuse any other compiler (COMPILER MISMATCH),
#     so a count is compared only with one the same compiler produced, and a
#     regression under the pinned compiler stays red;
#   * `--rebaseline` takes EVERY gated axis from one run, and only under a
#     compiler that is NOT the pinned one -- under the pinned compiler it refuses
#     before building (a lower count there is a regression). It also refuses a
#     run with a fatal invariant or a moved REBASELINE_FIXED pin (no proof
#     authority, no native verification request, subject clean_kernel).
#
# Environment:
#   TRUST_STAGE1_BIN / TRUSTC / TRUST_REPO_ROOT   toolchain discovery (shared
#                                                 with trust_verify_ratchet.sh)
#   TRUST_IR_BUILD_TARGET_DIR                     CARGO_TARGET_DIR override
#   TRUST_IR_BUILD_DUMP                           where to leave the IR dump
#                                                 (the build log and the measured
#                                                 axis JSON are left there too)
#
# RELEASE-SHAPED is load-bearing: `infer_type` is cfg-split and the crystal is
# about the DEPLOYED body, so `--release` (debug_assertions off) plus
# `-Cdebuginfo=0` are part of the measurement, not conveniences.
#
# THE -O0 ARGV DEFECT, and why this script now PINS the profile instead of
# inheriting it (recorded 2026-08-13).
#
# rustc infers `debug-assertions` FROM the optimization level when the flag is
# absent: ON at `-Copt-level=0`, OFF above. Cargo does not compensate -- it
# emits NO `-C debug-assertions` at all for the release profile, because `false`
# is already rustc's default at -O3. So appending an opt-level override to a
# release build silently flips debug_assertions ON. Measured here 2026-08-13,
# rustc 1.97.1 / cargo 1.97.1 (aarch64-apple-darwin), on a
# `#[cfg(debug_assertions)] compile_error!` probe crate:
#
#   cargo rustc --release --lib                                  -> compiles (OFF)
#   cargo rustc --release --lib -- -Copt-level=0                 -> ERRORS   (ON)
#   cargo rustc --release --lib -- -Copt-level=0 \
#                                  -Cdebug-assertions=off        -> compiles (OFF)
#   cargo rustc --release --lib -v -- -Copt-level=0              -> cargo's own
#                                    rustc argv contains no `-C debug-assertions`
#
# This script does NOT override the opt level, so it was never mis-measured.
# It is pinned anyway for two reasons: the property the crystal depends on
# should be STATED in the argv rather than inferred from a profile name, and the
# next person to add an `-Copt-level=` here must not silently swap the program.
# The effect if it ever did: ~30 `#[cfg(not(debug_assertions))]` bodies vanish --
# `infer_type_fast{,_impl,_inner,_arc}`, `try_get_cached_type`,
# `cache_type_result`, `infer_cubical` x8, `infer_zfc` x5 -- and
# `TypeChecker::infer_type` becomes its DEBUG twin. A different program.
#
# The pin is not left on trust: after the build, the PROFILE ASSERTION below
# reads the release-only spine back out of the coverage dump and fails closed if
# it is missing.
set -uo pipefail

REPO="$(cd "$(dirname "$0")/.." && pwd -P)"
BASELINE="$REPO/data/trust_ir_build_baseline.json"
BODIES_FILE="$REPO/data/trust_ir_build_agreed_bodies.json"
RATCHET_SCRIPT="$REPO/scripts/trust_verify_ratchet.sh"
AXES="$REPO/scripts/trust_ir_axes.py"

# R7 PINNED INPUTS (docs/GATE_REGISTRY.md R7; 2026-11-13). Every verdict here
# comes from two other files this script runs: the comparator ($AXES) and the
# toolchain discovery ($RATCHET_SCRIPT --locate-stage1). Declared, so
# check_gate_registry.py pins their bytes beside this script's and an edit to
# either reds this row until its arms replay (E6's finding, e09dbb255: the
# comparator changed after the 2026-10-08 demonstration and nothing saw it).
ANSWERS_PINNED_INPUTS=True

fail() { echo "TRUST-IR BUILD FAIL: $*" >&2; exit 1; }
note() { echo "  $*"; }

# A successful native compile can still withhold the TrustIR publication.
# Surface its actual semantic refusal before suggesting a missing dump sink.
require_coverage() {
  local coverage="$1" log="$2"
  [[ -f "$coverage" ]] && return 0
  if grep -Fq 'trust-ir-lower semantic finalization failed:' "$log"; then
    grep -F 'trust-ir-lower semantic finalization failed:' "$log" >&2
    fail "compiler refused TrustIR semantic publication; no coverage json at $coverage (log: $log)"
  fi
  fail "no coverage json at $coverage — the dump sink did not attach (log: $log)"
}

MODE="ratchet"; FLIP="yes"
for arg in "$@"; do
  case "$arg" in
    --negative-control) FLIP="no"; MODE="negative" ;;
    --tighten|--update) MODE="tighten" ;;
    --print-only)       MODE="print" ;;
    --rebaseline)       MODE="rebaseline" ;;
    --pinned-inputs)    printf '%s\n' "${AXES#"$REPO"/}" "${RATCHET_SCRIPT#"$REPO"/}"; exit 0 ;;
    -h|--help)          sed -n '2,92p' "$0"; exit 0 ;;
    *)                  fail "unknown argument: $arg" ;;
  esac
done

[[ -f "$AXES" ]] || fail "missing $AXES — the axis inventory IS the gate"
# The comparator proves itself before it is trusted to judge a build: every
# gated axis must be able to go red on its own, an unbaselined axis must be red,
# and `tighten` must be unable to rescue a regression. Cheap (no compiler) and
# it fails closed, so a broken comparator can never report a green.
python3 "$AXES" selftest >/dev/null 2>&1 \
  || fail "scripts/trust_ir_axes.py selftest FAILED — the comparator is broken; run it directly"

# ── toolchain ───────────────────────────────────────────────────────────────
# Reuse the ratchet's discovery verbatim rather than re-deriving it: explicit
# configuration is authoritative and invalid explicit paths fail closed; a
# machine with no Trust checkout exits 2 and the caller decides what that means.
if STAGE1="$(bash "$RATCHET_SCRIPT" --locate-stage1)"; then
  :
else
  rc=$?
  [[ "$rc" -eq 2 ]] && { echo "TRUST-IR BUILD SKIP: no local Trust stage1 toolchain"; exit 2; }
  fail "Trust stage1 discovery is invalid or ambiguous; set TRUST_STAGE1_BIN explicitly"
fi
TRUSTC_BIN="${TRUSTC:-$STAGE1/trustc}"
[[ -x "$TRUSTC_BIN" ]] || fail "stage1 trustc not executable at $TRUSTC_BIN"

# The version stamp is NOT the source identity: CFG_VER_HASH is the trust git
# HEAD at BUILD time, so a stage2 binary can carry a newer stamp than a stage1
# that was linked from a dirty tree carrying later work. Record it, never
# reason from it.
TRUSTC_VERSION="$("$TRUSTC_BIN" -vV 2>/dev/null | tr '\n' ' ')"
TRUSTC_SHA="$(shasum -a 256 "$TRUSTC_BIN" 2>/dev/null | awk '{print $1}')"

SCRATCH="$(mktemp -d)"; trap 'rm -rf "$SCRATCH"' EXIT

# ── the compiler's identity, and the pin, BEFORE anything is built ─────────
# The digests are the identity (the stamp is not, see above): the `trustc`
# binary and the ONE `librustc_driver` of its sysroot, which is where the
# lowering actually lives -- two Trust builds can ship a byte-identical driver
# shim. Exactly one driver library is required; zero or several is a sysroot
# this script cannot name, and it fails closed.
SYSROOT="$("$TRUSTC_BIN" --print sysroot 2>/dev/null)" \
  || fail "\`$TRUSTC_BIN --print sysroot\` failed -- the compiler's identity cannot be read"
DRIVERS=()
for lib in "$SYSROOT"/lib/librustc_driver-*.dylib "$SYSROOT"/lib/librustc_driver-*.so; do
  [[ -f "$lib" ]] && DRIVERS+=("$lib")
done
[[ "${#DRIVERS[@]}" -eq 1 ]] \
  || fail "expected exactly one librustc_driver in $SYSROOT/lib, found ${#DRIVERS[@]} -- the compiler's identity is ambiguous"
DRIVER_SHA="$(shasum -a 256 "${DRIVERS[0]}" 2>/dev/null | awk '{print $1}')"
COMPILER_JSON="$SCRATCH/compiler.json"
python3 - "$COMPILER_JSON" "$TRUSTC_VERSION" "$TRUSTC_SHA" "$DRIVER_SHA" <<'PY' \
  || fail "could not record the compiler's identity"
import json, sys
out, stamp, trustc_sha, driver_sha = sys.argv[1:5]
json.dump({"version_stamp": stamp.strip(), "trustc_sha256": trustc_sha,
           "driver_sha256": driver_sha}, open(out, "w"), indent=1)
PY
if [[ "$MODE" == "ratchet" || "$MODE" == "tighten" || "$MODE" == "rebaseline" ]]; then
  [[ -f "$BASELINE" ]] || fail "no baseline at $BASELINE -- seed it with --rebaseline"
  CC_RC=0
  CC_MSG="$(python3 "$AXES" compiler-check --baseline "$BASELINE" --compiler "$COMPILER_JSON")" || CC_RC=$?
  if [[ "$MODE" == "rebaseline" && "$CC_RC" -eq 0 ]]; then
    fail "REBASELINE REFUSED: this run's compiler IS the one the baseline pins
       ($CC_MSG). Under one compiler an axis moves only by --tighten, which never
       loosens: a lower count under the pinned compiler is a regression, not a re-baseline."
  fi
  if [[ "$MODE" != "rebaseline" && "$CC_RC" -ne 0 ]]; then
    echo "TRUST_IR_BUILD=refused:compiler-mismatch"
    fail "$CC_MSG"
  fi
fi
DUMP="${TRUST_IR_BUILD_DUMP:-$SCRATCH/dump}"
TDIR="${TRUST_IR_BUILD_TARGET_DIR:-$SCRATCH/target}"
rm -rf "$DUMP" && mkdir -p "$DUMP" "$TDIR"
# Retain producer diagnostics even when no coverage commit marker is published.
# A valid native build can still refuse crate-level TrustIR finalization.
LOG="$DUMP/clean_kernel.build.log"

# ── the rustc wrapper ───────────────────────────────────────────────────────
# Two things plain RUSTFLAGS cannot do: apply the lowering configuration
# uniformly to every unit cargo drives (proc-macros and build scripts included),
# and attach the dump sink + flip log to the SUBJECT UNIT ONLY. The second is
# what makes attribution provable — every "compiled from trust-ir" line in the
# log then demonstrably comes from clean_kernel, which is exactly the mistake
# that produced the retracted "4291 flipped bodies" figure.
WRAP="$SCRATCH/trustc-wrap.sh"
cat > "$WRAP" <<'WRAPPER'
#!/bin/sh
set -e
# Probe invocations must pass through untouched: cargo parses their exact
# stdout and an extra -Z flag can change or reject it.
for a in "$@"; do
  case "$a" in
    -vV|--version|--print|--print=*) exec "$TRUSTC" "$@" ;;
  esac
done
# `-Cdebug-assertions=off` is PINNED, not inherited from the release profile.
# See the -O0 argv defect note in this file's header: the moment anyone appends
# an `-Copt-level=` here, cargo's silence about debug-assertions turns the
# subject into the DEBUG kernel. Spelling it makes the profile a fact of the
# argv, and `clean_kernel.argv` records it.
EXTRA="-Ztrust-verify=off -Ztrust-ir-lower=on -Cdebuginfo=0 -Cdebug-assertions=off"
case " $* " in
  *" --crate-name clean_kernel "*)
    EXTRA="$EXTRA -Ztrust-dump=ir:$TIB_DUMP -Ztrust-ir-flip=$TIB_FLIP"
    { printf 'ARGV:'; for a in "$@"; do printf ' %s' "$a"; done; printf ' %s\n' "$EXTRA"; } \
      > "$TIB_DUMP/clean_kernel.argv"
    RUSTC_LOG=rustc_mir_transform::trust_ir_flip=info exec "$TRUSTC" "$@" $EXTRA
    ;;
esac
exec "$TRUSTC" "$@" $EXTRA
WRAPPER
chmod +x "$WRAP"

echo "== trust-ir build: clean-kernel, release, flip=$FLIP =="
note "trustc: $TRUSTC_BIN"
note "stamp:  $TRUSTC_VERSION"

# The subject unit MUST actually recompile, or there is no dump and no flip
# event to count. With a reused target dir cargo would report success having
# done nothing, so drop clean-kernel's artifacts first: the measurement is
# defined as a non-incremental compile of the subject crate.
#
# Keep the cleanup on the SAME compiler identity as the measured build and
# fail closed.  This is not cosmetic in a Trust-pinned checkout: Cargo queries
# rustc even for `cargo clean`, and the workspace config carries
# `-Ztrust-verify=off`.  A stock stable rustc rejects that query.  Until
# 2026-08-21 the error was redirected away behind `|| true`, so a reused target
# could retain clean-kernel and the following build could succeed without
# emitting any dump at all.  The missing-coverage check caught that state, but
# only after the script had falsely claimed it had forced a subject rebuild.
if ! RUSTC="$TRUSTC_BIN" CARGO_TARGET_DIR="$TDIR" \
    targo clean --locked --release -p clean-kernel >/dev/null 2>&1; then
  fail "could not remove the clean-kernel subject artifacts with the measured compiler"
fi

env -u CARGO_ENCODED_RUSTFLAGS -u CARGO_BUILD_RUSTFLAGS \
    -u TRUST_VERIFY_PRIMARY_ONLY -u SOURCE_DATE_EPOCH -u TRUST_ENUM_DECLINE_CENSUS \
  RUSTC="$WRAP" TRUSTC="$TRUSTC_BIN" TIB_DUMP="$DUMP" TIB_FLIP="$FLIP" \
  CARGO_TARGET_DIR="$TDIR" CARGO_INCREMENTAL=0 \
  targo --unverified build --locked --release -p clean-kernel --lib > "$LOG" 2>&1
RC=$?
if [[ "$RC" -ne 0 ]]; then
  tail -40 "$LOG" >&2
  fail "trustc build of clean-kernel exited $RC (log: $LOG)"
fi

# `--lib` (2026-09-20): the subject is the crate's LIBRARY -- the trust-ir
# module, the coverage report and every flip event this script measures come
# from the lib unit, and `clean_kernel.argv` records that unit's argv. The three
# BINARY targets of clean-kernel fail to link under every v13 sysroot on this box
# (`the crate panic_abort does not have the panic strategy abort` -- a sysroot
# property, identical in control and subject, recorded in CLAUDE.md's crystal
# section), and until today that failure arrived AFTER the lib's IR was
# published and aborted this script right here: exit 101, no axes.json, no
# retained build log, on the 2026-09-09 subject dump (its log, line 54) and on
# every 2026-09-20 attempt. A measurement driver that cannot reach its own
# measure step on the only box that runs it is not a driver; the bins were never
# the subject.

# ── measure ─────────────────────────────────────────────────────────────────
COVERAGE="$DUMP/clean_kernel.coverage.json"
require_coverage "$COVERAGE" "$LOG"

# The build log is an INPUT to the measurement (flip events live only there), so
# it is kept next to the dump rather than in the vanishing scratch dir. Without
# it the flip-to-coverage join — and therefore the "semantically backed" axes —
# cannot be recomputed after the fact, which is precisely the position the
# 2026-08-13 loss left every earlier lane in.
# The build wrote LOG here from the start, including failed publication attempts.
MEASURED="$DUMP/clean_kernel.axes.json"
python3 "$AXES" measure --coverage "$COVERAGE" --log "$LOG" --out "$MEASURED" \
  || fail "axis extraction failed over $COVERAGE + $LOG"

read -r BODIES LOWERED SPLICED AGREED MISMATCH LINEAGE_ROWS INTERP_AGREED SEAM_AGREED BACKED <<<"$(
  python3 -c 'import json,sys
m = json.load(open(sys.argv[1]))["measured"]
print(m["bodies"], m["lowered"], m["spliced"], m["derived_mir_agreed"], m["mismatch"],
      m["lineage_rows"], m["interpreter_agreed"], m["seam_agreed"], m["flip_backed_total"])' "$MEASURED"
)"

# ── PROFILE ASSERTION: is the subject the DEPLOYED kernel? ──────────────────
# A pinned flag is a claim; this is the measurement. Every name below is behind
# `#[cfg(not(debug_assertions))]` in crates/clean-kernel/src/tc/, so its presence
# in the dump is one-sided proof that debug_assertions was OFF and that the body
# reachable from `TypeChecker::infer_type` is the RELEASE one. If a future edit
# appends an opt-level override (or a profile change turns assertions on), the
# spine disappears and this fails closed instead of quietly re-baselining the
# ratchet against a different program.
SPINE_MISSING="$(
  python3 - "$COVERAGE" <<'PY'
import json, sys
required = [
    "infer_type_fast", "infer_type_fast_impl", "infer_type_fast_inner",
    "infer_type_fast_arc", "try_get_cached_type", "cache_type_result",
]
paths = {b.get("def_path", "") for b in json.load(open(sys.argv[1]))["bodies"]}
leaves = {p.rsplit("::", 1)[-1] for p in paths}
print(" ".join(n for n in required if n not in leaves))
PY
)"
if [[ -n "$SPINE_MISSING" ]]; then
  fail "PROFILE ASSERTION FAILED: the release-only inference spine is absent from the dump ($SPINE_MISSING).
       Every one of those is #[cfg(not(debug_assertions))]. Their absence means this build had
       debug_assertions ON, i.e. the subject is the DEBUG kernel, not the deployed one -- almost
       certainly an appended -Copt-level= without -Cdebug-assertions=off. Read the -O0 argv defect
       note at the top of this script. Do NOT re-baseline from this run."
fi
note "profile assertion ok: release-only inference spine present (6/6)"

CODEGEN_FLIPS="$(grep -c 'trust-ir-flip: compiled from trust-ir' "$LOG" || true)"
CTFE_FLIPS="$(grep -c 'trust-ir-flip: CTFE compiled from trust-ir' "$LOG" || true)"
FLIPS=$((CODEGEN_FLIPS + CTFE_FLIPS))
FOREIGN="$(grep 'trust-ir-flip: .*compiled from trust-ir' "$LOG" | grep -cv clean_kernel || true)"

# The grep counts above and the extractor's own counts are INDEPENDENT readings
# of the same log — one by line count, one by parsing `did=DefId(krate:index`.
# If they disagree the log shape changed under us and every joined axis
# (`flip_backed_*`) is suspect, so this fails closed rather than reporting a
# number nobody can reproduce by hand.
read -r X_TOTAL X_CG X_CTFE X_FOREIGN X_UNJOIN <<<"$(
  python3 -c 'import json,sys
d = json.load(open(sys.argv[1])); m, i = d["measured"], d["invariants"]
print(m["flip_events_total"], m["flip_events_codegen"], m["flip_events_ctfe"],
      i["foreign_flip_events"], i["flip_events_unjoinable"])' "$MEASURED"
)"
[[ "$X_CG" -eq "$CODEGEN_FLIPS" && "$X_CTFE" -eq "$CTFE_FLIPS" && "$X_FOREIGN" -eq "$FOREIGN" ]] \
  || fail "flip-log readings disagree: grep says $CODEGEN_FLIPS/$CTFE_FLIPS/$FOREIGN, the parser says $X_CG/$X_CTFE/$X_FOREIGN — the log shape changed, do not trust the joined axes"

note "bodies $BODIES  lowered $LOWERED  spliced $SPLICED  derived-MIR agreed $AGREED  mismatch $MISMATCH"
note "interpreter agreed $INTERP_AGREED   seam agreed $SEAM_AGREED   lineage rows $LINEAGE_ROWS/$BODIES"
note "flips $FLIPS ($CODEGEN_FLIPS codegen + $CTFE_FLIPS CTFE), $BACKED semantically backed, non-clean_kernel events: $FOREIGN"

# ── invariants that hold in EVERY mode ──────────────────────────────────────
# A flip requires DerivedAgreed, so a clean_kernel flip count above the crate's
# agreed count is arithmetically impossible and means the events were
# mis-attributed. This is the check the retracted 4291 figure would have failed.
[[ "$FOREIGN" -eq 0 ]] \
  || fail "$FOREIGN flip events did not name clean_kernel — attribution is broken, the counts below are not crate numbers"
[[ "$FLIPS" -le "$AGREED" ]] \
  || fail "flips ($FLIPS) exceed derived-MIR agreed ($AGREED); a flip requires DerivedAgreed, so this is impossible and the measurement is wrong"
# Every flip event must land on a coverage row by `def_index`. If it does not,
# `flip_backed_*` silently under-counts and the gate on it becomes decorative.
[[ "$X_UNJOIN" -eq 0 ]] \
  || fail "$X_UNJOIN flip event(s) do not join to any coverage row by def_index — the semantic-backing axes cannot be computed"

if [[ "$MODE" == "negative" ]]; then
  [[ "$FLIPS" -eq 0 ]] \
    || fail "NEGATIVE CONTROL: -Ztrust-ir-flip=no still produced $FLIPS flip events"
  echo "NEGATIVE CONTROL OK: 0 flip events with -Ztrust-ir-flip=no"
  exit 0
fi

if [[ "$MODE" == "print" ]]; then
  echo ""
  python3 "$AXES" check --measured "$MEASURED" --baseline "$BASELINE" --bodies "$BODIES_FILE" \
    --compiler "$COMPILER_JSON" || true
  echo "PRINT-ONLY: no ratchet applied (axis table above is informational)"
  exit 0
fi

if [[ "$MODE" == "rebaseline" ]]; then
  # Every gated axis from THIS run, the compiler pinned, the body sets
  # rewritten. The comparator refuses again here on its own terms (pinned
  # compiler, fatal invariant, missing axis, a REBASELINE_FIXED pin moved).
  python3 "$AXES" rebaseline --measured "$MEASURED" --baseline "$BASELINE" \
    --bodies "$BODIES_FILE" --compiler "$COMPILER_JSON" --write \
    || fail "the comparator refused the re-baseline -- see its reason above"
  python3 "$AXES" check --measured "$MEASURED" --baseline "$BASELINE" --bodies "$BODIES_FILE" \
    --compiler "$COMPILER_JSON" >/dev/null \
    || fail "the re-baselined file does not pass its own measurement -- not written correctly"
  echo "BASELINE RE-MINTED under $TRUSTC_VERSION: $BASELINE (+ body sets: $BODIES_FILE)"
  exit 0
fi

# ── ratchet ─────────────────────────────────────────────────────────────────
# Every axis in `scripts/trust_ir_axes.py::AXES` is evaluated, ALL of them are
# printed, and the failures are reported together. It deliberately does not stop
# at the first red: a first-failure exit would make every axis behind it
# invisible — the same shape of blindness this gate exists to remove.
echo ""
if python3 "$AXES" check --measured "$MEASURED" --baseline "$BASELINE" --bodies "$BODIES_FILE" \
    --compiler "$COMPILER_JSON"; then
  RATCHET_RC=0
else
  RATCHET_RC=1
fi

if [[ "$MODE" == "tighten" ]]; then
  # Seed unbaselined axes, raise improving ones, NEVER lower one. This runs even
  # when the check is red, because that is the whole point: an axis that
  # regressed keeps its old baseline and stays red, while the axes that have no
  # baseline at all stop being blind spots.
  # Under the pinned compiler only (checked before the build, and again by the
  # comparator): the pin IS the provenance of every value, so nothing else is
  # recorded per run; `axis_updated` says which axes each run moved.
  python3 "$AXES" tighten --measured "$MEASURED" --baseline "$BASELINE" \
                          --bodies "$BODIES_FILE" --compiler "$COMPILER_JSON" --write \
    || fail "tighten failed"
  echo "BASELINE TIGHTENED: $BASELINE  (+ body sets: $BODIES_FILE)"
  echo "  A tighten never lowers a baseline, so a red axis stays red — re-run without"
  echo "  --tighten to see the gate's verdict."
  exit 0
fi

[[ "$RATCHET_RC" -eq 0 ]] || fail "the axis ratchet is RED — see the table above"

echo "TRUST-IR BUILD OK"
