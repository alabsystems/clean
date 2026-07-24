#!/usr/bin/env bash
# Twin monotonic ratchet for Trust Level-0 verification of clean-kernel.
#
#   SOUNDNESS ratchet (never relaxed): the soundness canaries
#     (tests/trust_verify/vacuity_sentinel.rs) contain genuinely-false safety
#     obligations that a SOUND verifier must leave failed/unknown. If any flips
#     to `proved`, the verifier is unsound (vacuous UNSAT context) — block.
#   COVERAGE ratchet (per-function common-set diff): the HARD gate is that NO
#     function FULLY VERIFIED in the baseline becomes GENUINELY unverified now
#     (failed, or a non-work-budget unknown). It is keyed on each function's
#     source location (the verdict note's `-->`), which covers both verified and
#     incomplete functions, so the "common set" is the functions present in BOTH
#     runs. This replaces the old ABSOLUTE-total gate (unproved>ceiling /
#     verified<floor), which was memory-guard-NONDETERMINISTIC — the ~33.6GB
#     VC-gen guard skips a varying swath of obligations run-to-run, so absolute
#     totals drift and could spuriously trip a "regression" with 0 functions
#     actually regressed. Aggregate floor/ceiling are kept as SOFT info only.
#     A function whose only new non-verification is a TrustVcGenWorkBudgetExceeded
#     (memory-guard) unknown is NOT a regression — that is the nondeterministic
#     swath, not a real loss. Per-function parse+diff lives in
#     scripts/trust_verify_coverage_diff.py; baseline in
#     data/trust_verify_function_baseline.json.
#
# Goal: drive `unproved` to 0 while soundness stays perfect.
#
# Usage:
#   scripts/trust_verify_ratchet.sh --soundness            # fast: canaries only
#   scripts/trust_verify_ratchet.sh --coverage             # heavy: per-function diff gate
#   scripts/trust_verify_ratchet.sh --coverage --update    # seed/re-anchor the per-function baseline
#   scripts/trust_verify_ratchet.sh                        # all gates (no baseline write)
set -uo pipefail

REPO="$(cd "$(dirname "$0")/.." && pwd -P)"
RATCHET="$REPO/data/trust_verify_ratchet.json"
FUNC_BASELINE="$REPO/data/trust_verify_function_baseline.json"
COVERAGE_DIFF="$REPO/scripts/trust_verify_coverage_diff.py"
SOUNDNESS_GATE="$REPO/scripts/trust_verify_soundness_gate.py"
SENTINEL="$REPO/tests/trust_verify/vacuity_sentinel.rs"
fail() { echo "RATCHET FAIL: $*" >&2; exit 1; }

# Locate one Trust stage1 without baking a developer username, host triple, or
# checkout layout into the gate. Explicit configuration is authoritative and
# invalid explicit paths fail closed. Otherwise prefer a `trustc` already on
# host stage1 in a colocated Trust checkout (binding the gate to the source
# beside Clean), then a unique staged build, and finally `trustc` on PATH.
locate_stage1_bin() {
  local configured="${TRUST_STAGE1_BIN:-}"
  local trustc="${TRUSTC:-}"
  local candidate host root path found=""

  if [[ -n "$configured" ]]; then
    if [[ -x "$configured" && ! -d "$configured" ]]; then
      configured="$(cd "$(dirname "$configured")" && pwd -P)"
    fi
    if [[ ! -x "$configured/trustc" ]]; then
      echo "configured TRUST_STAGE1_BIN has no executable trustc: $configured" >&2
      return 1
    fi
    printf '%s\n' "$(cd "$configured" && pwd -P)"
    return 0
  fi

  if [[ -n "$trustc" ]]; then
    if [[ ! -x "$trustc" ]]; then
      echo "configured TRUSTC is not executable: $trustc" >&2
      return 1
    fi
    printf '%s\n' "$(cd "$(dirname "$trustc")" && pwd -P)"
    return 0
  fi

  host="$(rustc -vV 2>/dev/null | sed -n 's/^host: //p' | head -1 || true)"
  for root in \
    "${TRUST_REPO_ROOT:-}" \
    "$REPO/../.." \
    "$REPO/../trust" \
    "$REPO/../../trust"
  do
    [[ -n "$root" && -d "$root/build" ]] || continue
    root="$(cd "$root" && pwd -P)"
    if [[ -n "$host" && -x "$root/build/$host/stage1/bin/trustc" ]]; then
      printf '%s\n' "$root/build/$host/stage1/bin"
      return 0
    fi
    for path in "$root"/build/*/stage1/bin/trustc; do
      [[ -x "$path" ]] || continue
      candidate="$(cd "$(dirname "$path")" && pwd -P)"
      if [[ -n "$found" && "$found" != "$candidate" ]]; then
        echo "multiple Trust stage1 toolchains found; set TRUST_STAGE1_BIN explicitly" >&2
        return 1
      fi
      found="$candidate"
    done
  done

  if [[ -n "$found" ]]; then
    printf '%s\n' "$found"
    return 0
  fi
  if candidate="$(command -v trustc 2>/dev/null)" && [[ -x "$candidate" ]]; then
    printf '%s\n' "$(cd "$(dirname "$candidate")" && pwd -P)"
    return 0
  fi
  return 2
}

if [[ "${1:-}" == "--locate-stage1" ]]; then
  locate_stage1_bin
  exit $?
fi

if STAGE1="$(locate_stage1_bin)"; then
  :
else
  locate_rc=$?
  if [[ "$locate_rc" -eq 2 ]]; then
    fail "stage1 trustc not found — set TRUST_STAGE1_BIN, set TRUSTC, put trustc on PATH, or build a colocated Trust toolchain"
  fi
  exit "$locate_rc"
fi
if [[ -n "${TRUSTC:-}" ]]; then
  TRUSTC_BIN="$(cd "$(dirname "$TRUSTC")" && pwd -P)/$(basename "$TRUSTC")"
else
  TRUSTC_BIN="$STAGE1/trustc"
fi
export PATH="$STAGE1:$HOME/.cargo/bin:/opt/homebrew/bin:$PATH"

# MODE selects which gate(s) to run; UPDATE re-baselines on an improvement.
# Accepts both the canonical `--coverage --update` form and the legacy standalone
# `--update` (which runs all gates and re-baselines). UPDATE=1 iff `--update`
# appears in ANY argument position.
MODE="all"; UPDATE=0
for arg in "$@"; do
  case "$arg" in
    --update) UPDATE=1 ;;
    --soundness|--coverage|--benchmark) MODE="$arg" ;;
  esac
done
# A bare `--update` (no gate selector) keeps MODE=all: it runs all gates and the
# combined path's run_coverage re-baselines because UPDATE=1. `--coverage --update`
# runs only the coverage gate and re-baselines. Either way UPDATE drives the write.
SCRATCH="$(mktemp -d)"; trap 'rm -rf "$SCRATCH"' EXIT
have() { command -v "$1" >/dev/null 2>&1; }

[ -x "$TRUSTC_BIN" ] || fail "stage1 trustc not built at $TRUSTC_BIN — run the trust toolchain build first"

# --- sum 'Trust verification: N proved, M failed, K unknown ... R runtime-checked' ---
# Portable (BSD/macOS awk has no match()-with-array): grep the lines, sum fields.
# proved/failed/unknown are always present (-> $3 $5 $7); runtime-checked is summed
# separately (0 if a verifier build omits it) so the main extraction stays robust.
# RUNTIME-CHECKED counts as VERIFIED (the obligation is enforced by an inserted
# runtime guard — sound, no false-cert), but is NOT a static proof; the goal drives
# it to 0 (all statically proved). A `proved -> runtime-checked` flip is therefore
# soundness-neutral and must NOT trip the coverage gate (an earlier proved-floor did).
sum_verdicts() { # $1=logfile -> echoes "proved failed unknown runtime_checked"
  local pfu rc
  pfu=$(grep -oE 'Trust verification: [0-9]+ proved, [0-9]+ failed, [0-9]+ unknown' "$1" \
    | awk '{p+=$3; f+=$5; u+=$7} END {printf "%d %d %d", p+0, f+0, u+0}')
  # runtime-checked is the AUTHORITATIVE per-function verdict-line field. Scope the
  # grep to the `Trust verification:` summary line ONLY. The verifier ALSO emits a
  # per-function `Level 0 summary: ... N runtime-checked` warning line restating the
  # same count, so an unscoped `grep '[0-9]+ runtime-checked'` DOUBLE-COUNTS every
  # runtime-checked obligation (verdict line + Level-0-summary line), roughly 2×
  # inflating `verified`. Match only the verdict line's trailing `N runtime-checked`.
  rc=$(grep -oE 'Trust verification: [0-9]+ proved, [0-9]+ failed, [0-9]+ unknown, [0-9]+ timed out, [0-9]+ runtime-checked' "$1" \
    | grep -oE '[0-9]+ runtime-checked' \
    | awk '{r+=$1} END {printf "%d", r+0}')
  echo "$pfu $rc"
}

run_soundness() {
  echo "== SOUNDNESS ratchet: verifying canaries =="
  local log="$SCRATCH/sentinel.log"
  local p f u rc total attempt counts gate_rc
  # WARM-UP RETRY: a cold solver/cache may occasionally under-emit structured
  # transport on the first run. Retry incomplete inventories up to 3x warm. A
  # genuinely-false row reported as Proved has a distinct exit code and blocks
  # immediately on the first observation; it is never retried away.
  for attempt in 1 2 3; do
    RUSTC_BOOTSTRAP=1 "$TRUSTC_BIN" --edition 2021 --crate-type lib \
      -Ztrust-verify-output=both "$SENTINEL" -o "$SCRATCH/sentinel.rlib" >"$log" 2>&1
    # The structured per-function gate is authoritative: every named canary
    # must emit its expected false VC family, and no row in that family may be
    # proved. Aggregate counts alone cannot detect a false proof hidden by an
    # unrelated obligation disappearing or becoming unknown.
    have python3 || fail "python3 required for the per-canary soundness gate ($SOUNDNESS_GATE)"
    [ -f "$SOUNDNESS_GATE" ] || fail "soundness-gate helper missing: $SOUNDNESS_GATE"
    if counts=$(python3 "$SOUNDNESS_GATE" --log "$log" --source "$SENTINEL"); then
      read -r p f u rc total <<<"$counts"
    else
      gate_rc=$?
      # Exit 2 is an observed false proof and blocks immediately. Missing or
      # incomplete transport may be the documented cold-cache under-emission,
      # so it receives the same bounded warm retry as the aggregate floor.
      [ "$gate_rc" -ne 2 ] || fail "individual soundness-canary FALSE-PROVE; see $log"
      if [ "$attempt" -lt 3 ]; then
        echo "  (attempt $attempt: individual canary transport incomplete — retrying warm)"
        continue
      fi
      fail "individual soundness-canary verification incomplete after 3 attempts; see $log"
    fi
    break
  done
  echo "  canary obligations: proved=$p failed=$f unknown=$u runtime-checked=$rc (total=$total)"
  # This is a defense-in-depth arithmetic consequence of the authoritative
  # per-function check: 15 distinct functions each supplied at least one exact,
  # non-Proved false row. Keep it explicit so future checker refactors cannot
  # accidentally weaken that invariant.
  [ $((f + u + rc)) -ge 15 ] || fail "individual gate returned fewer than 15 unproved false rows — checker invariant broken"
  echo "  ✓ soundness canaries hold (all 15 exact false VC rows are present and individually unproved)"
}

run_coverage() {
  echo "== COVERAGE ratchet: re-verifying clean-kernel (heavy) =="
  local ceiling; ceiling=$(grep -oE '"current_ceiling": [0-9]+' "$RATCHET" | grep -oE '[0-9]+')
  local log="$SCRATCH/kverify.log"
  RUSTC_BOOTSTRAP=1 RUSTFLAGS="-Ztrust-verify-target=clean_kernel -Ztrust-verify-output=human" \
    cargo build --locked --manifest-path "$REPO/Cargo.toml" -p clean-kernel --lib >"$log" 2>&1
  local cargo_rc=$?
  # A COMPLETE verification build exits 0 (Level-0 warning mode). A terminated
  # (SIGTERM=143, e.g. contention/OOM) or errored build did NOT cover every
  # function — its obligation counts are a TRUNCATION ARTIFACT, never a real
  # coverage gain. Refuse to report it (would otherwise false-ratchet down).
  [ "$cargo_rc" -eq 0 ] || fail "clean-kernel verification build did not COMPLETE (cargo exit $cargo_rc — terminated/errored, likely contention or a Lever bug). Measurement invalid; do not run concurrently with another clean-kernel verify. See $log"
  read -r p f u rc < <(sum_verdicts "$log")
  local unproved=$((f + u)); local verified=$((p + rc))
  local verified_floor; verified_floor=$(grep -oE '"verified_floor": [0-9]+' "$RATCHET" | head -1 | grep -oE '[0-9]+')
  echo "  clean-kernel (aggregate): proved=$p failed=$f unknown=$u runtime-checked=$rc  unproved=$unproved verified=$verified  (soft floor=$verified_floor, soft ceiling=$ceiling)"
  [ $((p + f + u)) -ge 1000 ] || fail "clean-kernel produced only $((p+f+u)) obligations (baseline total ~5810) — verification incomplete; see $log"

  # ── PER-FUNCTION COMMON-SET DIFF — the AUTHORITATIVE coverage gate ──────────
  # The old gate compared ABSOLUTE totals (unproved>ceiling, verified<floor) and
  # HARD-failed. Those totals are memory-guard-NONDETERMINISTIC: the ~33.6GB
  # VC-gen guard skips a varying swath of obligations run-to-run, and new kernel
  # code adds obligations — so a faithful re-measure on current main can trip a
  # SPURIOUS "COVERAGE REGRESSION" even when 0 functions actually regressed.
  # The honest test is per-function: did any function FULLY VERIFIED in the
  # baseline become GENUINELY unverified now (failed, or a non-work-budget
  # unknown)? 0 per-function regressions == no real coverage loss, regardless of
  # absolute-total drift. New functions are landscape; the aggregate is SOFT.
  have python3 || fail "python3 required for the per-function coverage diff ($COVERAGE_DIFF)"
  [ -f "$COVERAGE_DIFF" ] || fail "coverage-diff helper missing: $COVERAGE_DIFF"
  if [ "$UPDATE" = 1 ]; then
    python3 "$COVERAGE_DIFF" update --log "$log" --baseline "$FUNC_BASELINE" \
      || fail "failed to write per-function baseline $FUNC_BASELINE"
    # Keep the SOFT aggregate floor/ceiling in the ratchet JSON re-anchored to
    # this run's measured numbers (informational; ratchets ceiling DOWN / floor UP).
    # Record the ACTUAL measured aggregates as SOFT informational context. These
    # are no longer hard-gated, so they reflect this run's real numbers rather
    # than a monotonic best-ever (which would drift from reality given the
    # memory-guard nondeterminism). The authoritative gate is the per-function
    # baseline written above.
    python3 - "$RATCHET" "$p" "$f" "$u" "$rc" "$unproved" "$verified" <<'PY'
import json,sys
path,p,f,u,rc,unp,ver=sys.argv[1],*map(int,sys.argv[2:8])
d=json.load(open(path))
d["baseline"].update(proved=p,failed=f,unknown=u,runtime_checked=rc,unproved=unp,verified=ver)
# SOFT context: store the last measured aggregates (informational, not gated).
d["coverage_ratchet"]["current_ceiling"]=unp
d["coverage_ratchet"]["verified_floor"]=ver
json.dump(d,open(path,"w"),indent=2); open(path,"a").write("\n")
print(f"  recorded SOFT aggregates (informational): unproved={unp}, verified={ver}")
PY
    return 0
  fi
  [ -f "$FUNC_BASELINE" ] || fail "per-function baseline missing: $FUNC_BASELINE — run 'scripts/trust_verify_ratchet.sh --coverage --update' once to seed it"
  # HARD gate: any genuine per-function regression -> non-zero exit -> fail.
  python3 "$COVERAGE_DIFF" gate --log "$log" --baseline "$FUNC_BASELINE" \
    || fail "COVERAGE REGRESSION — one or more functions FULLY VERIFIED in the baseline are now GENUINELY unverified (a real coverage loss, not memory-guard drift). See the REGRESSION list above. The honest per-function common-set diff is authoritative; absolute totals are not gated."
  echo "  ✓ COVERAGE OK (0 genuine per-function regressions; aggregate floor/ceiling are soft/informational)"
}

run_benchmark() {
  echo "== GLOBAL benchmark: diverse correct-code patterns must verify clean =="
  local bench="$REPO/tests/trust_verify/global_benchmark.rs"
  [ -f "$bench" ] || fail "global benchmark missing: $bench"
  local log="$SCRATCH/benchmark.log"
  RUSTC_BOOTSTRAP=1 "$TRUSTC_BIN" --edition 2021 --crate-type lib \
    -Ztrust-verify-output=human "$bench" -o "$SCRATCH/bench.rlib" >"$log" 2>&1
  local rc=$?
  read -r p f u _rcheck < <(sum_verdicts "$log")
  echo "  benchmark obligations: proved=$p failed=$f unknown=$u"
  # The benchmark holds ONLY correct code (PROVE + FRONTIER). PROVE functions
  # must prove; FRONTIER may be Unknown (a warning) — neither is an error. A
  # `guaranteed Level 0 safety violation` here means the verifier FALSE-REFUTED
  # correct code: a GLOBAL regression (a whole class of programs broke), exactly
  # what Lever A did to byte-serialization. Blocks unconditionally.
  if [ "$rc" -ne 0 ] || grep -q "guaranteed Level 0 safety violation" "$log"; then
    echo "  FALSE-REFUTED correct functions:"
    grep -oE "guaranteed Level 0 safety violation\(s\) in \`[^\`]+\`" "$log" | sed 's/^/    /' | head
    fail "GLOBAL REGRESSION — verifier reported a guaranteed violation on CORRECT benchmark code (false refutation). Helping one program class while breaking another is NOT a global improvement; this is not mergeable."
  fi
  echo "  ✓ all diverse correct-code patterns verify clean (no false refutations)"
}

case "$MODE" in
  --soundness) run_soundness ;;
  --coverage)  run_coverage ;;
  --benchmark) run_benchmark ;;
  *)           run_soundness; run_benchmark; run_coverage ;;
esac
echo "RATCHET OK"
