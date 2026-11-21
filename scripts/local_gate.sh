#!/usr/bin/env bash
# Local fail-closed enforcement gate. GitHub CI was retired by owner decision.
#
# Run before pushing main:  scripts/local_gate.sh [--fast]
#
# Gates (each fail-closed):
#   1. Soundness certificate (C1-C5+C4') + golden TCB pin + false-axiom guards
#   1b. axiom_audit.json ↔ soundness_tcb.json (cert C2 golden) consistency —
#      fail-closed; binds the first-class domain-axiom metric to the live cert
#   2. CLI feature coverage (descriptor registry ↔ clap paths ↔ referenced files)
#   3. Ratchets: unchecked-decl + axiom audit surfaced from the cert golden pins;
#      extend_constants_* bulk-bypass ratchet (fail-closed); path-to-3 TCB ratchet
#      (domain-axiom count monotonic-down toward the 3-axiom goal, fail-closed);
#      prelude/.olean collision ratchet (prelude names that DISCARD Lean's
#      declaration at import, monotonic-down, fail-closed)
#   3a. add_decl_* bypass ratchet MEASURED from crates/**/*.rs (selftest first,
#      then the scan): the CLAUDE.md soundness rule that no gate had ever
#      re-derived — data/unchecked_decl_ratchet.json was only ever checked
#      against itself (scripts/check_add_decl_ratchet.py)
#   3b. Trust-core evidence staleness tripwire: recomputes the cmd_replacement
#      module-tree digest + cmd_replacement.rs sha and fails when the checked-in
#      launch-evidence artifacts pin different digests (prints
#      TRUSTCORE_STALENESS=fresh|stale)
#   3c. Crystal revalidation scope: binds the crystal chain revalidation records
#      to the clean-kernel SOURCE tree they were measured at, and fails when a
#      CHAINED body's own source file has moved past it (whole-crate
#      renumbering is ledgered, not failed)
#   3d. Crystal enum tag pin: the chained kernel enums' declaration order and
#      discriminants, re-derived from source and cross-checked against the
#      reflected tag defs and the recorded trust-ir artifacts. A reorder is
#      invisible to every other gate and silently makes a registered crystal
#      module a theorem about a body that is no longer shipped
#      (data/crystal_enum_tag_pin.json)
#   3d2. Source-elab ratchet ARTIFACT check (cheap): the pinned Mathlib-source
#      slice in scripts/source_elab_gate.sh vs data/source_elab_ratchet.json —
#      a pinned file with no ratchet entry enforces a baseline of 0, i.e. is
#      silently unenforced. The MEASUREMENT is hours long and runs as the
#      `gate::srcelab` suite row, never here.
#   3e. Green-artifact recheck: re-runs `clean check` on every corpus a
#      checked-in reports/*-green.json claims is green, and fails when the count
#      no longer matches the pin. The mtype green artifact sat RED for a week
#      because nothing re-ran it (full mode only; needs a prebuilt binary)
#   4. Paragon quality ratchet (shrink-only: file-size, unwrap/expect,
#      bare-pub, dead-code suppressions — data/paragon_ratchet.json)
#   4b. Lint coverage: no tracked crate outside [workspace] members, no gate
#      site that dropped --workspace/--all-targets, and the standalone crystal-A2
#      projector's tests and lint RUN (scripts/check_lint_coverage.py)
#   5. (full mode) workspace LINT (`cargo clippy --locked --workspace
#      --all-targets -- -D warnings`; the former bare `cargo check` obeyed
#      default-members and saw 8 of 27 crates) + NON-VACUOUS KernelVerified gate (re-stamps a
#      pinned OOM-safe slice → KV ratchet + elision subset, scripts/kv_ratchet_gate.sh)
#      + full clean-kernel --lib suite + trusted-kernel lint ratchet (dead_code/
#      unused debt hidden by source-level #[allow] attributes in clean-kernel;
#      the workspace [lints] set these to warn — audit r5/r6 M1)
#   6. (full mode, LAST) frontend merge suite: every lib, bin, integration and
#      doctest target of clean-parser/-olean/-macro/-elab, --no-fail-fast,
#      one verdict per target (scripts/frontend_merge_suite.sh)
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

FAST=0
[[ "${1:-}" == "--fast" ]] && FAST=1
fail() { echo "LOCAL GATE: FAIL — $1" >&2; exit 1; }

# Each heavy leg owns its memory reservation before acquiring CPU. Keep cold
# compile floors numeric: an auto class can learn only warm no-op rebuilds.
# These floors are reservations, not evidence that a whole phase fits them.
_gate_build() ( # <memory GiB> <CPUs> <label> <executable> [args...]
  local gb=${1:-} cpus=${2:-} label=${3:-} started rc=0
  if [[ ! "$gb" =~ ^[1-9][0-9]*$ || ! "$cpus" =~ ^[1-9][0-9]*$ || -z "$label" || $# -lt 4 ]]; then
    echo "local-gate admission: REFUSED: positive numeric budgets and a command are required" >&2
    return 75
  fi
  if [[ ${HEAVY_GATE_HELD+x} ]]; then
    echo "local-gate admission: REFUSED: run local_gate.sh directly, outside a memory reservation" >&2
    return 75
  fi
  # This compiler-capable composite may rebuild cold under the current toolchain.
  # Preserve higher requests; warm samples are not a lower cold-build bound.
  if [[ ${#gb} -lt 2 || ( ${#gb} -eq 2 && "$gb" < "47" ) ]]; then
    printf 'local-gate admission: RAISED %s from %s to 47 GiB (compiler floor)\n' "$label" "$gb" >&2
    gb=47
  fi
  shift 3
  started="$(mktemp "${TMPDIR:-/tmp}/local-gate-admitted.XXXXXX")" || return 75
  trap 'rm -f "$started"' EXIT
  trap 'exit 129' HUP
  trap 'exit 130' INT
  trap 'exit 143' TERM
  scripts/heavy_gate.sh run "$gb" "local-gate-$label" -- \
    build-slot --cpus "$cpus" --mem-gb "$gb" -- \
    sh -c 'printf admitted >"$0" || exit 74; exec "$@"' "$started" "$@" || rc=$?
  # Exit 2 is an intentional SKIPPED in two payloads. A controller's refusal
  # must never impersonate that payload outcome, including a vacuous exit 0.
  if [[ ! -s "$started" ]]; then
    echo "local-gate admission: REFUSED: payload did not start (admission exit $rc)" >&2
    return 75
  fi
  return "$rc"
)

# The frontend's run/doc phases keep their own auto history, including high
# partial peaks. Scope its minimum to this call; never change the machine policy.
_gate_frontend_auto_floor() {
  local floor=${HEAVY_GATE_AUTO_FLOOR_GB:-47}
  if [[ ! "$floor" =~ ^[0-9]+$ ]]; then
    echo "local-gate admission: REFUSED: frontend auto floor must be numeric" >&2
    return 75
  fi
  while [[ ${#floor} -gt 1 && "$floor" == 0* ]]; do floor=${floor#0}; done
  if [[ ${#floor} -lt 2 || ( ${#floor} -eq 2 && "$floor" < "47" ) ]]; then floor=47; fi
  printf '%s\n' "$floor"
}

# ── THE STANDALONE CRATE HAS NO LEG HERE ────────────────────────────────────
#
# scripts/crystal_a2_project is its own [workspace] (it depends on trust-ir,
# which nothing Clean ships does), so neither `cargo test --workspace` nor the
# workspace clippy compiles it. Until 2026-09-25 this file ran it as the
# `crystal-a2-project` leg, FIRST, before a demonstration stop, and
# scripts/check_lint_coverage.py decided whether that leg really gated -- by
# reading this file, then by running its first lines in a scratch repo. Both
# were evadable (verifier r8: a `fail` redefined only where `crates/` exists
# passed the demonstration and let this gate exit 0 past a failing projector
# test), and the pre-push hook never ran the leg at all. The crate's tests and
# its `-D warnings` lint (with its wildcard lints FORBIDDEN on the command line)
# now run INSIDE scripts/check_lint_coverage.py, on every invocation: the
# `lint-coverage` leg below, in both modes, and the hook's. Nothing here is a
# demonstration input any more.

# ── WAIVED LEGS ─────────────────────────────────────────────────────────────
#
# `fail` above exits on the spot, which is right for a leg that is meant to
# block and WRONG for a leg the reviewed policy already waived. Measured
# 2026-09-14: `no-ignored-tests` was RED at origin/main from another lane's
# landing, waived in scripts/githooks/gate-legs.txt until 2026-09-28 (the
# pre-push hook duly ran it, printed it and did not block) — and it is leg 8 of
# 56 here, so `scripts/local_gate.sh`, the command CLAUDE.md tells every lane to
# run before pushing, exited 1 with FORTY-EIGHT legs never reached. The
# soundness certificate, every ratchet and the workspace lint were among them.
# That is the same shape as the tomllib failure recorded under PYTHON
# RESOLUTION below, from a different cause: one early leg taking the whole gate
# with it. (Waiver CLOSED 2026-09-15: all 57 sites converted, leg is a plain `fail` again; see its IN_HOOK row.)
#
# So a waived leg reports through `fail_waivable <leg-id> <message>`, which
# reads the SAME reviewed table the hook reads — one source, not a second
# opinion — prints the failure in full, records it, and lets the gate continue.
# It is not a softening: an UNWAIVED leg still exits on the spot; an EXPIRED
# waiver still fails (here and in the hook); the waived failure is re-printed in
# the summary at the end; and `scripts/check_hook_coverage.py` refuses the push
# unless every WAIVED row in gate-legs.txt has a `fail_waivable` call site here
# carrying its id, so a waiver cannot be added to the table and quietly fail to
# apply, and a call site cannot outlive the waiver that justified it.
# The gate cd's to the repo root at startup (see below), so a repo-relative
# path is correct here and stays correct in a worktree.
GATE_LEGS_POLICY="scripts/githooks/gate-legs.txt"
WAIVED_FAILURES=()

# Echo "expires|owner" for a WAIVED row, else nothing. Same 6-column format the
# hook parses: <status> | <mode> | <leg-id> | <owner> | <expires> | <reason>.
waived_row() {
  [[ -f "$GATE_LEGS_POLICY" ]] || return 1
  awk -F'|' -v id="$1" '
    /^[[:space:]]*#/ { next }
    NF >= 6 {
      status = $1; leg = $3; owner = $4; expires = $5
      gsub(/^[ \t]+|[ \t]+$/, "", status)
      gsub(/^[ \t]+|[ \t]+$/, "", leg)
      gsub(/^[ \t]+|[ \t]+$/, "", owner)
      gsub(/^[ \t]+|[ \t]+$/, "", expires)
      if (status == "WAIVED" && leg == id) { print expires "|" owner; exit }
    }' "$GATE_LEGS_POLICY"
}

fail_waivable() {
  local leg="$1" msg="$2" row expires owner today
  row="$(waived_row "$leg")"
  if [[ -z "$row" ]]; then
    fail "$msg"
  fi
  expires="${row%%|*}"; owner="${row#*|}"
  today="$(date -u +%Y-%m-%d)"
  if [[ "$expires" < "$today" ]]; then
    fail "$msg [its waiver EXPIRED on $expires, owner $owner — fix the leg or re-own the row in scripts/githooks/gate-legs.txt]"
  fi
  echo "LOCAL GATE: WAIVED — $leg: $msg" >&2
  echo "  waived until $expires, owner $owner (scripts/githooks/gate-legs.txt). The leg RAN and printed above; it does not block." >&2
  WAIVED_FAILURES+=("$leg (until $expires, owner $owner)")
}

report_waived() {
  (( ${#WAIVED_FAILURES[@]} )) || return 0
  echo "" >&2
  echo "LOCAL GATE: ${#WAIVED_FAILURES[@]} leg(s) FAILED under a reviewed waiver and did not block:" >&2
  local w
  for w in "${WAIVED_FAILURES[@]}"; do echo "  ~ $w" >&2; done
  echo "  Each row in scripts/githooks/gate-legs.txt carries its owner, expiry and the measured reason." >&2
}

# ── PYTHON RESOLUTION (fail-closed) ─────────────────────────────────────────
#
# This gate's legs are `$GATE_PYTHON scripts/*.py`, and five of the scripts they
# reach need `tomllib` (Python >= 3.11). On this machine `/usr/bin/python3` is
# 3.9.6 and sits AHEAD of Homebrew's 3.14 on PATH, so the VERY FIRST leg died at
# import with ModuleNotFoundError and the whole gate exited 1 — before the
# soundness certificate, the ratchets, or the workspace lint ever ran. Measured
# 2026-08-20: the lint frontend had just been repaired (scripts/rust_frontend.sh)
# and still could not run from here, because nothing downstream of leg 1 ran.
#
# Resolved to an explicit interpreter rather than a PATH shim on purpose. A
# generated `python3` wrapper in a bin dir was measured to BLOCK for >60 s at 0%
# CPU on first exec (macOS evaluates a newly written executable; load average
# was 21), and a wrapper that silently fails to exec would turn every python leg
# into a no-op that PASSES — the exact failure this gate exists to prevent.
# Nested gate scripts keep the ambient `python3`: none of them reach a
# tomllib-dependent script (checked 2026-08-20).
_gate_python() {
  local cand
  for cand in "${CLEAN_GATE_PYTHON:-}" python3 python3.14 python3.13 python3.12 python3.11 \
              /opt/homebrew/bin/python3 /usr/local/bin/python3; do
    [[ -n "$cand" ]] || continue
    command -v "$cand" >/dev/null 2>&1 || continue
    if "$cand" -c 'import tomllib' >/dev/null 2>&1; then command -v "$cand"; return 0; fi
  done
  return 1
}
GATE_PYTHON="$(_gate_python)" \
  || fail "no python3 with 'tomllib' (needs >= 3.11, or 'tomli' installed); five of this gate's scripts parse TOML, so the gate cannot run. Set CLEAN_GATE_PYTHON=/path/to/python3."
[[ "$(command -v python3 2>/dev/null)" == "$GATE_PYTHON" ]] \
  || echo "== local gate: python — $GATE_PYTHON ($("$GATE_PYTHON" -V 2>&1)); PATH python3 is $(python3 -V 2>&1) =="

# Legs call bare `targo`, which refuses to run as the rustup symlink
# ~/.cargo/bin/targo that an ordinary shell's PATH names first. Put the pinned
# toolchain's own bin first (the resolution CLAUDE.md gives for hand-run
# targo); change nothing when it cannot be resolved. Same rule as
# scripts/githooks/pre-push, measured there 2026-09-29.
if trust_sysroot="$(rustc +trust --print sysroot 2>/dev/null)" \
   && [ -x "$trust_sysroot/bin/targo" ] && [ ! -L "$trust_sysroot/bin/targo" ]; then
  PATH="$trust_sysroot/bin:$PATH"
  export PATH
fi

# ── meta-gate: REMOVED BY OWNER DECISION (2026-08-24) ────────────────────────
# A fail-closed check lived here requiring an installed pre-push hook
# (`bash scripts/install-git-hooks.sh --check`). The owner does not want git
# hooks on this machine and asked for it to be dropped. Recorded rather than
# silently deleted so the next lane does not re-add it as an oversight.
#
# WHAT IS LOST, stated plainly: nothing now verifies that anything ever RUNS this
# gate. That was the check's real point, and the trap it named is real -- until
# 2026-08-23 `core.hooksPath` held fourteen `.sample` files and no hook while the
# tree carried both a `scripts/hooks/pre-push` and a `just install-hooks` recipe,
# so the gate was wired to nothing and a RED sat undetected for about a week
# (the mtype green artifact, 32/49 against a gate demanding 49/49).
#
# WHY IT IS STILL RIGHT TO DROP: enforcement-by-hook is a property of an
# OPERATOR'S CLONE, not of the tree, and a gate leg cannot make it true -- it can
# only refuse to run until someone changes their local setup. A leg that fails on
# every clone that has not opted in is one `--no-verify` away from disabling every
# OTHER leg in this file, which is strictly worse than not having it.
#
# Anyone who does want the hook can still install it:
#     bash scripts/install-git-hooks.sh
# and audit coverage with `--check` / `--status`. The script is untouched.

# The gate registry. NOT a leg about the tree -- a leg about the LEGS.
#
# Six times in one week an invariant was asserted here where nothing re-derived
# it (add_decl_*, crystal_fixture_freshness, gate::srcelab, four perturbation
# batteries, seal_driver's guard, premise_witness_gate). Each was fixed as an
# instance. This is the class: every enforcement artifact is either WIRED and
# FALSIFIABLE or it is a green stamp, and until 2026-08-24 nothing in either
# repo asked which. The checker re-derives `wired_by` from the runner roots
# rather than reading the registry back, refuses a gate-shaped file that has no
# row, and refuses a soundness row that has never been seen to fail.
#
# It runs its own 16 mutation arms FIRST, on every invocation, for the same
# reason the add_decl leg does: a demonstrator whose falsifiability is only
# checked when somebody remembers is the artifact this gate exists to stop
# shipping. ~0.15 s for the arms, ~0.05 s for the check.
# GATE-LEG: gate-registry
echo "== local gate: gate registry (selftest, then check) =="
"$GATE_PYTHON" scripts/check_gate_registry.py --selftest \
  || fail "gate-registry SELFTEST — the registry checker's own mutation arms no longer fire, so a green from it means nothing (scripts/check_gate_registry.py --selftest)"
"$GATE_PYTHON" scripts/check_gate_registry.py \
  || fail "gate registry — a gate-shaped file has no row in data/gate_registry.json, a gate lost its runner, or a soundness gate has never been demonstrated to fail (scripts/check_gate_registry.py)"

# The registry says what runs; this says whether what runs SELECTS anything.
# `cargo test --locked -p clean-kernel axiom_refutation_gate` exits 0 having
# matched zero tests ("0 passed; ...; 10412 filtered out") because that gate
# lives in clean-verify. A filter that matches nothing is a gate that cannot
# fail, and libtest reports it as ok. Static, no cargo: ~0.8 s including its own
# self-test arms, which run first for the same reason the two legs above do.
# GATE-LEG: cargo-test-selectors
echo "== local gate: cargo-test selectors (selftest, then check) =="
"$GATE_PYTHON" scripts/check_cargo_test_selectors.py --selftest \
  || fail "cargo-test-selectors SELFTEST — the checker's own arms no longer fire (scripts/check_cargo_test_selectors.py --selftest)"
"$GATE_PYTHON" scripts/check_cargo_test_selectors.py \
  || fail "cargo-test selectors — a gate on the enforcement surface runs a \`targo --unverified test\` filter that selects ZERO tests; libtest exits 0 on it, so that gate cannot fail (scripts/check_cargo_test_selectors.py --list)"

# The two legs above ask whether the GATES are honest. This one asks whether the
# PROSE is, and nothing did. On 2026-08-26 four CLAUDE.md claims were proved
# false by measurement in one day and two of them caused bricks to be opened
# against things already fixed -- the everyday battery had read 63/63 in the very
# artifact the sentence cited while the sentence said 51/63, and "simp has NO
# conditional-lemma discharger" was three weeks stale. Only the first of those
# is mechanically reachable, and this leg reaches it: a `<!-- claim: figure -->`
# marker re-derives the number from its artifact, and a paragraph that quotes an
# N/M figure beside an artifact it does not bind is refused, so the next claim of
# that shape cannot be written unbound. It also refuses a governed doc citing a
# repo path that is not in the tree -- which is how it found
# docs/AUDIT_LEAN4_REPLACEMENT_2026-07-23.md, "the authoritative commit-pinned
# source interpretation", cited five times across four docs and never existing
# under that name. Markdown and JSON plus the git INDEX (`rev-parse
# --show-toplevel` and `ls-files` on the root, one batched `ls-tree` per sibling,
# GIT_DIR/GIT_WORK_TREE/GIT_INDEX_FILE scrubbed) -- no cargo, no source; it needs
# a checkout, and a `git archive` snapshot is a D0 TREE refusal by design.
# Cost history, three measured points: 0.06 s with 19 arms (2026-08-26); 0.93 s
# with 35 arms (2026-09-14 -- coverage, 7 -> 16 governed docs); ~1.9 s selftest
# + ~2.1 s check with 52 arms (2026-09-15 -- the fixture became a git repository
# copied per arm, plus the index query; 55 arms after the same-day D5 LINK
# merge; read the live arm count off the DOC_CLAIMS_SELFTEST line), the arms
# running first for the reason the two legs above do.
# GATE-LEG: doc-claims
echo "== local gate: doc claims (selftest, then check) =="
"$GATE_PYTHON" scripts/check_doc_claims.py --selftest \
  || fail "doc-claims SELFTEST — the doc-claim checker's own mutation arms no longer fire, so a green from it means nothing (scripts/check_doc_claims.py --selftest)"
"$GATE_PYTHON" scripts/check_doc_claims.py \
  || fail "doc claims — a governed doc quotes a figure its artifact no longer carries, cites a path that is not in the tree, or states an N/M figure beside an artifact it binds neither way (scripts/check_doc_claims.py --list)"

# The suite runner's durable record. `data/suite_state/` is git-TRACKED and is
# also RUNNER OUTPUT that changes without a commit, so every `git checkout` over
# it is a silent data loss -- one routine crash-recovery checkout destroyed a
# complete 14.33-hour sweep, exit code 0, no warning. The records are now
# written THROUGH an append-only journal outside the working tree and the
# tracked directory is a projection of it. That fix has exactly one failure
# mode: somebody deletes the journal call and nothing notices until the next
# checkout. So the wiring is re-derived here rather than trusted.
#
# ~1.4 s for the 16 mutation arms, ~0.1 s for the check. The arms run FIRST, on
# every invocation, for the same reason the two legs around it do.
# GATE-LEG: suite-journal
echo "== local gate: suite-state journal (selftest, then check) =="
"$GATE_PYTHON" scripts/check_suite_journal.py --selftest \
  || fail "suite-journal SELFTEST — the journal checker's own mutation arms no longer fire, so a green from it means nothing (scripts/check_suite_journal.py --selftest)"
"$GATE_PYTHON" scripts/check_suite_journal.py \
  || fail "suite-state journal — the runner's write-through journal is unwired, torn, or the working tree holds records the journal says were lost; recover with \`scripts/verify_runner.sh journal --apply\` and commit them (scripts/check_suite_journal.py)"

# GATE-LEG: dep-boundary
echo "== local gate: cross-repo dependency boundary =="
"$GATE_PYTHON" scripts/check_workspace_dependency_boundary.py \
  || fail "Clean must consume shared verification vocabulary through trust-ir-contract, never the Trust workspace"

# Lint-coverage invariant (~0.1s, metadata only — safe in the --fast path). The
# lint gate below is only worth its runtime if it still SELECTS everything: a
# tracked crate outside [workspace] members is linted by no command at all, and
# a gate site that drops --workspace/--all-targets re-opens the blind spot where
# non-default members' test targets are never compiled.
# GATE-LEG: lint-coverage
echo "== local gate: lint coverage (every tracked crate, every target) =="
_gate_build 12 2 lint-coverage "$GATE_PYTHON" scripts/check_lint_coverage.py \
  || fail "lint coverage — a tracked crate escaped [workspace] members, a gate site dropped --workspace/--all-targets, or the standalone crystal-A2 projector's tests or lint failed (scripts/check_lint_coverage.py)"

# Test-target coverage. `clean-verify` sets `autotests = false` so its
# specification-building integration tests share ONE binary and one
# `Specification::new()` (12.59 measured hours of duplicate builds otherwise --
# see crates/clean-verify/tests/spec_suite.rs). The price is that a new
# `tests/*.rs` is compiled only when something declares it, and a test nobody
# builds is a test that cannot fail -- silently, with no error and no warning.
# GATE-LEG: test-target-coverage
echo "== local gate: test-target coverage (every tests/*.rs is actually built) =="
"$GATE_PYTHON" scripts/check_test_target_coverage.py \
  || fail "test-target coverage — a tests/*.rs in an autotests = false crate is neither a [[test]] target nor reached from one, so nothing compiles it (scripts/check_test_target_coverage.py)"

# Format, scoped to what THIS push adds (~1.0-1.8 s: 0.81 s of selftest arms
# plus 0.2-1.0 s of measurement). The workspace `fmt --all --check` below is
# 26.4 s warm on this machine and lives in the FULL gate; that cost is why no
# hook ran fmt at all, and why `gate::fmt` went red three times and was fixed by
# somebody other than its author every time. This leg checks only the .rs files
# the push touches, with rustfmt's `--skip-children` so a changed mod.rs cannot
# drag in -- or blame -- files the push never touched.
#
# It is NOT `fmt --all` on a diet. It filters to the files `cargo fmt --all`
# actually reaches, because 21 tracked .rs files in this tree are dirty and
# structurally invisible to it (13 outside crates/, 8 spliced with include!(),
# which rustfmt has never followed). Verified 2026-08-25: over all 6,940 tracked
# .rs files this leg is GREEN, exactly matching `fmt --all --check` on the same
# tree. `--report-blindspot` names the unreachable ones.
# GATE-LEG: fmt-changed
echo "== local gate: rustfmt on the files this change touches (selftest, then check) =="
"$GATE_PYTHON" scripts/check_fmt_changed.py --selftest \
  || fail "fmt-changed SELFTEST — the leg's own mutation arms no longer fire, so a green from it means nothing (scripts/check_fmt_changed.py --selftest)"
"$GATE_PYTHON" scripts/check_fmt_changed.py --worktree \
  || fail "rustfmt — a .rs file this change touches is not formatted; run 'just fmt' and commit the result (scripts/check_fmt_changed.py)"

# GATE-LEG: no-ignored-tests
echo "== local gate: first-party Rust contains no ignored tests or doctests =="
if ignore_hits="$(
  git grep --line-number --extended-regexp \
    '(^[[:space:]]*#[[:space:]]*!?[[:space:]]*\[[[:space:]]*(ignore([[:space:]]*=|[[:space:]]*\])|cfg_attr\([^]]*,[[:space:]]*ignore([[:space:]]*=|[[:space:]]*[,)])))|(^[[:space:]]*(///|//!|\*)[[:space:]]*```([^`,[:space:]]+,)?ignore([,[:space:]]|$))' \
    -- '*.rs' ':(exclude)vendor/**' ':(exclude)third_party/**' \
      ':(exclude)reference/**'
)"; then
  printf '%s\n' "$ignore_hits" >&2
  fail "ignored first-party tests/doctests are forbidden; make bounded tests active or move qualification/measurement code to an explicit Rust tool"
else
  ignore_scan_status=$?
  [[ $ignore_scan_status -eq 1 ]] \
    || fail "the first-party #[ignore] scanner failed with status $ignore_scan_status"
fi

# GATE-LEG: self-skipping-tests
echo "== local gate: tests that can skip their own assertions (selftest, then check) =="
# The sibling of the leg above, and the same rule one step further in: a test
# must PASS, FAIL or be DELETED -- and a test whose assertions sit behind
# `if let Ok(..)`, a silent `Err(_) => {}` arm or an early `return` reports
# `ok` whether or not it measured anything. CLAUDE.md records the census that
# found six of them (2026-09-15, the nullary `macro_rules` finding); this is
# the ratchet that stops the seventh. --selftest first, for the same reason
# fmt-changed runs its arms first: a green from a gate whose arms no longer
# fire means nothing.
"$GATE_PYTHON" scripts/check_self_skipping_tests.py --selftest \
  || fail "self-skipping-tests SELFTEST — the leg's own mutation arms no longer fire, so a green from it means nothing (scripts/check_self_skipping_tests.py --selftest)"
"$GATE_PYTHON" scripts/check_self_skipping_tests.py \
  || fail "self-skipping tests — a #[test] can skip its own assertions at run time (guarded assertions, a silent Err/_ arm, or an early return) and would report ok forever; make the skip path FAIL, or review the site into data/self_skipping_test_ratchet.json with a reason AND a // SELF-SKIP OK: comment at the construct"

# GATE-LEG: soundness-cert
echo "== local gate: soundness certificate =="
_gate_build 19 2 soundness-cert scripts/cargo_test_nonvacuous.sh soundness-cert -- \
  targo --unverified test -p clean-kernel --lib --locked --features math-overlays -q \
  -- test_soundness_certificate golden_matches_live_axioms tests_false_axiom_prevention soundness_nested_arg \
  || fail "soundness certificate / golden TCB / regression suites"

# GATE-LEG: axiom-audit-consistency
echo "== local gate: axiom-audit <-> cert consistency =="
_gate_build 19 2 axiom-audit-consistency scripts/cargo_test_nonvacuous.sh axiom-audit-consistency -- \
  targo --unverified test -p clean-kernel --test verify_axiom_audit_integration --locked -q \
  -- axiom_audit_tcb_mirror_matches_soundness_tcb_golden \
  || fail "axiom_audit.json drifted from data/soundness_tcb.json (cert C2 golden) — sync the soundness_tcb_mirror block"

# GATE-LEG: prelude-axiom-ratchet
echo "== local gate: default-prelude axiom census + ratchet =="
# The two artifacts above (soundness_tcb.json, axiom_audit.json) are both scoped
# to Environment::soundness_certificate_env() -- Environment::new() plus the
# NN/math overlays. NEITHER looks at Environment::with_prelude(), which is what
# a bare `clean check` loads and which holds 300 Axiom-kind constants, 293 of
# them non-foundational. This leg is that coverage. It reuses the SAME cargo
# build as the soundness-cert leg above (-p clean-kernel --lib
# --features math-overlays), so it costs the test time and no compile.
_gate_build 19 2 prelude-axiom-ratchet scripts/cargo_test_nonvacuous.sh prelude-axiom-ratchet -- \
  targo --unverified test -p clean-kernel --lib --locked --features math-overlays -q \
  -- prelude_axiom \
  || fail "default-prelude axiom ratchet — a non-foundational axiom was added to the environment \`clean check\` loads by default, a census count rose, FOUNDATIONAL_AXIOMS was widened, or a Theorem/Definition in that environment now reaches non-foundational debt; see data/prelude_axiom_ratchet.json"

# GATE-LEG: cli-feature-coverage
echo "== local gate: feature coverage =="
_gate_build 12 2 cli-feature-coverage scripts/cargo_test_nonvacuous.sh cli-feature-coverage -- \
  targo --unverified test --locked -p clean-cli --test feature_coverage -q \
  || fail "CLI feature coverage"

# GATE-LEG: cli-help-truth
echo "== local gate: help truth =="
_gate_build 12 2 cli-help-truth scripts/cargo_test_nonvacuous.sh cli-help-truth -- \
  targo --unverified test --locked -p clean-cli --test help_truth -q \
  || fail "CLI help truth — a command prints no description, restates its own name, or names a repo path that does not exist; see crates/clean-cli/tests/help_truth.rs"

# The reduction-bound theorem family (proofs/reduction_bound.lean): every
# declaration elaborates and is kernel-checked, the headline statements and the
# definitions they are written in match their pins, each device mode has its
# witness, and no theorem reaches an axiom outside the kernel's foundations.
# clean-elab is not a default member, so `test-fast` does not build this
# target, and its only other runner is the full-mode frontend merge suite at the
# end of this script (about an hour). The target was red on main at 6780040a17
# (docs/DECISIONS.md, the reduction-bound section), which is why it has a leg of
# its own in both modes. Measured 2026-11-19: 181.5 s for the debug test binary;
# the cold build of that binary took 5m42s and peaked at 33.0 GB.
# GATE-LEG: reduction-bound-theorem
echo "== local gate: reduction-bound theorem (statements, definitions, witnesses, axioms) =="
_gate_build 47 4 reduction-bound-theorem scripts/cargo_test_nonvacuous.sh reduction-bound-theorem -- \
  targo --unverified test --locked -p clean-elab --test reduction_bound_all_lengths -q \
  || fail "reduction-bound theorem — proofs/reduction_bound.lean no longer elaborates, a headline statement or a definition under it no longer matches its pin, a device mode lost its witness, or a theorem reaches a non-foundational axiom; the panic names which (crates/clean-elab/tests/reduction_bound_all_lengths.rs)"

# Every CLI help surface has been READ against its handler, and a surface that
# appears or changes afterwards is refused until it is read again (~0.3 s).
# GATE-LEG: help-surfaces
echo "== local gate: help surfaces (read-verified roster) =="
"$GATE_PYTHON" scripts/check_help_surfaces.py --selftest >/dev/null \
  || fail "help-surfaces SELFTEST — the checker's own mutation arms no longer fire, so a green from it means nothing"
"$GATE_PYTHON" scripts/check_help_surfaces.py \
  || fail "help surfaces — a CLI help surface is unread, changed since its read, or stale; \`python3 scripts/check_help_surfaces.py --dump\` prints the rows a fresh read mints (scripts/check_help_surfaces.py)"

# GATE-LEG: ratchet-surfaces
echo "== local gate: ratchet surfaces =="
"$GATE_PYTHON" - <<'EOF' || exit 1
import json, sys
r = json.load(open('data/unchecked_decl_ratchet.json'))
tcb = json.load(open('data/soundness_tcb.json'))
audit = json.load(open('data/axiom_audit.json'))
mirror = audit.get('soundness_tcb_mirror', {})
print(f"  unchecked-decl call sites: structural={r.get('structural_call_sites', r.get('add_decl_structural', 'n/a'))} "
      f"unchecked={r.get('unchecked_call_sites', r.get('add_decl_unchecked', 'n/a'))}")
print(f"  TCB axioms: {tcb.get('axiom_count', 'n/a')} "
      f"(foundational={tcb.get('foundational_count', 'n/a')}, "
      f"domain={tcb.get('admitted_domain_count', 0) + tcb.get('other_admitted_count', 0)})")
print(f"  axiom_audit.json mirror: domain_axiom_count={mirror.get('domain_axiom_count', 'MISSING')} "
      f"(asserted == cert by step 1b)")
EOF

# GATE-LEG: extend-constants-ratchet
echo "== local gate: extend_constants bypass ratchet =="
"$GATE_PYTHON" scripts/check_extend_constants_ratchet.py --selftest \
  || fail "extend_constants ratchet SELFTEST — the ratchet's own mutation arms no longer fire, so a green from it means nothing (scripts/check_extend_constants_ratchet.py --selftest)"
"$GATE_PYTHON" scripts/check_extend_constants_ratchet.py \
  || fail "extend_constants_* bypass ratchet — a new unaccounted bulk-import bypass; add a // SOUNDNESS: comment + a data/unchecked_decl_ratchet.json entry"

# add_decl_* bypass ratchet, MEASURED against the source tree.
#
# CLAUDE.md makes this a first-class soundness rule ("add_decl_structural /
# add_decl_unchecked require a // SOUNDNESS: comment ... Tracked in
# data/unchecked_decl_ratchet.json; only goes down"), and until 2026-08-22 NO
# gate read a line of Rust to enforce it. `validate_unchecked_decl_ratchet`
# (clean-cli gate_checks.rs) checks that JSON against itself; the
# `unchecked_decl_ratchet_zero` lane in scripts/deny_sorry_gate.sh asserted the
# two counts were the literal 0 and recorded that as a passing lane into
# reports/deny-sorry-launch-evidence.json. Neither re-derived anything, and the
# literal 0 was FALSE — SUPERSEDED 2026-08-23 (G6): that lane is now
# `unchecked_decl_ratchet_accounted` and calls this same scanner.
#
# FALSIFIED, not assumed: planting `env.add_decl_unchecked(d)` in production
# code in crates/clean-kernel/src/env/snapshot.rs — no SOUNDNESS comment, no
# ratchet entry — left every gate in the repo byte-identical (2026-08-22). This
# leg is RED on that mutation and green without it.
#
# The --selftest arm runs FIRST and on every run, deliberately: a ratchet whose
# own falsifiability is only checked when someone remembers is the artifact this
# whole gate exists to stop shipping. 16 mutation arms, ~0.2 s; the measurement
# itself is ~3.4 s over 6,815 .rs files.
#
# G6 (2026-08-23): arms 13-16 run against the REAL SANCTIONED_SITES allowlist.
# 13/14 keep the 2026-08-22 falsification as a STANDING arm — the real
# snapshot.rs at its real path, green unplanted and red planted — and 15/16 pin
# the half a JSON count cannot enforce: a ratchet row cannot legalise a site the
# code allowlist does not name, and a sanctioned site cannot gain a second call.
# GATE-LEG: add-decl-ratchet
echo "== local gate: add_decl_* bypass ratchet (selftest, then measure) =="
"$GATE_PYTHON" scripts/check_add_decl_ratchet.py --selftest \
  || fail "add_decl ratchet SELFTEST — the ratchet's own mutation arms no longer fire, so a green from it means nothing (scripts/check_add_decl_ratchet.py --selftest)"
"$GATE_PYTHON" scripts/check_add_decl_ratchet.py \
  || fail "add_decl_* bypass ratchet — a production call site registers a declaration WITHOUT type checking and is not accounted for in data/unchecked_decl_ratchet.json, or an accounted site lost its // SOUNDNESS: comment, or a recorded row no longer matches a live site"

# Widened environment-bypass census (program G-SCAN, 2026-08-23). The two
# ratchets above watch FOUR methods; the recon census
# (docs/analysis/spine-lattice-recon-2026-08-22.md §3) measured that the
# surface through which declarations/inductives/recursors/axioms/whole
# deserialized Environments become kernel-visible without full checking is far
# wider — every TrustedEnvExt method, the register_*/extend_*_unchecked
# inductive-metadata family, upgrade_axiom_stubs, add_skolem_axiom,
# add_constant_unchecked_for_test, set_constant_source, and the env
# deserialization entry points (Environment::from_json / load_from_file /
# load_snapshot). Until 2026-08-23 items 5-13 and 16-18 of that census had
# partial or ZERO scanner coverage. The scanner re-derives every row of
# data/env_bypass_census.json from crates/**/*.rs (both dot-call and
# Environment::/TrustedEnvExt::-qualified forms), fails closed on an
# unaccounted call, a stale site, an over-baseline count, or a NEW
# TrustedEnvExt method nobody watches, and cross-references (never re-counts)
# the add_decl_*/extend_constants_* rows ledgered in
# data/unchecked_decl_ratchet.json. Selftest first, same contract as the
# add_decl leg: 16 mutation arms, ~0.1 s; the measurement is ~2.3 s.
# GATE-LEG: env-bypass-census
echo "== local gate: environment-bypass census (selftest, then measure) =="
"$GATE_PYTHON" scripts/check_env_bypass_census.py --selftest \
  || fail "env-bypass census SELFTEST — the census scanner's own mutation arms no longer fire, so a green from it means nothing (scripts/check_env_bypass_census.py --selftest)"
"$GATE_PYTHON" scripts/check_env_bypass_census.py \
  || fail "environment-bypass census — a production call reaches a kernel-environment mutation/deserialization door (TrustedEnvExt method, register_*/extend_*_unchecked, upgrade_axiom_stubs, add_skolem_axiom, set_constant_source, Environment::from_json/load_from_file/load_snapshot, ...) at a site data/env_bypass_census.json does not account for, a census row went stale, or the TrustedEnvExt trait gained a method no scanner watches"

# One-trust status page (2026-09-14). docs/STATUS_ONE_TRUST.md is GENERATED from
# the spine scoreboard and the bypass censuses, and its --check was wired to
# NOTHING. Measured consequence: the committed page said the section 3.6
# assumption ledger "is not yet minted" -- a ledger that has existed and been
# gated since 2026-09-09 -- and understated bypass_doors.watched as 8 against a
# live 12. A published status page contradicting the artifacts it cites is the
# class this repo exists to refuse. --check masks the producers' timestamps, so
# it reddens when a NUMBER moves and not when a clock ticks (falsified both ways).
# GATE-LEG: one-trust-status-check
echo "== local gate: one-trust status page is a fresh render =="
"$GATE_PYTHON" scripts/one_trust_status.py --self-test \
  || fail "one-trust status SELFTEST -- the page generator's own arms no longer fire, so a green from --check means nothing (scripts/one_trust_status.py --self-test)"
"$GATE_PYTHON" scripts/one_trust_status.py --check \
  || fail "one-trust status page -- docs/STATUS_ONE_TRUST.md differs from a fresh render, so it is publishing numbers its own sources no longer carry; regenerate with scripts/one_trust_status.py and READ THE DIFF"

# Parity tiers (2026-09-14). data/parity_tiers.json is Ring R3's fidelity-tier
# statement, GENERATED from committed artifacts, and the wired spine-scoreboard
# leg below publishes 20 of its 65 rows straight out of it -- including
# monotone-ratcheted tier values. Its own --check was wired to NOTHING and the
# artifact had not been re-minted since 2026-08-25, so the scoreboard was
# ratcheting `mathlib-source-elab` at 326 while the armed source-elab ratchet read
# 353: two committed artifacts disagreeing about one measurement, with the check
# that notices run by nobody. Same class as spine-assumption-ledger-check and
# verdict-io-contracts-check. FRESHNESS lines are printed and do not fail (a
# measured tier goes stale whenever commits land; --strict-fresh is the mode that
# refuses that, and is deliberately not used here).
# GATE-LEG: parity-tiers-check
echo "== local gate: R3 parity tiers (selftest, then ratchet over the committed artifact) =="
"$GATE_PYTHON" scripts/parity_tiers.py --self-test \
  || fail "parity-tiers SELFTEST -- the tier generator's own mutation arms no longer fire, so a green from --check means nothing (scripts/parity_tiers.py --self-test)"
"$GATE_PYTHON" scripts/parity_tiers.py --check \
  || fail "parity tiers -- data/parity_tiers.json no longer re-derives from its committed sources, or a tier moved against its own ratchet direction; regenerate with scripts/parity_tiers.py and READ THE DIFF"

# Model islands (2026-09-12). Embed memo designs/2026-08-28-embedding-the-kernel-model.md,
# owner ruling 5 taken for IN-PLACE ISLANDS: the self-verification model is embedded
# as `clean { }` islands in crates/clean-kernel/src/model_islands.rs, generated from
# crates/clean-verify/spec/*.clean. Trust's compiler parses each island with the REAL
# Clean parser and registers every declaration through add_decl, so the CIC kernel
# type-checks the model during a Rust build and a rejected island fails that build.
# THREE things this leg refuses, each demonstrated: the generated module drifting from
# its units; a declaration the unit no longer registers; and -- the one that matters --
# a declaration that is PRELUDE-OWNED, where the island reports a kernel-checked green
# having checked the prelude's declaration instead of the model's. That last is not
# visible in the compiler's own note: the add_inductive idempotence guard silently
# accepts a subset-of-constructors re-declaration, measured live on `Eq`.
# --verify SKIPS (exit 0, printed) on a host with no Trust toolchain.
# GATE-LEG: model-islands
echo "== local gate: model islands (selftest, drift, then kernel-check under Trust) =="
"$GATE_PYTHON" scripts/model_islands.py --self-test \
  || fail "model-islands SELFTEST -- the renderer's own mutation arms no longer fire, so a green from --check/--verify means nothing (scripts/model_islands.py --self-test)"
"$GATE_PYTHON" scripts/model_islands.py --check \
  || fail "model-islands DRIFT -- crates/clean-kernel/src/model_islands.rs no longer re-renders from crates/clean-verify/spec/*.clean; re-mint data/model_unit_declarations.json (clean-verify's parser-derived test confirms it) and READ THE DIFF"
_gate_build 12 2 model-islands "$GATE_PYTHON" scripts/model_islands.py --verify \
  || fail "model-islands KERNEL-CHECK -- an embedded declaration failed to register, or is PRELUDE-OWNED so the island green is the prelude's and not the model's (scripts/model_islands.py --verify)"

# Ring R2 member-set derivation check (2026-09-14). data/verdict_set.json is the
# artifact every other lane-(b) claim is stated over: the in-crate reference
# closure from the declared roots, split into lane (a) pure / lane (b)
# IO-bearing / lane (c) claim-owning scripts, each member pinned by sha256 and
# lane (c) carrying a line ratchet. It was wired to NOTHING and had no registry
# row until today, and that is exactly how it rotted: its edge rule followed
# `crate::`/`super::`/`self::` references only, so a file declaring `mod foo;`
# and then writing `foo::Item` -- which Rust resolves against the items in
# scope -- kept the whole child module outside the closure. Measured 2026-09-14:
# 27 modules, 15,542 lines, 79 IO token sites reachable from closure members and
# counted by nothing, including all of clean-olean import::{load,parse,path,
# module_cache_direct} and clean-verify spec::core_spec. The consumer leg below
# could not have caught it: verdict_io_contracts re-derives over the members
# verdict_set.json NAMES, so a member set that is too small is a green there.
# --self-test runs 25 mutation arms first (both directions of the new edge
# rule among them), then --check re-derives and refuses a mismatch.
# GATE-LEG: verdict-set-check
echo "== local gate: Ring R2 member-set derivation (selftest, then check) =="
"$GATE_PYTHON" scripts/verdict_set.py --self-test \
  || fail "verdict-set SELFTEST -- the member-set derivation's own mutation arms no longer fire, so a green from --check means nothing (scripts/verdict_set.py --self-test)"
"$GATE_PYTHON" scripts/verdict_set.py --check \
  || fail "verdict-set -- data/verdict_set.json no longer re-derives (a root moved, a closure member drifted or vanished, or the lane-(c) line ratchet grew); re-mint with scripts/verdict_set.py, or scripts/verdict_set.py --rebase-up \"<why the surface must grow>\" if the growth is deliberate, and READ THE DIFF"

# IO-contract model derivation check (2026-09-12). data/verdict_io_contracts.json
# is Ring R2 lane (b)'s contract model: every IO-bearing site in the lane, grouped
# into contracts, each with a statement, a probe and a discharge. It is DERIVED
# from data/verdict_set.json plus the lane's own source, and --check re-derives
# and refuses a mismatch -- so a lane-(b) file whose bytes drift from the digest
# the partition measured can no longer sit unnoticed behind a green scoreboard.
# It was wired to NOTHING until today, and could not have been wired: build()
# stamped the mint day into all 44 ledger rows, so --check was red-by-
# construction -- the committed artifact differed from a fresh derivation in
# exactly 88 lines, every one of them a date, and rendering with the mint day
# pinned reproduced it byte-for-byte. Dates are sticky now (carried forward per
# row id, stamped only when a row is new or its content changed, the rule
# scripts/spine_assumption_ledger.py already used), falsified in both directions.
# Runs BEFORE the ledger leg below, which cross-references this artifact's rows.
# GATE-LEG: verdict-io-contracts-check
echo "== local gate: lane-(b) IO contract model derivation (selftest, then check) =="
"$GATE_PYTHON" scripts/verdict_io_contracts.py --self-test \
  || fail "verdict-io contracts SELFTEST -- the contract model's own mutation arms no longer fire, so a green from --check means nothing (scripts/verdict_io_contracts.py --self-test)"
"$GATE_PYTHON" scripts/verdict_io_contracts.py --check \
  || fail "verdict-io contracts -- data/verdict_io_contracts.json no longer re-derives (a lane-(b) member drifted from the digest data/verdict_set.json pins, an IO site appeared or vanished, or the artifact was hand-edited); re-mint with scripts/verdict_io_contracts.py and READ THE DIFF"

# Assumption-ledger derivation check (2026-09-09). data/spine_assumption_ledger.json
# is RE-DERIVED by scripts/spine_assumption_ledger.py from its SEEDED_ENTRIES plus
# committed artifacts; a row typed straight into the JSON is dropped by the
# generator's next bare run. Audit r16 M16-6 typed row A-CLZ-DEREF-ARC-DATA-OFFSET
# into it on 2026-09-02 and the committed file stood STALE for a week -- measured
# at 3e5cf0ed4 in a detached worktree -- while the scoreboard ratchet below read
# its `count` untroubled: a stale-but-well-formed ledger satisfies a direction
# ratchet. --self-test runs the generator's own mutation arms first (a planted
# derived row, an unknown class, a vanished cited file, a rotted anchor, each
# missing key, every count drift, a status outside the vocabulary, ...), then
# --check derives and refuses if the committed artifact differs. Sub-second.
# GATE-LEG: spine-assumption-ledger-check
echo "== local gate: spine assumption ledger derivation (selftest, then check) =="
"$GATE_PYTHON" scripts/spine_assumption_ledger.py --self-test \
  || fail "spine assumption ledger SELFTEST -- the generator's own mutation arms no longer fire, so a green from --check means nothing (scripts/spine_assumption_ledger.py --self-test)"
"$GATE_PYTHON" scripts/spine_assumption_ledger.py --check \
  || fail "spine assumption ledger -- data/spine_assumption_ledger.json no longer re-derives from SEEDED_ENTRIES + the committed artifacts (a row typed into the JSON, a seeded anchor that rotted, a source artifact that moved); regenerate with scripts/spine_assumption_ledger.py and READ THE DIFF -- a dropped row is a debt that vanished, not one that was paid"

# Vendored-dependency provenance (2026-09-14). data/vendor_manifest.json is the
# tamper-evidence manifest for the `cargo vendor` tree (paragon axis 1: "every
# third-party dependency vendored AND verified"). vendor/ is GITIGNORED and
# shipped as a release archive, but both of the manifest's claims can be checked
# from committed files alone: it pins `cargo_lock_sha256`, and no row may carry
# a `name` that cannot be a crate name (`toml-0.9.12+spec`, the signature of the
# greedy name/version split that once labelled 8 rows `sha256-registry` for a
# comparison that never ran). HARD since 2026-10-07: the waiver this leg carried
# is gone because the artifact can be minted again. `cargo vendor` still refuses
# this lock (indexmap/num-integer/num-traits/sha2 at the same version from
# crates-io AND the first-party ty.git), so the generator grew a third-party-only
# staging mode that unpacks every crates.io package of Cargo.lock exactly as
# cargo's registry vendoring does, after checking each .crate's sha256 against
# the lock: `gen_vendor_manifest.py --stage-third-party vendor`, then
# `gen_vendor_manifest.py vendor`. A Cargo.lock change reddens this leg until
# that pair is re-run; that is the binding working, not a defect.
# GATE-LEG: vendor-manifest-check
echo "== local gate: vendored-dependency provenance (selftest, then check) =="
"$GATE_PYTHON" scripts/gen_vendor_manifest.py --self-test \
  || fail "vendor-manifest SELFTEST -- the name/version split arms no longer fire (semver build metadata contains hyphens, so a greedy split mangles the name and silently skips the Cargo.lock cross-check), so a green from --check means nothing (scripts/gen_vendor_manifest.py --self-test)"
"$GATE_PYTHON" scripts/gen_vendor_manifest.py --check \
  || fail "vendored-dependency provenance -- data/vendor_manifest.json is stale against Cargo.lock, or a row claims a registry checksum it could not have compared; re-mint: python3 scripts/gen_vendor_manifest.py --stage-third-party vendor && python3 scripts/gen_vendor_manifest.py vendor"

# The vendored Carcara's ledger (2026-09-30). third-party/carcara is Clean's
# Alethe checker, and third-party/carcara/UPSTREAM.json gives every file its
# upstream digest and, for a file changed here, its local one -- the record that
# keeps the import checkable against upstream. Nothing recomputed it: a vendored
# edit could land with a stale digest or no row at all and nobody would be told.
# Reads the INDEX, so an unstaged edit in a shared tree reds nobody.
# GATE-LEG: vendored-carcara-ledger
echo "== local gate: vendored Carcara ledger (selftest, then check) =="
"$GATE_PYTHON" scripts/check_vendored_carcara_ledger.py --self-test \
  || fail "vendored-carcara-ledger SELFTEST -- the ledger arms no longer fire (a stale digest, a file with no row, a row with no file), so a green from --check means nothing (scripts/check_vendored_carcara_ledger.py --self-test)"
"$GATE_PYTHON" scripts/check_vendored_carcara_ledger.py --check \
  || fail "vendored-carcara-ledger -- third-party/carcara/UPSTREAM.json disagrees with the staged vendored files; after staging, refresh digests with scripts/check_vendored_carcara_ledger.py --write, and add a row by hand for a new file"

# The upstream-soundness intake ledger (2026-10-18). data/upstream_soundness_intake.json
# is the standing record of every summer/Oct-2026 upstream Lean 4 kernel soundness
# report with Clean's disposition, the path:line that proves it, and its
# fixture-in-ORDER, and the DECISIONS entry for an oracle-ACCEPTS row or a live hole. Reports now arrive weekly and upstream
# is deleting its own Acc.rec tests (#13851), so a report that is forgotten or a
# disposition that rots because its guard moved is how Clean would silently fall
# behind. The checker reads the cited files only as DATA (line-count), mints no
# verdict from source text. No cargo, no network.
# GATE-LEG: upstream-soundness-intake
echo "== local gate: upstream-soundness intake ledger (selftest, then check) =="
"$GATE_PYTHON" scripts/check_upstream_soundness_intake.py --self-test \
  || fail "upstream-soundness-intake SELFTEST -- the ledger arms no longer fire (an unresolved evidence path:line, a fixture missing from ORDER, an oracle-ACCEPTS or live-hole row with no DECISIONS entry, an undeclared disposition, a live hole below P0, an unmeasured not-affected row), so a green from --check means nothing (scripts/check_upstream_soundness_intake.py --self-test)"
"$GATE_PYTHON" scripts/check_upstream_soundness_intake.py --check \
  || fail "upstream-soundness-intake -- data/upstream_soundness_intake.json has a row whose evidence path:line does not resolve, a non-null fixture missing from the replay_forged ORDER, an oracle-ACCEPTS or live-hole row whose decision names no docs/DECISIONS.md heading, an undeclared disposition, a live hole below P0, or a not-affected row that was never measured (scripts/check_upstream_soundness_intake.py --check)"

# Static source inventory freshness (2026-09-14). docs/SOURCE_INVENTORY.md is a
# generated documentation diagnostic (Rust LOC and source `#[test]` attribute
# counts, whole-tree and per-crate), linked from docs/README.md and named as a
# diagnostic by docs/RELEASE_READINESS.md. Its generator was registered by
# nothing and run by nothing, and the committed page was FORTY-SIX DAYS STALE:
# last written 2026-07-30, and re-deriving it moved the headline by 362,841
# Rust lines (3,143,314 -> 3,506,155) and 3,400 `#[test]` attributes
# (49,827 -> 53,227). It is a diagnostic, never verification evidence -- which
# is exactly why nobody noticed, and exactly why the number should not be
# published if nothing keeps it true.
# GATE-LEG: source-inventory-check
echo "== local gate: static source inventory freshness (selftest, then check) =="
"$GATE_PYTHON" scripts/sync_readme_metrics.py --self-test \
  || fail "source-inventory SELFTEST -- the two-way arms no longer fire (an unstaged edit must not move the published number; the same edit staged must), so a green from --check means nothing (scripts/sync_readme_metrics.py --self-test)"
"$GATE_PYTHON" scripts/sync_readme_metrics.py --check \
  || fail "source-inventory -- docs/SOURCE_INVENTORY.md no longer matches the tree it counts; regenerate with scripts/sync_readme_metrics.py (it is a source-shape diagnostic, not verification evidence, but a published number that nothing keeps true is worse than no number)"

# Frontend corpus classification freshness (2026-09-14).
# tests/lean4_compat/frontend_corpus_classification.json is the corpus-level
# frontend evidence artifact the `clean replacement` surface validates, derived
# from tests/lean4_compat/phase1_expected_outcomes.json and the pinned corpus
# checksums. Its --check was guarded ONLY by a cargo integration test
# (crates/clean-elab/tests/integration/lean4_phase1_compat.rs), which the gate
# excludes on cost and whose suite row reads UNKNOWN — and the artifact was
# measurably STALE for twenty days: 02669378a (2026-08-25) improved the dotted-
# name failure path so 1673.lean reports the self-reference recursion refusal
# instead of a generic UnknownFVar type mismatch, the profile recorded it, and
# the derived classification still carried the old category and signature.
# Nothing was wrong with the improvement; nothing re-derived the artifact.
# GATE-LEG: frontend-classification-check
echo "== local gate: frontend corpus classification (selftest, then check) =="
"$GATE_PYTHON" scripts/lean4_compat/generate_frontend_classification.py --self-test \
  || fail "frontend-classification SELFTEST -- the placeholder-rejection arms no longer fire. They are the property TWO Rust tests were written for and never once executed (they skip whenever the real artifact is present, and it has been tracked since the commit that added them), so a green from --check means nothing about it (scripts/lean4_compat/generate_frontend_classification.py --self-test)"
"$GATE_PYTHON" scripts/lean4_compat/generate_frontend_classification.py --check \
  || fail "frontend-classification -- tests/lean4_compat/frontend_corpus_classification.json no longer matches what its generator derives from the phase1 profile and the pinned corpus; regenerate with scripts/lean4_compat/generate_frontend_classification.py and READ THE DIFF (a moved diagnostic CATEGORY is a frontend behaviour change, not a refresh)"

# EvalIR producer freshness (2026-09-14). data/evalir_coverage.json and
# data/evalir_adequacy_grid.json are two of the thirteen PRODUCERS the G-SCORE
# ratchet below reads, and neither was wired to anything: both are derived from
# clean-verify's own `eval_ir_*.rs` sources, and a producer that stops matching
# its sources turns the ratchet beneath it into a comparison between two
# snapshots of the same stale number. Measured 2026-09-14: the adequacy grid was
# STALE at HEAD -- `eval_ir_syntax.rs` had moved and the grid still recorded the
# old digest -- red on its own --check, seen by no gate. The classification was
# unaffected (97 rows, same split), which is the point: nothing here says the
# staleness was harmless, only that nobody would have known either way.
# GATE-LEG: evalir-coverage-check
echo "== local gate: EvalIR coverage derivation (selftest, then check) =="
"$GATE_PYTHON" scripts/evalir_coverage.py --self-test \
  || fail "evalir-coverage SELFTEST -- the coverage derivation's own arms no longer fire, so a green from --check means nothing (scripts/evalir_coverage.py --self-test)"
"$GATE_PYTHON" scripts/evalir_coverage.py --check \
  || fail "evalir-coverage -- data/evalir_coverage.json no longer matches its clean-verify sources; regenerate with scripts/evalir_coverage.py and READ THE DIFF (the G-SCORE ratchet reads this artifact)"

# GATE-LEG: evalir-adequacy-grid-check
echo "== local gate: EvalIR adequacy grid derivation (selftest, then check) =="
"$GATE_PYTHON" scripts/evalir_adequacy_grid.py --self-test \
  || fail "evalir-adequacy-grid SELFTEST -- the grid's own arms no longer fire, so a green from --check means nothing (scripts/evalir_adequacy_grid.py --self-test)"
"$GATE_PYTHON" scripts/evalir_adequacy_grid.py --check \
  || fail "evalir-adequacy-grid -- data/evalir_adequacy_grid.json no longer matches the IRInst telescopes in eval_ir_syntax.rs and the ir_exec dispatch in eval_ir_machine.rs; regenerate with scripts/evalir_adequacy_grid.py and READ THE DIFF (a field whose read/drop verdict moved is a semantic change, not a refresh)"

# The fixed Environment DAG wire schema (2026-11-11). generate.py materializes
# crates/clean-kernel/src/env/dag_serialization/* from
# data/environment_dag_wire/schema_v2.json, and --check refuses a committed
# file whose tokens differ from a fresh generation (Trustfmt layout is not a
# token). It landed in 04f9856f3 with a --check that no runner invoked, so a
# hand edit of a generated decoder, or a schema edit without regeneration, was
# seen only by the full-mode self-test suite. Its registry row asked to become a
# gate once a runner adopted --check; this leg is that runner. 0.07 s measured.
# GATE-LEG: environment-dag-wire-check
echo "== local gate: Environment DAG wire schema (check) =="
"$GATE_PYTHON" scripts/environment_dag_wire/generate.py --check \
  || fail "environment-dag-wire -- a generated file under crates/clean-kernel/src/env/dag_serialization/ no longer matches data/environment_dag_wire/schema_v2.json; regenerate with scripts/environment_dag_wire/generate.py and READ THE DIFF (it is the kernel's persisted wire format)"

# Q3 runner fail-closed stub tests; no external checker required or executed.
# A leg of its own since 2026-11-13: it landed in f45134c2d inside the
# environment-dag-wire-check leg, which moved the FAST region without a row in
# scripts/githooks/gate-legs.txt. 3.2 s wall measured (1.3 s user, loaded box).
# GATE-LEG: nanoda-runner-selftest
echo "== local gate: nanoda runner self-test (stub binary; no external checker) =="
"$GATE_PYTHON" scripts/nanoda_recheck.py --selftest \
  || fail "nanoda runner selftest -- a pinned identity, reason or subject refusal failed"

# The CIC_L rule inventory (2026-11-12, self-proof plan unit S7). Pinned Lean
# 4 kernel sources are vendored under tests/fixtures/lean_kernel/; the script
# parses them and theories/cic_l (comments and literals blanked) and refuses
# when a kernel function, case arm or hardcoded constant has no row in
# data/cic_l_rule_inventory.json, when a row names a CIC_L item or an upstream
# anchor that is not there, or when the families not yet specified are not
# exactly data/cic_l_rule_ratchet.json. Its last line says how many rule
# families the specification does not cover; that line, not prose, is the
# figure. Self-test first, then the check: 0.23 s measured.
# GATE-LEG: cic-l-rule-inventory
echo "== local gate: CIC_L rule inventory against pinned Lean kernel sources (selftest, then check) =="
"$GATE_PYTHON" scripts/check_cic_l_rule_inventory.py \
  || fail "cic-l-rule-inventory -- a rule of pinned Lean's kernel is unmapped, a row of data/cic_l_rule_inventory.json names something that is not there, or the unspecified set moved against data/cic_l_rule_ratchet.json; read the (a)/(b)/(c) lines above. A specification change that closes a family edits its row and runs --update; nothing else lowers the ratchet"

# G-SCORE scoreboard ratchet (2026-08-23). data/spine_scoreboard.json is the
# one artifact that states spine/lattice progress (program doc
# designs/2026-08-22-spine-and-lattice-program.md §6; quoting a row of it from
# prose is a bug). --ratchet regenerates all 27 rows from the committed
# producer artifacts and enforces each row's direction against the committed
# baseline: up may not decrease, down may not increase, frozen may not move
# without a dated re-measured re-base, census.axiom_count must equal 11, and a
# baseline row may never silently vanish. UNKNOWN is first-class — it reports
# and never satisfies or violates. Wiring was deferred from the minting commit
# (3fafef4bb) on purpose: a gate must not be born enforcing a baseline the
# same change invented. --ratchet is READ-ONLY by its own self-tested contract
# (caf6dad89 follow-up): green touches nothing, a violation exits 1 naming the
# row and leaves the baseline alone, and a missing/unreadable baseline fails
# closed (mint with --refresh) — so the save/restore wrapper this leg once
# carried is gone; the tree stays clean without it.
# GATE-LEG: spine-scoreboard-ratchet
echo "== local gate: spine/lattice scoreboard ratchet (G-SCORE) =="
"$GATE_PYTHON" scripts/spine_scoreboard.py --ratchet \
  || fail "spine/lattice scoreboard ratchet — a scoreboard row moved against its committed direction (monotone-up decreased, monotone-down increased, frozen changed without a dated re-base, census != 11, or a baseline row vanished), or the committed baseline data/spine_scoreboard.json is missing/unreadable (--ratchet is read-only and cannot mint it; use --refresh); the violation names the row (scripts/spine_scoreboard.py --ratchet)"

# GATE-LEG: trust-verdict-emitters
echo "== local gate: trust-verdict emitter discipline (Pillar 1) =="
"$GATE_PYTHON" scripts/check_trust_verdict_emitters.py \
  || fail "trust-verdict emitter discipline — a new unclassified KernelVerified green in clean-kernel, a mislabeled kernel-rechecked entry, an un-justified asserts-own-authority emitter, or a raised own-authority ratchet; classify it in data/trust_verdict_emitters.json (Pillar-1 gate)"

# GATE-LEG: tcb-target-ratchet
echo "== local gate: path-to-3 TCB ratchet =="
"$GATE_PYTHON" scripts/tcb_target_ratchet.py \
  || fail "path-to-3 TCB ratchet — a domain axiom was added (moving away from the 3-axiom goal) or the foundational set drifted; see data/tcb_target_ratchet.json"

# GATE-LEG: prelude-collision-ratchet
echo "== local gate: prelude/.olean collision ratchet =="
"$GATE_PYTHON" scripts/check_prelude_collision_ratchet.py \
  || fail "prelude/.olean collision ratchet — a prelude name now shadows (and discards) a differently-typed Lean declaration at import, so tactics see a statement the user never wrote; see data/prelude_collision_census.json"

# GATE-LEG: prelude-instance-priority-ratchet
echo "== local gate: prelude instance-priority ratchet =="
"$GATE_PYTHON" scripts/check_prelude_instance_priority_ratchet.py \
  || fail "prelude instance-priority ratchet — a hand-registered instance carries a priority the shipped .olean contradicts (or the measured denominator shrank), so synthInstance reaches a different candidate first and elaborated terms change shape; see data/prelude_instance_priority_census.json"

# GATE-LEG: source-elab-ratchet-artifact
echo "== local gate: source-elab ratchet artifact =="
# ARTIFACT ONLY (~50 ms). The SRCELAB measurement itself re-elaborates four
# Mathlib source files through Clean's own frontend and takes HOURS
# (measured 2026-08-23 at a86c5ffd6, --jobs 4: 25,217 s of CPU, 3 h 35 min of
# wall), so it lives in the persistent suite runner as the `gate::srcelab` row,
# not here. What
# belongs here is the cheap half nothing else covered: the ratchet's
# enforcement reads `baselines.get(key, {}).get("success_baseline", 0)`, so a
# pinned file with no ratchet entry is measured against a baseline of ZERO and
# the gate still reports PASS. This leg fails closed on that, on an armed entry
# whose baseline is 0, on a cap that no longer matches the pinned slice, and on
# an armed ratchet with no `armed_commit` provenance.
scripts/source_elab_gate.sh --check-artifact \
  || fail "source-elab ratchet artifact — data/source_elab_ratchet.json disagrees with the pinned slice in scripts/source_elab_gate.sh (a pinned file with no entry silently enforces a baseline of 0); re-arm with scripts/source_elab_gate.sh --update"

# GATE-LEG: lean-suite-conformance-ledger
echo "== local gate: Lean test-suite conformance ledger =="
# ARTIFACT ONLY (~1 s with the self-test). The ledger records, per import-free
# file of Lean's own tests/elab and tests/elab_fail, the pinned Lean's verdict,
# Clean's verdict and the outcome; this leg refuses a ledger whose outcomes do
# not follow from its verdicts or whose totals do not add up, i.e. a hand-edited
# one. The MEASUREMENT against it is the full-only `lean-suite-conformance` leg.
{ "$GATE_PYTHON" scripts/lean_suite_conformance.py --selftest >/dev/null \
    && "$GATE_PYTHON" scripts/lean_suite_conformance.py --check-artifact; } \
  || fail "Lean test-suite conformance ledger — data/lean_suite_conformance.json is inconsistent (an outcome that does not follow from its two verdicts, totals that do not add up, a missing checkout rev) or the script's self-test is red; re-mint it with scripts/lean_suite_conformance.py --update, never by hand"

# GATE-LEG: silent-tactic-ratchet
echo "== local gate: silent-tactic ratchet =="
"$GATE_PYTHON" scripts/check_silent_tactic_ratchet.py \
  || fail "silent-tactic ratchet — a tactic now fails with NO diagnostic naming it, so the declaration degrades to an unattributable synthetic sorry and every UnknownTactic-keyed coverage script under-reports the gap; see data/silent_tactic_census.json"

# GATE-LEG: g-auto-static
# GATE-LEG: g-simp-static
echo "== local gate: tactic family gates (G-AUTO, G-SIMP) =="
# Executable family gates (docs/plans/TACTICS_TO_100_2026-07-29.md §7; teeth
# record: scripts/tactic_parity/TEETH.md). Fixture/manifest integrity (probe
# denominators pinned at 131/127, import-Init headers, no unlisted fixtures)
# is enforced fail-closed on EVERY run — it needs no binary. The MEASURED
# gates drive the prebuilt release binary over real `import Init` fixtures
# and therefore run in full mode only;
# they NEVER invoke cargo. Exit 2 = "no prebuilt binary": non-fatal by
# design, with the SKIPPED verdict line printed by the gate itself.
# Fail-closed (any other nonzero exit is a hard failure) when the binary
# exists.
#
# COST — CORRECTED 2026-08-27. This comment used to say "~2 min per fixture
# file, 13 files", which is not a measurement and is wrong by about an order of
# magnitude. The commit that FELLED the import-era OOM wall and made these
# fixtures completable at all (d41dfd545, 2026-08-14) records its own number:
# g_auto/logic.lean "completes at 2.2 GB peak in 812 s". family_gate.py's
# PER_FILE_TIMEOUT_SECS is 1800 and a timeout is an infrastructure FAILURE, not
# a skip — so on the box where the baselines were armed the budget was already
# only ~2.2x the slowest known file. Measured on aarch64-unknown-linux-gnu
# 2026-08-27 at 642462e95 with target/release/clean: g_auto/decide.lean and
# g_auto/norm_num.lean each hit the 1800 s timeout (decide.lean peaked at
# ~26.7 GB RSS), so this leg is a MULTI-HOUR, fail-closed blocker here, not a
# ~26 min one. Budget for it before running full mode. Whether that is a
# perf/memory REGRESSION since the 2026-08-15 baseline mint (b091ab074) or just
# a slower host than the one it was armed on is NOT settled: the discriminating
# experiment is to re-run g_auto/logic.lean here and compare against the 812 s /
# 2.2 GB that d41dfd545 measured for it.
"$GATE_PYTHON" scripts/tactic_parity/family_gate.py --family g_auto --static \
  || fail "G-AUTO fixture/manifest integrity (tests/fixtures/tactic_families/g_auto)"
"$GATE_PYTHON" scripts/tactic_parity/family_gate.py --family g_simp --static \
  || fail "G-SIMP fixture/manifest integrity (tests/fixtures/tactic_families/g_simp)"
if [[ $FAST -eq 1 ]]; then
  echo "  LEAN_AXIOM_CENSUS=SKIPPED reason=fast-mode (unmeasured; run scripts/check_lean_axiom_census.py)"
  echo "  SCRIPT_SELFTESTS=SKIPPED reason=fast-mode (~15 min; runs in full mode, or directly: scripts/check_script_selftests.sh)"
  echo "  G-AUTO=SKIPPED reason=fast-mode (measured gate runs in full mode, or directly: scripts/tactic_parity/g_auto.sh)"
  echo "  G-SIMP=SKIPPED reason=fast-mode (measured gate runs in full mode, or directly: scripts/tactic_parity/g_simp.sh)"
else
  # GATE-FULL-ONLY BEGIN
  # GATE-LEG: lean-axiom-census
  # E7 builds the pinned packages and compares every origin-module closure.
  # Exit 3 means not knowable here, never a green census.
  if scripts/heavy_gate.sh run auto:e7-census:2 e7-census -- build-slot -- "$GATE_PYTHON" scripts/check_lean_axiom_census.py; then
    :
  else
    e7_rc=$?
    if [[ $e7_rc -eq 3 ]]; then
      echo "  LEAN_AXIOM_CENSUS=UNKNOWN reason=not-knowable-here"
      exit 3
    fi
    fail "lean-axiom-census -- pinned package build, Ax0 policy, closure ratchet or fresh census comparison failed"
  fi
  # GATE-LEG: nat-operand-shape
  # Pins WHICH Nat op Lean's kernel grinds on and at WHICH operand position.
  # `native_nat_binop_grind_stuck` (clean-kernel/src/tc/reduction/nat.rs) carries
  # a soundness rationale that used to claim the guard "matches Lean, whose
  # `@[extern]` Nat.add/Nat.sub stay stuck on a symbolic operand". Measured
  # 2026-08-31: true for add/mul/pow, FALSE for sub, which recurses on its SECOND
  # argument and walks a large literal there. Nothing checked that claim, and not
  # knowing cost three attempted fixes, each found by a full spec build or a 24 MB
  # export cycle. This leg costs ~20 s.
  #
  # FULL-only and not in the hook: it needs the pinned `lean` toolchain, which no
  # other hook leg requires, and one probe deliberately takes 16.5 s because it
  # genuinely walks 512 steps.
  #
  # Exit 2 is SKIPPED, not failure — the runner refuses when it cannot identify a
  # lean rather than reporting a table produced by a compiler that never ran.
  if _gate_build 12 2 nat-operand-shape "$GATE_PYTHON" tests/nat-operand-shape-probe/run.py; then
    :
  else
    nat_probe_rc=$?
    if [[ $nat_probe_rc -eq 2 ]]; then
      echo "  NAT-OPERAND-SHAPE=SKIPPED reason=no-usable-lean (pinned toolchain absent; run directly: python3 tests/nat-operand-shape-probe/run.py)"
    else
      fail "nat operand-shape probe — Lean's reduction behaviour moved away from a pinned probe-expect, so a claim about which Nat op grinds on which operand is now stale (python3 tests/nat-operand-shape-probe/run.py; exit ${nat_probe_rc})"
    fi
  fi

  # GATE-LEG: tactic-lean-verdicts
  # Re-mints each family's sealed LEAN_VERDICTS.json into memory with the
  # pinned oracle-world lean (by absolute path, one process at a time, 120 s /
  # 2 GiB caps) and compares verdicts, classes, unknown tactics and axioms with
  # the committed sidecar the --static legs above trust (item 17, 2026-10-27).
  # ~2 min.
  # FULL-only for the nat-operand-shape reason: it needs the pinned Lean
  # toolchain. SKIPPED needs exit 2 AND the minter's own
  # `MINT_LEAN_VERDICTS=skipped:no-usable-lean` line (missing Lean, the aterm
  # reroute to Clean, another build, a cap): Python also exits 2 when it cannot
  # open the script and argparse on a usage error, and a renamed minter or a
  # changed flag must not disarm the one leg that asks pinned Lean. Anything
  # else nonzero is a hard failure (pinned by scripts/test_mint_lean_verdicts.py).
  for fam_mint in g_auto g_simp; do
    if mint_out=$(_gate_build 12 2 tactic-lean-verdicts "$GATE_PYTHON" scripts/tactic_parity/mint_lean_verdicts.py --check --family "$fam_mint" 2>&1); then
      printf '%s\n' "$mint_out"
    else
      mint_rc=$?
      printf '%s\n' "$mint_out"
      if [[ $mint_rc -eq 2 ]] && grep -q '^MINT_LEAN_VERDICTS=skipped:no-usable-lean ' <<<"$mint_out"; then
        echo "  TACTIC-LEAN-VERDICTS=SKIPPED family=${fam_mint} reason=no-usable-lean (run directly: python3 scripts/tactic_parity/mint_lean_verdicts.py --check --family ${fam_mint})"
      else
        fail "tactic family Lean verdicts ${fam_mint} — pinned Lean no longer gives the verdicts committed in tests/fixtures/tactic_families/${fam_mint}/LEAN_VERDICTS.json, or the mint refused or did not run as a minter (exit ${mint_rc}); re-mint with python3 scripts/tactic_parity/mint_lean_verdicts.py --family ${fam_mint}, never by hand"
      fi
    fi
  done

  for fam_gate in g_auto g_simp; do
    # g_auto reached 26.7 GiB before interruption; never learn a lower warm floor.
    fam_gb=12
    [[ "$fam_gate" == g_auto ]] && fam_gb=35
    if _gate_build "$fam_gb" 2 "tactic-$fam_gate" scripts/tactic_parity/${fam_gate}.sh; then
      :
    else
      fam_rc=$?
      if [[ $fam_rc -eq 2 ]]; then
        : # SKIPPED verdict line already printed by the gate (no prebuilt binary)
      else
        fail "tactic family gate ${fam_gate} — fail-closed measurement failure (scripts/tactic_parity/${fam_gate}.sh exit ${fam_rc}; see reports/tactic-families/${fam_gate}-latest.json and scripts/tactic_parity/TEETH.md)"
      fi
    fi
  done
  # GATE-FULL-ONLY END
fi

# Green-artifact recheck. Every `reports/*-green.json` asserts that a `.lean`
# corpus checked clean — and NOTHING re-ran those claims. On 2026-08-19
# `scripts/mtype_green.sh` was found RED (MType.lean 32/49 against a gate
# demanding 49/49) with the source unchanged since 216ac5209: the regression was
# in the ELABORATOR, and it sat undetected for a week because no gate re-ran the
# claim. The full green scripts are too slow for this path (mtype's cert export
# alone is ~145 s), but the part that ROTTED is `clean check`, which is
# sub-second per file. Fail-closed; SKIPPED only when there is no prebuilt
# binary, which the gate never builds.
if [[ $FAST -eq 1 ]]; then
  echo "  GREEN_RECHECK=SKIPPED reason=fast-mode (runs in full mode, or directly: scripts/green_artifact_recheck.sh)"
elif [[ -x target/release/clean ]]; then
  # GATE-FULL-ONLY BEGIN
  # GATE-LEG: green-artifact-recheck
  _gate_build 12 2 green-artifact-recheck scripts/green_artifact_recheck.sh \
    || fail "green-artifact recheck — a checked-in reports/*-green.json no longer reproduces (scripts/green_artifact_recheck.sh)"
  # GATE-FULL-ONLY END
else
  echo "  GREEN_RECHECK=SKIPPED reason=no-prebuilt-binary (targo --unverified build --locked --release -p clean, then rerun)"
fi

# ── THE THREE PROBE BATTERIES ────────────────────────────────────────────────
#
# `scripts/u2_battery.sh` (52 probes over universe/level semantics),
# `scripts/source_frontier_battery.sh` (32 fixtures carrying 42 pinned
# assertions over the three largest Mathlib-SOURCE failure classes) and the
# everyday-language battery (63 snippets, `cargo test -p clean-elab --lib
# test_r100_everyday_battery_full`) between them
# caught essentially every elaborator defect of the 2026-08 frontier work — and
# until this change NOT ONE of them was wired to any gate. All three ran only
# when a human remembered to run them. That is the registry's UNWIRED class
# (`scripts/check_gate_registry.py`, instance 2) three times over, on the three
# artifacts with the highest measured defect yield in the tree.
#
# WHY HERE AND NOT IN THE HOOK. The pre-push hook's contract is NO cargo and NO
# build: its 20-odd legs are sub-second Python, 17.5-18.5 s end to end
# (`scripts/githooks/gate-legs.txt`). Both `.lean` batteries drive a prebuilt
# `target/release/clean` over real fixtures and the everyday battery is a cargo
# test, so none of the three can live there without turning the hook into
# something people uninstall. Full mode already carries a 233 s workspace
# clippy, a ~75 s KV re-stamp and a ~30 min kernel suite; measured below, these
# three are small beside that.
#
# A MISSING PREREQUISITE IS A REFUSAL, NOT A SKIP — the one place these legs
# deliberately differ from `green-artifact-recheck` above. That leg prints
# `GREEN_RECHECK=SKIPPED reason=no-prebuilt-binary`, which is defensible for a
# leg that re-checks OTHER artifacts' claims. It is not defensible here: a
# battery that silently does not run is precisely the green stamp this whole
# file exists to stop shipping, and a skip is indistinguishable from a pass in
# every downstream reading. So each leg below names the exact build command and
# exits 1.
#
# READ-ONLY, AND ENFORCED RATHER THAN ASSUMED. Both `.lean` batteries END by
# rewriting a TRACKED artifact (`reports/u2-battery.json`,
# `reports/source-frontier-battery.json`) that embeds the HEAD sha and the
# binary's sha256, so a plain call would leave the tree dirty on EVERY gate run
# — and a gate that dirties the tree is a gate people learn to `git checkout`
# past. `_battery_readonly` restores the artifact's exact PRE-RUN BYTES (a copy,
# never `git checkout --`, which would clobber an operator's own uncommitted
# edit to it). Nothing is weakened by that: the verdict is the exit status and
# the per-probe lines above it, which are produced BEFORE the artifact is
# written and are what these legs read. Refreshing the artifact stays a
# deliberate act — run the battery directly.
#
# BOTH `.lean` BATTERIES ALSO FAIL CLOSED ON THEIR OWN INPUTS, which is why the
# source-frontier leg sets SRCFRONTIER_REQUIRE_PINNED=1 (that battery's
# header names this as the setting for "wherever the battery is wired into a
# gate"; u2 hard-fails on dirty inputs unconditionally). Consequence worth
# knowing before it surprises somebody: editing a fixture or a battery script
# and running the full gate before committing REFUSES, naming the dirty path.
# That is the intended contract — a probe pinned against an uncommitted fixture
# pins nothing — not a defect in these legs.
if [[ $FAST -eq 1 ]]; then
  echo "  LEAN_SUITE_CONFORMANCE=SKIPPED reason=fast-mode (needs target/release/clean and a lean4 tests checkout; runs in full mode, or directly: scripts/lean_suite_conformance.py)"
  echo "  LEAN_FRONT_DOOR=SKIPPED reason=fast-mode (needs target/release/clean; runs in full mode, or directly: scripts/lean_front_door_diff.py check --clean target/release/clean)"
  echo "  SRCELAB_BREADTH=SKIPPED reason=fast-mode (runs in full mode, or directly: scripts/source_elab_breadth.py --check-artifact)"
  echo "  U2_BATTERY=SKIPPED reason=fast-mode (needs target/release/clean; runs in full mode, or directly: scripts/u2_battery.sh)"
  echo "  SOURCE_FRONTIER_BATTERY=SKIPPED reason=fast-mode (needs target/release/clean; runs in full mode, or directly: SRCFRONTIER_REQUIRE_PINNED=1 scripts/source_frontier_battery.sh)"
  echo "  NATIVE_EXEC_BATTERY=SKIPPED reason=fast-mode (a targo --unverified test that builds and runs clean; runs in full mode, or directly: targo --unverified test --locked -p clean --test native_exec_battery)"
  echo "  EVERYDAY_BATTERY=SKIPPED reason=fast-mode (a targo --unverified test; runs in full mode, or directly: targo --unverified test --locked -p clean-elab --lib -q -- test_r100_everyday_battery_full)"
  echo "  REPLAY_REACHABILITY_CENSUS=SKIPPED reason=fast-mode (builds a clean-olean example and lib test; runs in full mode, or directly: scripts/replay_reachability_census.sh)"
else
  # GATE-FULL-ONLY BEGIN
  # Run a battery that rewrites a tracked artifact, and put the artifact back
  # byte-for-byte. Snapshot-and-restore rather than `git checkout --`: an
  # operator may legitimately be holding an uncommitted edit to the artifact,
  # and a gate leg may not decide to throw that away.
  _battery_readonly() { # <tracked-artifact> <command...>
    local artifact="$1"; shift
    local snapshot="" rc=0
    if [[ -e "$artifact" ]]; then
      snapshot="$(mktemp "${TMPDIR:-/tmp}/gate-battery-artifact.XXXXXX")"
      cp "$artifact" "$snapshot"
    fi
    "$@" || rc=$?
    if [[ -n "$snapshot" ]]; then
      cp "$snapshot" "$artifact"
      rm -f "$snapshot"
    elif [[ -e "$artifact" ]]; then
      rm -f "$artifact"
    fi
    return "$rc"
  }

  # GATE-LEG: lean-suite-conformance
  # THE TWO-WAY ORACLE, MEASURED: every file in data/lean_suite_conformance.json
  # through target/release/clean (60 s / 2 GiB cap per file, a cap hit is its
  # own outcome), against the pinned Lean's recorded verdict. Fails on any file
  # the ledger records as AGREEING that no longer agrees and on ANY new
  # clean-accepts-lean-rejects file -- the silent-acceptance face no Mathlib
  # count can see. Needs the release binary (REFUSES without it, like the
  # batteries below) and a lean4 checkout at the ledger's rev ($HOME/lean4-src or
  # LEAN4_TESTS_DIR; absent or foreign, the script prints a skipped: verdict).
  echo "== local gate: Lean test-suite two-way conformance (measured) =="
  [[ -x target/release/clean ]] \
    || fail "Lean test-suite conformance — REFUSING, not skipping: there is no executable target/release/clean. Build it and rerun: targo --unverified build --locked --release -p clean --bin clean"
  _gate_build 12 2 lean-suite-conformance "$GATE_PYTHON" scripts/lean_suite_conformance.py --jobs 2 \
    || fail "Lean test-suite conformance — a file the ledger records as agreeing with the pinned Lean no longer agrees, or Clean now ACCEPTS a file Lean rejects (NEW-DISAGREEMENT / NEW-FALSE-ACCEPT above). Fix it, or accept an improvement with scripts/lean_suite_conformance.py --update; a regression is accepted only with --update --rebase '<why>'"

  # GATE-LEG: lean-front-door
  # `clean lean` (the `lean`-compatible front door, docs/DECISIONS.md R74-R78),
  # BYTE FOR BYTE: every file reports/lean-front-door/byte-diff.json records as
  # MATCHING pinned Lean (same exit status, same stdout and stderr bytes) is run
  # again through target/release/clean and compared with the Lean bytes recorded
  # there (Lean is not re-run). Fails when one stops matching, when one's text
  # changed since it was measured, or when the artifact's rows and totals do not
  # follow from its hashes. REFUSES without the release binary; with no lean4
  # checkout the elab rows are skipped (LEAN_FRONT_DOOR=skipped:corpus-absent)
  # and the in-repository fixtures still run.
  echo "== local gate: clean lean byte-diff against pinned Lean =="
  [[ -x target/release/clean ]] \
    || fail "clean lean byte-diff — REFUSING, not skipping: there is no executable target/release/clean. Build it and rerun: targo --unverified build --locked --release -p clean --bin clean"
  { "$GATE_PYTHON" scripts/lean_front_door_diff.py --selftest >/dev/null \
      && _gate_build 12 2 lean-front-door "$GATE_PYTHON" scripts/lean_front_door_diff.py check --clean target/release/clean; } \
    || fail "clean lean byte-diff — a file that matched pinned Lean byte for byte no longer does (FAIL lines above), its text changed, or the artifact is inconsistent. Fix the regression, or re-measure with scripts/lean_front_door_diff.py measure --clean target/release/clean --update"

  # GATE-LEG: srcelab-breadth-artifact
  # The breadth measurement (scripts/source_elab_breadth.py run) is PERIODIC --
  # about 2.8 h of gated wall per 12 Mathlib files -- and is deliberately not a
  # push leg. What is checked here is cheap: every committed
  # reports/source-elab/breadth-*.json re-derives its pooled rate, intervals and
  # walls from its own rows, obeys its sample rule, and does not lower a file's
  # count against an earlier artifact of the same sample and corpus.
  echo "== local gate: source-elab breadth artifact =="
  { "$GATE_PYTHON" scripts/source_elab_breadth.py --selftest >/dev/null \
      && "$GATE_PYTHON" scripts/source_elab_breadth.py --check-artifact; } \
    || fail "source-elab breadth artifact — a committed reports/source-elab/breadth-*.json no longer re-derives from its own rows, breaks its sample rule, or lowers a count against an earlier artifact of the same sample (see above); re-aggregate it with scripts/source_elab_breadth.py aggregate, never by hand"

  # GATE-LEG: u2-battery
  echo "== local gate: U2 universe/level probe battery (52 probes) =="
  [[ -x target/release/clean ]] \
    || fail "U2 battery — REFUSING, not skipping: there is no executable target/release/clean, and a battery that does not run is not a gate. Build it and rerun: targo --unverified build --locked --release -p clean --bin clean"
  _battery_readonly reports/u2-battery.json _gate_build 12 2 u2-battery scripts/u2_battery.sh \
    || fail "U2 universe/level battery — a probe drifted: a PASS-pinned fixture no longer reports its exact declaration count, a MUST_FAIL fixture PASSED (a rung flipped it — re-pin deliberately, with a dated note in the battery), a pinned failure changed SHAPE, or the battery's own inputs are untracked/dirty. The offending fixture and the expected fragment are named above (scripts/u2_battery.sh)"

  # GATE-LEG: source-frontier-battery
  echo "== local gate: Mathlib-source frontier probe battery (32 fixtures) =="
  [[ -x target/release/clean ]] \
    || fail "source-frontier battery — REFUSING, not skipping: there is no executable target/release/clean, and a battery that does not run is not a gate. Build it and rerun: targo --unverified build --locked --release -p clean --bin clean"
  _battery_readonly reports/source-frontier-battery.json \
    _gate_build 12 2 source-frontier-battery env SRCFRONTIER_REQUIRE_PINNED=1 scripts/source_frontier_battery.sh \
    || fail "Mathlib-source frontier battery — a probe drifted in class I (instance search through a def-based alias), class II (dot notation whose target does not resolve) or mask 3 (auto-implicit swallowing an unresolved head): a PASS-pinned fixture no longer reports its exact count, a MUST_FAIL fixture PASSED, a pinned diagnostic fragment changed shape, or (SRCFRONTIER_REQUIRE_PINNED=1) a gate input is untracked/dirty. The offending fixture and fragment are named above (scripts/source_frontier_battery.sh)"

  # GATE-LEG: native-exec-battery
  #
  # The native path's no-wrong-answer contract: every program under
  # tests/fixtures/native_exec_battery runs through the real `clean run` and is
  # byte-identical to pinned Lean v4.30.0-rc2 (committed expected
  # stdout/stderr/status, minted by `lean --run`) or refused with a named
  # error; WRONG_OUTPUT_EXIT0 must be 0, and a verdict that moves off its pin in
  # reports/native-exec-battery.json is a result to re-pin deliberately. The
  # SAME two fail-open paths as the everyday battery below are closed the same
  # way: CLEAN_NATIVE_EXEC_UPDATE would turn the test into an artifact
  # generator (stripped with `env -u`), and an absent report would leave it
  # nothing to compare against (refused here, and by the test itself).
  echo "== local gate: native execution battery (byte-exact vs pinned Lean) =="
  [[ -f reports/native-exec-battery.json ]] \
    || fail "native execution battery — REFUSING: reports/native-exec-battery.json is absent, and it is the battery's pin set. Restore it from git, or re-mint it deliberately: CLEAN_NATIVE_EXEC_UPDATE=1 targo --unverified test --locked -p clean --test native_exec_battery"
  _gate_build 12 2 native-exec-battery env -u CLEAN_NATIVE_EXEC_UPDATE \
    scripts/cargo_test_nonvacuous.sh native-exec-battery -- \
    targo --unverified test -p clean --locked --test native_exec_battery \
    || fail "native execution battery — a program printed bytes pinned Lean does not (WRONG_OUTPUT_EXIT0 / WRONG_OUTPUT / CRASH / TIMEOUT), or a verdict moved off its pin in reports/native-exec-battery.json (a flip is a RESULT: re-pin with CLEAN_NATIVE_EXEC_UPDATE=1 and say why). The offending program is named above (crates/clean/tests/native_exec_battery.rs)"

  # GATE-LEG: parse-parity
  #
  # The differential parse gate: every probe in
  # tests/fixtures/parser_parity/ground_truth.tsv, captured from pinned Lean
  # v4.30.0-rc2, is parsed by clean-parser and classified MATCH / LOUD /
  # SILENT-DIVERGENT against Lean's tree. Red on a divergence the allowlist
  # does not pin, on a stale allowlist entry, on a family off its MATCH floor
  # either way, and on a README scoreboard that no longer matches the run.
  # Until 2026-09-30 nothing ran it, and it was found red on main: the renderer
  # panicked on binders made unspellable weeks earlier, and past that five
  # rows diverged. It is the only gate here that compares a PARSE TREE with
  # Lean's, which no count of successes can do.
  echo "== local gate: parse parity (clean-parser trees vs pinned Lean) =="
  _gate_build 12 2 parse-parity scripts/cargo_test_nonvacuous.sh parse-parity -- \
    targo --unverified test --locked -p clean-parser --test parse_parity \
    || fail "parse parity — clean-parser's tree for a probe in tests/fixtures/parser_parity/ground_truth.tsv disagrees with pinned Lean and is not allowlisted (a new silent misparse), an allowlisted probe no longer diverges (delete its entry), a family's MATCH count moved off its floor (the message prints the table to paste), or the README scoreboard is stale. The probe is named above (crates/clean-parser/tests/parse_parity.rs)"

  # GATE-LEG: replay-reachability-census
  #
  # The by-name census (crates/clean-olean/src/recheck_closed/
  # by_name_census_tests.rs) gates every name the dependency-closed replay's
  # kernel code mentions BY NAME, but only over the items its source scan
  # decides the replay can REACH. That reach is an over-approximation the test
  # cannot check against itself: measured 2026-10-07, deleting the census's
  # implicit `Drop::drop` resolution left the census test GREEN while the
  # linker still kept 18 kernel items (`Expr`, `Name`, `LevelArc` drops among
  # them) the census no longer saw. This leg links a binary that calls only
  # `recheck_closed`, demangles what the linker kept, and refuses any kept
  # kernel item the census did not reach. Until 2026-10-07 nothing ran it.
  echo "== local gate: replay reachability census (linker-kept items vs the by-name census) =="
  _gate_build 12 2 replay-reachability-census bash scripts/replay_reachability_census.sh \
    || fail "replay reachability census — the linker keeps a kernel item reachable from recheck_closed that the by-name census did NOT reach, so the census's verdict is vacuous for it (MISSING rows above), or the census could not run (no demangler, a build failure, an empty dump). Widen the census's reach in crates/clean-olean/src/recheck_closed/by_name_census_tests*.rs (scripts/replay_reachability_census.sh)"

  # GATE-LEG: everyday-battery
  #
  # TWO fail-open paths in the test itself are closed HERE, deliberately, and
  # neither is hypothetical:
  #   * with CLEAN_EVERYDAY_UPDATE set the test REWRITES the artifact and
  #     returns, so an operator who happens to have that variable exported would
  #     turn this leg into an artifact generator that can never disagree with
  #     anything. `env -u` removes it for this leg only.
  #   * with the artifact ABSENT the test prints a NOTE and returns green,
  #     measuring nothing. An absent artifact is refused here instead.
  # The cargo call is wrapped in scripts/cargo_test_nonvacuous.sh for the same
  # reason the soundness-cert leg is: a filter that selects zero tests exits 0
  # and libtest calls it `ok`.
  echo "== local gate: everyday-language battery (63 snippets) =="
  [[ -f reports/everyday-battery.json ]] \
    || fail "everyday battery — REFUSING: reports/everyday-battery.json is absent, and the test treats an absent artifact as a PASS (it prints a NOTE and returns), so this leg would measure nothing. Restore it from git, or regenerate it deliberately: CLEAN_EVERYDAY_UPDATE=1 targo --unverified test --locked -p clean-elab --lib -q -- test_r100_everyday_battery_full"
  _gate_build 12 2 everyday-battery env -u CLEAN_EVERYDAY_UPDATE \
    scripts/cargo_test_nonvacuous.sh everyday-battery -- \
    targo --unverified test -p clean-elab --lib --locked -q -- test_r100_everyday_battery_full \
    || fail "everyday-language battery — either an R100 LOCKED snippet regressed (the assert names it: those 38 are byte-identical to the 2026-07-20 measurement and may not go backwards) or reports/everyday-battery.json is stale against the live 63-snippet run (a verdict flipped; regenerate with CLEAN_EVERYDAY_UPDATE=1 and commit it, never hand-edit)"
  # `@[implemented_by]`'s scope and the declarations the `attribute` command
  # may name (Lean's imported-module refusal, per elaboration run), on the
  # clean-elab lib-test build the battery above already made.
  _gate_build 12 2 implemented-by-scope scripts/cargo_test_nonvacuous.sh implemented-by-scope -- \
    targo --unverified test -p clean-elab --lib --locked -q -- tests_implemented_by_scope declared_here::tests \
    || fail "implemented_by scope — where an @[implemented_by] argument resolves, or which declarations an attribute [implemented_by]/[extern] command may name, moved off pinned Lean v4.30.0-rc2, or the filter selected zero tests (crates/clean-elab/src/tests_implemented_by_scope.rs, declared_here_tests.rs)"
  # GATE-FULL-ONLY END
fi

# Both checks reuse the standalone build in a dedicated target directory.
# GATE-LEG: trustcore-evidence-staleness
echo "== local gate: trust-core evidence staleness tripwire =="
trustcore_targo="$(scripts/rust_frontend.sh --targo)" \
  || fail "trust-core evidence staleness — cannot resolve the Trust Targo frontend"
evidence_target="${CLEAN_EVIDENCE_TARGET_DIR:-$PWD/target/clean-evidence-standalone}"
CARGO_TARGET_DIR="$evidence_target" build-slot --cpus 2 -- "$trustcore_targo" --unverified run --locked -q -p clean-evidence -- \
  check trustcore-staleness --repo-root "$PWD" \
  || fail "trust-core evidence staleness — the Rust checker could not run or reported stale evidence (see the diagnostic above)"

# GATE-LEG: python-minters-publication
echo "== local gate: Python tooling membership against published main =="
published_main="$(git ls-remote --exit-code --refs origin refs/heads/main)" || fail "Python tooling membership — cannot read published origin/main"
[[ "$published_main" =~ ^([0-9a-f]{40}|[0-9a-f]{64})$'\t'refs/heads/main$ ]] || fail "Python tooling membership — invalid origin/main advertisement"
CARGO_TARGET_DIR="$evidence_target" build-slot --cpus 2 -- "$trustcore_targo" --unverified run --locked -q -p clean-evidence -- \
  check python-minters --published "${BASH_REMATCH[1]}" --repo-root "$PWD" \
  || fail "Python tooling membership — see the diagnostic above (fetch origin main if its advertised commit is missing)"

# Crystal revalidation SCOPE. Every link-2a gate compares a spec module to a
# COMMITTED FIXTURE; the only thing that ever compared a fixture to a live
# trustc dump is scripts/crystal_fixture_freshness.py, whose answer is a dated
# record (data/crystal_chain_revalidation_*.json). Nothing bound those records
# to the clean-kernel source they were measured at, so nothing could say whether
# they still describe HEAD -- and at 891b7d153 they did not: three files had
# moved in crates/clean-kernel/src/env/ with every crystal gate green.
#
# Fails on CONTENT scope only -- a chained body's own defining source file
# moving. Whole-crate functy.N/enum.N/struct.N/@func.N renumbering, which moves
# on any crate item with zero instructions changed, is printed as a ledgered
# revalidation DEBT and does not fail: a gate that reddens on renumbering is a
# gate that gets switched off, taking the content case with it. ~0.24 s.
# GATE-LEG: crystal-revalidation-scope
echo "== local gate: crystal revalidation scope (chained-body source drift) =="
"$GATE_PYTHON" scripts/crystal_freshness_scope.py \
  || fail "crystal revalidation scope — either a chained body's own clean-kernel source moved since the newest data/crystal_chain_revalidation_*.json (the spec module may no longer transcribe the emitted body; re-derive with scripts/crystal_fixture_freshness.py against a fresh dump and commit a new record) or the def_path->source mapping went stale (scripts/crystal_freshness_scope.py)"

# Crystal ENUM TAG PIN. Four of the eleven chained bodies are matches over a
# kernel enum, and the emitted trust-ir names no variants -- it switches on the
# NUMERIC DISCRIMINANT, which Clean's side of the proof encodes too
# (clean_mode_tag, source_system_tag, expr_path_step_tag, level_kind_tag).
# The Reference guarantees the VALUES given a declaration order; nothing
# guaranteed the ORDER. Reordering two variants changes no behaviour of the Rust
# program and fails no other gate, while moving Cubical off 2 and leaving the
# registered module, the fixture and the lineage digest byte-identical. ~0.05 s.
# GATE-LEG: crystal-enum-tag-pin
echo "== local gate: crystal enum tag pin =="
"$GATE_PYTHON" scripts/check_enum_tag_pin.py \
  || fail "crystal enum tag pin — a chained enum's declaration order, discriminants, serde-index coherence, reflected tag def or recorded switch arms moved, so a registered crystal module now proves something about a body that is no longer shipped; see data/crystal_enum_tag_pin.json"

# Crystal FIXTURE PINS. The sibling of the leg above, and of the hole
# crystal_fixture_freshness.py exists to close -- one level DOWN, where nobody
# had looked. The rebaseline tool records the sha256 and byte length of every
# `*.trust-ir.txt` it mints; measured 2026-08-27, those fields were read by the
# minter and BY NOTHING ELSE in either tree. So twenty-one fixtures pinned the
# emitted IR that every link-2a lane compares its spec module against, a
# committed record said what they contained when a real compiler produced them,
# and the two were never compared: editing a fixture leaves every link-2a gate
# green, because every link-2a gate reads the fixture.
# It needs no compiler and no dump, which is exactly why it can be a leg where
# crystal_fixture_freshness.py cannot. A green here means "nobody edited a
# fixture since the last real measurement", NEVER "the chains are revalidated".
# ~0.04 s including its own four mutation arms.
# LZB ACTIVATION MINT. The four biggest proof terms in the crystal --
# `ir_lzb_deref_activation` and the three `*_seg` lemmas, ~45k characters -- are
# EMITTED by scripts/gen_lzb_activation.py from a list of execution segments,
# not typed. Two clauses, and the order matters: --self-test first (with the
# pre-strengthening parameters the emitter must reproduce, byte for byte, the
# four terms hand-written and kernel-checked at fc350b9c4, whose digests it
# pins), then --check (the committed Rust consts must be what it emits today).
# A generator whose output nothing re-derives is the class round 17 left open;
# this is that class closed for these four. ~0.05 s, pure Python.
# GATE-LEG: lzb-activation-mint
echo "== local gate: lzb activation mint =="
"$GATE_PYTHON" scripts/gen_lzb_activation.py --self-test \
  || fail "lzb activation mint SELF-TEST — the emitter no longer reproduces the four kernel-checked 2026-08-26 terms from the pre-strengthening parameters, so its shape has drifted and --check below proves nothing"
"$GATE_PYTHON" scripts/gen_lzb_activation.py --check \
  || fail "lzb activation mint — crates/clean-verify/src/spec/core_spec/eval_ir_lzb_activation.rs no longer holds what the generator emits. Re-emit (--emit) rather than hand-editing a 24k-character proof term; if the deref model's cost or return value changed, change DEREF_STEPS/deref_result and re-emit"

# LZD ACTIVATION MINT. The eight biggest proof terms in the DERIVED chain --
# `ir_lzd_deref_activation`, the three `*_seg` lemmas, the CPS induction and
# A4/A5 plus their no-fault corollary, ~90k characters -- are EMITTED by
# scripts/gen_lzd_activation.py from the same execution-segment description
# gen_lzb_activation.py uses, with two differences it has to carry: the deref is
# FORTY steps rather than seven because it is four real bodies, and every deref
# ALLOCATES, so each segment threads a (heap, counter, MemExt) state and every
# hypothesis about the entry heap is re-framed where it is used. Same two
# clauses in the same order as the leg above: --self-test (the emitter must
# reproduce the terms a kernel accepted, whose digests it pins), then --check.
# ~0.1 s, pure Python.
# GATE-LEG: lzd-activation-mint
echo "== local gate: lzd activation mint =="
"$GATE_PYTHON" scripts/gen_lzd_activation.py --self-test \
  || fail "lzd activation mint SELF-TEST — the emitter no longer reproduces the kernel-checked terms, so its shape has drifted and --check below proves nothing"
"$GATE_PYTHON" scripts/gen_lzd_activation.py --check \
  || fail "lzd activation mint — the committed Rust consts are no longer what the generator emits. Re-emit (--emit) rather than hand-editing a 38k-character proof term; if the derived deref's cost or return value changed, change DEREF_STEPS/child_of and re-emit"

# LZD SCTR MINT (E2). The five step-indexed proof terms of Level::is_zero -- the
# three `ir_lzd_*_sseg` local obligations (eval_ir_lzd_sctr.rs), the table's
# local obligation `ir_lzd_local` and the acceptance theorem `ir_lzd_pc`
# (eval_ir_lzd_pc.rs) -- are EMITTED by scripts/gen_lzd_sctr.py from the exact
# chain's own segment vocabulary (it imports gen_lzd_activation.py). Same two
# clauses in the same order as the leg above: --self-test (the emitter must
# reproduce the terms a kernel accepted, whose digests it pins), then --check.
# Pure Python.
# GATE-LEG: lzd-sctr-mint
echo "== local gate: lzd sctr mint =="
"$GATE_PYTHON" scripts/gen_lzd_sctr.py --self-test \
  || fail "lzd sctr mint SELF-TEST — the emitter no longer reproduces the kernel-checked step-indexed terms, so its shape has drifted and --check below proves nothing"
"$GATE_PYTHON" scripts/gen_lzd_sctr.py --check \
  || fail "lzd sctr mint — the committed step-indexed Rust consts are no longer what scripts/gen_lzd_sctr.py emits. Re-emit (--emit) rather than hand-editing a minted proof term"

# STACK LEMMAS MINT (E1 and before). The frame-stacking family, its
# module-extension twin and E1's node-keyed classifier and twin -- every term in
# crates/clean-verify/src/spec/core_spec/eval_ir_stack_minted.rs -- are EMITTED
# by scripts/gen_stack_lemmas.py, whose --self-test holds every term to the
# digest of a shape the kernel accepted and demonstrates that --check refuses
# three hand edits. It was unwired until the axes generator below began to
# IMPORT it: a generator nothing re-runs is how a derived artifact rots.
# Pure Python.
# GATE-LEG: stack-lemmas-mint
echo "== local gate: stack lemmas mint =="
"$GATE_PYTHON" scripts/gen_stack_lemmas.py --self-test \
  || fail "stack lemmas mint SELF-TEST — the emitter no longer reproduces the kernel-checked stacking terms, so its shape has drifted and --check below proves nothing"
"$GATE_PYTHON" scripts/gen_stack_lemmas.py --check \
  || fail "stack lemmas mint — eval_ir_stack_minted.rs is no longer what scripts/gen_stack_lemmas.py emits. Re-emit (--emit) rather than hand-editing a minted proof term"

# STACK AXES MINT (E1's open items). The bottom-frame dests family, the
# outcome-keyed module twin and the classifier's converse -- every term in
# eval_ir_stack_axes_minted.rs -- are EMITTED by scripts/gen_stack_axes.py,
# which imports gen_stack_lemmas.py for every table. Its --self-test pins the
# kernel-accepted digests, refuses three hand edits, and holds the twin to the
# running-keyed family by undoing the substitution. Pure Python.
# GATE-LEG: stack-axes-mint
echo "== local gate: stack axes mint =="
"$GATE_PYTHON" scripts/gen_stack_axes.py --self-test \
  || fail "stack axes mint SELF-TEST — the emitter no longer reproduces the kernel-checked axes terms (or the outcome-keyed twin no longer mirrors the running-keyed family), so --check below proves nothing"
"$GATE_PYTHON" scripts/gen_stack_axes.py --check \
  || fail "stack axes mint — eval_ir_stack_axes_minted.rs is no longer what scripts/gen_stack_axes.py emits. Re-emit (--emit) rather than hand-editing a minted proof term"

# IT SCTR MINT (E2, second instance). The eleven minted proof terms of
# TypeChecker::infer_type through the step-indexed device -- the body's local
# obligation `ir_it_top_sseg` (eval_ir_it_sctr.rs) and the table's local
# obligation, group soundness, acceptance theorem, safety corollaries, exact-
# premise instantiation, cross-check and non-vacuity witnesses
# (eval_ir_it_pc.rs) -- are EMITTED by scripts/gen_it_sctr.py. Same two clauses
# in the same order as the leg above: --self-test (the emitter must reproduce
# the terms a kernel accepted, whose digests it pins), then --check. Pure
# Python.
# GATE-LEG: it-sctr-mint
echo "== local gate: it sctr mint =="
"$GATE_PYTHON" scripts/gen_it_sctr.py --self-test \
  || fail "it sctr mint SELF-TEST — the emitter no longer reproduces the kernel-checked step-indexed terms for infer_type, so its shape has drifted and --check below proves nothing"
"$GATE_PYTHON" scripts/gen_it_sctr.py --check \
  || fail "it sctr mint — the committed step-indexed Rust consts for infer_type are no longer what scripts/gen_it_sctr.py emits. Re-emit (--emit) rather than hand-editing a minted proof term"

# LZD LAYOUT FACTS. A4/A5 over ir_lzd_module carry no authored FUNCTION; they
# still carry authored NUMBERS, and those had up to four independent spellings
# held in step by nothing but agreement -- the relation's a+8 / a+16 / +16, the
# proof-term generator's child_of(), the emitted body's own gep constants, and
# the ArcInner offset recomputable from the producer's struct table. This derives
# each from a COMMITTED artifact and refuses on disagreement, naming both sides.
# It runs no compiler and reads no dump. ~0.1 s, pure Python, four mutation arms.
# GATE-LEG: lzd-layout-facts
echo "== local gate: lzd layout facts =="
"$GATE_PYTHON" scripts/check_lzd_layout_facts.py --self-test \
  || fail "lzd layout facts SELF-TEST -- the gate no longer refuses a planted layout disagreement, so the check below proves nothing"
"$GATE_PYTHON" scripts/check_lzd_layout_facts.py \
  || fail "lzd layout facts -- a layout constant in the ir_lzd proof no longer matches the artifact it is supposed to describe. The recomputation from the producer's own struct table is the one to trust"

# SLOT LEMMA MINT. Phase-B's return-slot family -- the 26 terms of
# `crates/clean-verify/src/spec/core_spec/eval_ir_slot_lemmas.rs`, the
# alloca/store/load/ret slot closed at an ABSTRACT allocation counter -- was
# emitted by a script OUTSIDE the repo, so nothing in-tree could re-derive it or
# see a hand-edit. Same two clauses in the same order as the leg above:
# --self-test first (re-emitted under the Phase-B probe's OWN names, all 26 must
# reproduce byte for byte the terms that probe KERNEL-CHECKED, 28/28, whose
# sha256s it pins), then --check (the committed consts, the DECLS registration
# order and SLOT_LEMMA_NAMES must be what it emits today). ~0.05 s, pure Python.
# GATE-LEG: slot-lemma-mint
echo "== local gate: slot lemma mint =="
"$GATE_PYTHON" scripts/gen_slot_lemmas.py --self-test \
  || fail "slot lemma mint SELF-TEST — the emitter no longer reproduces the terms the Phase-B kernel probe accepted, so its shape has drifted and --check below proves nothing"
"$GATE_PYTHON" scripts/gen_slot_lemmas.py --check \
  || fail "slot lemma mint — crates/clean-verify/src/spec/core_spec/eval_ir_slot_lemmas.rs no longer holds what the generator emits. Re-emit (--emit, then rustfmt) rather than hand-editing a proof term; a DECLS or SLOT_LEMMA_NAMES disagreement means the stage gained or lost a declaration nobody recorded"

# LZD READINESS. Could the DERIVED closure of `level::Level::is_zero` be minted
# as ONE EvalIR module? Two mechanical questions, both fail-closed: every opcode
# in the five merged bodies must be a MODELLED IRInst constructor (census derived
# twice and required to agree, through evalir_coverage's own parser -- imported,
# never re-implemented, so there is one reader of that denominator), and every
# call must reach a body in the pair (joined by NAME through the committed
# closure record, because @func.N renumbers between dumps). --self-test first,
# then --check, same order and same reason as the two legs above. ~0.1 s, pure
# Python; it builds nothing and proves nothing -- READY means only that the two
# obstacles to attempting the Phase-B mint are absent.
# GATE-LEG: lzd-readiness
echo "== local gate: lzd readiness =="
"$GATE_PYTHON" scripts/crystal_lzd_readiness.py --self-test \
  || fail "lzd readiness SELF-TEST — the instrument no longer refuses a closure it should refuse, so --check below proves nothing"
"$GATE_PYTHON" scripts/crystal_lzd_readiness.py --check \
  || fail "lzd readiness — data/crystal_lzd_readiness.json is not what the instrument derives. An UNMODELLED opcode means the Phase-B module cannot be minted until the machine has a dispatch arm for it; an unresolved call means it would go stuck no_func"

# GATE-LEG: crystal-fixture-pins
echo "== local gate: crystal fixture pins =="
"$GATE_PYTHON" scripts/check_crystal_fixture_pins.py \
  || fail "crystal fixture pins — a committed *.trust-ir.txt no longer equals the digest the newest rebaseline record minted for it, or the fixture set gained/lost a member; the spec modules are compared against that text, so a theorem may now describe a body no measurement ever saw. Re-derive from a dump (scripts/crystal_fixture_freshness.py), never by editing the pin"

# Crystal A0/A6 PROBE TRANSCRIPTION. data/crystal_a0_a6_probe.json was re-minted
# 2026-08-25 from A0 4-of-6 / A6 3-of-4 to A0 5-of-6 / A6 4-of-4 -- and the
# re-mint is NOT a measurement: every current verdict in it is COPIED from a
# committed record. A file that asserts "each verdict is transcribed from a named
# committed record" and that nothing re-derives is exactly the class this
# registry exists to close, so the generator is also the checker: it re-reads all
# nine cited records, rebuilds the whole object, and refuses any disagreement.
# It re-derives the TRANSCRIPTION, never the crystal -- no trustc, no dump. ~0.3 s.
# GATE-LEG: a0a6-probe-transcription
echo "== local gate: crystal A0/A6 probe transcription =="
"$GATE_PYTHON" scripts/check_a0a6_probe_transcription.py \
  || fail "crystal A0/A6 probe transcription — data/crystal_a0_a6_probe.json disagrees with a committed record it cites, or a cited record moved without a re-mint; re-mint with scripts/check_a0a6_probe_transcription.py --mint and READ THE DIFF"

# GATE-LEG: paragon-ratchet
echo "== local gate: paragon quality ratchet =="
scripts/paragon_ratchet.sh || fail "paragon quality ratchet (see data/paragon_ratchet.json)"

# GATE-LEG: isabelle-ops-portability
echo "== local gate: portable Isabelle/Trust operations =="
"$GATE_PYTHON" scripts/test_isabelle_ops_portability.py \
  || fail "Isabelle/Trust operations portability regression"

# GATE-LEG: aristotle-corpus-static
echo "== local gate: Aristotle model-guide corpus (static) =="
"$GATE_PYTHON" scripts/aristotle_corpus_gate.py --fast \
  || fail "Aristotle corpus gate — a banned construct in code, a new vacuous Classical.propDecidable inhabitant of a Decidable target, a rung that gained an undischarged hypothesis, or composition byte-identity drift (which silently breaks the cross-file confluence discharge); see data/aristotle_corpus_ratchet.json. Elaboration is checked separately by 'just corpus-gate-full'."

if [[ $FAST -eq 0 ]]; then
  # GATE-FULL-ONLY BEGIN
  # GATE-LEG: a0-census-selftest
  # (full mode: needs no trust artifacts, ~0.1 s; kept out of the fast region
  # so the hook-coverage sha pin does not move. Audit r1: the census regex
  # requires the id ALONE on the marker line -- prose after it made this leg
  # invisible to check_gate_registry's leg census.)
  # Trust (2026-08-27, owner ruling R2 of workflow wf_1c3df27b): the A0
  # criterion is now the two-clause semantic obligation, computed by
  # scripts/crystal_a0_census.py against data/crystal_a0_discharge.json.
  # The file that COMPUTES a completion criterion must not be movable through
  # a row nobody runs: this leg replays its 27 refusal arms -- the seven
  # verify_prefix refusals (including the body/declaration partition the
  # criterion rests on), four closure-walk arms driven through the REAL
  # module-level walk (audit r4 M2: the old indirect arm tested its own
  # fixture flag, never the census walk), the discharge-core clause-(a)/(b)
  # arms, the mention-vs-registration arms, and the audit-r4 M1 path
  # constraint (non-.rs / outside-crates `where` refuses) -- and validates
  # the committed discharge table parses and names only real targets.
  echo "== local gate: A0 census selftest + discharge table =="
  "$GATE_PYTHON" scripts/crystal_a0_census.py --selftest \
    || fail "crystal_a0_census selftest — a refusal arm stopped firing; the A0 criterion computer can no longer be trusted to refuse"
  "$GATE_PYTHON" - <<'PYCHK' || fail "crystal_a0_discharge.json malformed"
import json, os
t = json.load(open("data/crystal_a0_discharge.json"))
assert t["schema"] == "clean.crystal.a0.discharge.v2"
for name, tgt in t["targets"].items():
    listed = {r.get("theorem"): r for r in tgt.get("clause_b_theorems", [])}
    # audit r1 M1: clause (b) is fail-closed here too -- a bare clause-b, an
    # unlisted theorem, or a theorem no source file registers all refuse.
    for r in tgt.get("clause_b_theorems", []):
        w = (r.get("where") or "").split()[0]
        assert w and os.path.isfile(w), (name, r.get("theorem"), w)
        th = r["theorem"]
        # audit r3 M3: no byte-copied mirror of the matcher any more -- round
        # 3 proved a mirror WILL drift (both copies carried the same
        # nested-comment lexing hole). The leg imports the census module and
        # calls THE function the census itself gates on, so the two surfaces
        # cannot disagree by construction.
        import importlib.util as _ilu
        _spec = _ilu.spec_from_file_location("_census", "scripts/crystal_a0_census.py")
        _census = _ilu.module_from_spec(_spec)
        _spec.loader.exec_module(_census)
        assert _census.clause_b_theorem_registered(th, w), (name, th, w)
    for k, ent in tgt["escaping_callees"].items():
        # v2: keys are trust-ir callee NAMES (durable), not func_ids (volatile)
        assert isinstance(k, str) and k.strip() and not k.isdigit(), (name, k)
        assert ent["clause"] in ("a", "b"), (name, k)
        if ent["clause"] == "a":
            # audit r2 M-1 step 4: whitespace-only is silence too.
            assert str(ent.get("model") or "").strip() and str(
                ent.get("residual") or "").strip(), (name, k)
        if ent["clause"] == "b":
            th = ent.get("theorem")
            assert th and th in listed, (name, k, th)
# NOTE (audit r1): callee-vs-walk agreement is checked only by the heavy census
# runs against a dump; this leg checks WELL-FORMEDNESS + theorem registration.
print(f"discharge table: {sum(len(t2['escaping_callees']) for t2 in t['targets'].values())} entries across {len(t['targets'])} target(s), well-formed; clause-b theorems source-verified")
PYCHK

  # GATE-LEG: kcheck-trusted-rows
  # X5 bounded runtime source inventory and exact per-row decision approvals.
  # This is administrative evidence; byte lineage and compiled authority stay open.
  echo "== local gate: kcheck runtime dependency inventory =="
  "$GATE_PYTHON" scripts/check_kcheck_trusted_rows.py --selftest \
    || fail "kcheck-trusted-rows selftest -- a planted inventory/decision defect escaped"
  "$GATE_PYTHON" scripts/check_kcheck_trusted_rows.py \
    || fail "kcheck-trusted-rows -- inspect the source envelope and record an exact row decision"

  # GATE-LEG: kcheck-coverage
  # Interim thread step K3: data/kcheck_coverage.json counts the real
  # declarations the adopted checker accepted in one run of theories/kcheck_run.
  # A second reader that shares no code with the Lean loader must agree with the
  # run's classes, names, details and statement echoes, or the record is
  # refused. Exit 3 (no record yet, or its Lean sources moved) is not a failure
  # here: the scoreboard leg below then derives the figure as ABSENT with that
  # reason, and fails once, until the board is re-minted, if the committed board
  # still states a number. No Lean toolchain is used; the rebuild is
  # `kcheck_coverage.py --replay`. This leg runs first so that the cause is
  # printed before the board that reads it.
  echo "== local gate: kcheck coverage =="
  "$GATE_PYTHON" scripts/kcheck_coverage.py --self-test \
    || fail "kcheck-coverage self-test -- a planted forged or miscounted run escaped"
  kcheck_coverage_rc=0
  "$GATE_PYTHON" scripts/kcheck_coverage.py --check || kcheck_coverage_rc=$?
  case "$kcheck_coverage_rc" in
    0) ;;
    3) echo "  KCHECK_COVERAGE=UNKNOWN (no current record; the scoreboard derives the figure as ABSENT)" ;;
    *) fail "kcheck-coverage -- the second reader refuses the record; re-mint with: python3 scripts/kcheck_coverage.py --write --advice-origin '<command>'" ;;
  esac

  # GATE-LEG: self-proof-scoreboard
  # W0 checks the saved scoreboard with the checkout-built native comparator.
  # A record that disagrees with its sources fails; an absent source reads
  # ABSENT, never zero. It states where the work stands and proves nothing.
  echo "== local gate: self-proof scoreboard =="
  _gate_build 47 3 self-proof-scoreboard env CARGO_PROFILE_DEV_DEBUG=0 CARGO_PROFILE_TEST_DEBUG=0 \
    CARGO_TARGET_DIR="$PWD/target/w0-scoreboard-gate" CARGO_BUILD_BUILD_DIR="$PWD/target/w0-scoreboard-gate" \
    scripts/run_w0_scoreboard_gate.sh "$GATE_PYTHON" "$trustcore_targo" \
    targo --unverified test --locked --offline -p clean-cli -p clean --lib --test w0_scoreboard_cli --message-format=json -- cmd_evidence:: \
    || fail "self-proof-scoreboard -- build, self-test or board check failed (see above); re-mint a stale board with: \`clean evidence status --scoreboard --write\`"

  # GATE-LEG: authority-sites
  # (full mode: a self-test, then a lexed walk of crates/**/*.rs and of the
  # pinned Trust commit; timings in scripts/githooks/gate-legs.txt. Self-proof
  # plan unit P1: data/authority_sites.json names every site spelled in the
  # scanned vocabulary that mints an authority-shaped acceptance, with the
  # checker and theory behind it, so the flip to kcheck has a map. A site the
  # tree has and the artifact does not name is a failure, and so is a named
  # mint whose recorded checker evidence left its function, a kernel claim whose
  # function calls no kernel entry or checked wrapper, and a first-risk list
  # above its ceiling. Where no Trust checkout holds the pinned commit the Trust
  # half reports `unknown` and the Clean half still decides; `just ci` runs the
  # Clean half alone (--clean-only). No cargo, no network.)
  echo "== local gate: authority-site census (selftest, then check) =="
  "$GATE_PYTHON" scripts/check_authority_sites.py --selftest \
    || fail "authority-sites SELFTEST -- the census arms no longer fire (a planted mint, a second mint in a named function, a mint hidden behind a #[cfg(test)] on a non-item, a sibling-tier label, a kernel-named counter, a new enum variant, a new read, a new checker root, a checker that left its function, a kernel claim with no kernel call or checked wrapper, a stale row, an unclassified row, an unread Clean site, a first-risk list above its ceiling, a Trust row with no TCB answer, a planted Trust consumer of the reference token, a Trust manifest newly linking a carrier of Clean's checkers, and plants in a copy of a real file against the real artifact)"
  "$GATE_PYTHON" scripts/check_authority_sites.py \
    || fail "authority-sites -- data/authority_sites.json does not match the tree: an authority-shaped label, kernel-named counter or checker root appeared that the census does not name, a named site's count moved, a named mint no longer names its recorded checker, a kernel claim cites no kernel call, the first-risk list rose above its ceiling, or a Trust manifest links one of Clean's checkers and is not listed. Read the site; \`python3 scripts/check_authority_sites.py --write\` refreshes the derived fields and a new construct/call row is then classified by hand"

  # GATE-LEG: provenance-anchors
  # (full mode; ~1 s — audit r6 class-closer. Lanes record pre-rebase worktree
  # HEADs in committed records, the rebase orphans the sha, and the record's
  # measurement tree becomes unrecoverable: rounds 5-6 found six such records
  # one at a time. This leg enforces the invariant that every sha-shaped
  # anchor in the audited record set resolves in this repo / ../trust /
  # ../trust-ir, carries an explicit unresolvability annotation, or is a
  # justified ALLOW row — so a NEW dangling anchor cannot land silently.)
  echo "== local gate: provenance anchors resolve =="
  "$GATE_PYTHON" scripts/test_provenance_anchor_paths.py \
    || fail "provenance path controls — explicit roots or inherited Git context weakened an anchor refusal"
  # Isolated worktrees need not have sibling checkouts. These scoped overrides
  # change only neighbor locations; the checker validates exact Git roots and
  # retains its complete subject inventory and every anchor/ref refusal.
  provenance_args=(scripts/check_provenance_anchors.py)
  if [[ ${CLEAN_GATE_TRUST_REPO+x} ]]; then
    provenance_args+=(--trust-repo "$CLEAN_GATE_TRUST_REPO")
  fi
  if [[ ${CLEAN_GATE_TRUST_IR_REPO+x} ]]; then
    provenance_args+=(--trust-ir-repo "$CLEAN_GATE_TRUST_IR_REPO")
  fi
  "$GATE_PYTHON" "${provenance_args[@]}" \
    || fail "provenance anchors — a committed record cites an unresolved sha, or an explicit neighbor path is invalid; check the selected repositories above (defaults ../trust and ../trust-ir), then re-anchor or annotate"

  # GATE-LEG: census-output-pin
  # (full mode; ~2 s — audit r11 M11-4. The arm-mutation gate pins the census's
  # REFUSALS; this pins its VERDICT. Measured: dropping `and bodyful(fid)[0]`
  # from the criteria dict left 34/34 arms, all_mutated_or_accounted, and every
  # gate green — a composition change that no refusal census can see. The
  # census is run here on a committed synthetic dump and its verdict surface
  # must match tests/fixtures/crystal_a0_census/expected.json.)
  echo "== local gate: A0 census output pin =="
  "$GATE_PYTHON" scripts/check_census_output_pin.py \
    || fail "census output pin — the A0 census's verdict moved on the committed fixture; re-mint expected.json in the same change and say what moved"

  # GATE-LEG: census-arm-mutation
  # (full mode; ~5 s — audit r6 class-closer. A selftest arm that does not
  # KILL the mutant it pins is vacuous: r4 M2, r6 M1 and this gate's own dry
  # run found six such arms. This leg deletes each guard in
  # scripts/crystal_a0_census.py from a COPY and requires --selftest to go
  # RED, with one accounted subsumption row; a drifted anchor fails closed.)
  echo "== local gate: census arm-mutation gate =="
  "$GATE_PYTHON" scripts/check_census_arms.py \
    || fail "census arm-mutation gate — an arm stopped killing the guard it pins, or the census moved without its table"

  # Workspace lint. This step used to be `cargo check --locked -q` under a
  # "workspace check" label, which was a misnomer: bare `cargo check` obeys
  # `default-members` (8 of 27 crates), so it compiled neither clean-autoform /
  # clean-ck0 / clean-reflect nor ANY test target of the 19 non-default members
  # — including crates/clean-verify/tests, where the crystal work lands.
  # `--workspace --all-targets` under clippy strictly subsumes what it did:
  # 27/27 crates, 521/521 targets, with the [workspace.lints.clippy] deny level
  # applied. Measured 2026-08-12 on an 18-core box: 233 s from an empty target
  # dir, 172 s on top of a warm default-members clippy. Default features only —
  # feature-gated code still needs its own `-p <crate> --features` run.
  #
  # Driven through scripts/rust_frontend.sh, which runs `targo tippy` with
  # these flags untouched and has no stock fallback (owner directive
  # 2026-09-28; Trust ships no `cargo-clippy`).
  #
  # SELFTEST FIRST, same contract as add-decl-ratchet / env-bypass-census /
  # fmt-changed. Three arms, ~1 s: a passing frontend is green with its args
  # verbatim; a real `-D warnings` violation keeps the frontend's own status;
  # no targo REFUSES (127) and never runs a stock cargo.
  echo "== local gate: workspace lint (27/27 crates, all targets) =="
  scripts/rust_frontend.sh --selftest \
    || fail "rust_frontend.sh --selftest -- the lint/format driver cannot be shown to keep a failing verdict or to refuse without targo, so its green means nothing"
  _gate_build 17 2 workspace-clippy scripts/rust_frontend.sh clippy --locked --workspace --all-targets -q -- -D warnings \
    || fail "workspace clippy (--workspace --all-targets) — a warning or error outside the default-members inner loop"

  # Format gate. CLAUDE.md has documented `fmt --all --check` as a pre-push leg
  # for months, but NO script ran it, so a fmt-dirty main could and did reach
  # origin (bc0941514, "main was fmt-dirty", three clean-elab files). Same
  # frontend resolver as the clippy leg above. Full mode only: measured 39 s
  # wall, too slow for the <30 s --fast path.
  echo "== local gate: workspace format =="
  # NOT `fmt --all --check`. That aborts on the Trust island form in
  # crates/clean-kernel/src/model_islands.rs and exits 1 having reported ZERO
  # formatting diffs -- a permanent red no formatting change can clear, which
  # tells a lane nothing and pushes it toward --no-verify. `--all` here is the
  # same predicate (per-file under --skip-children, filtered to exactly what
  # cargo fmt selects) minus that hole, and it fails closed.
  "$GATE_PYTHON" scripts/check_fmt_changed.py --all \
    || fail "workspace rustfmt (check_fmt_changed.py --all) — run 'just fmt' and commit the result"

  # Dependency trust-boundary gate (paragon axis 1: "every dependency verified,
  # continuously gated"). Runs the cargo-deny policy in deny.toml over the whole
  # resolved dep graph: advisories (RustSec DB), licenses (SPDX allow-list),
  # bans (rustls-only: no openssl/native-tls), sources (registry locked to
  # crates.io, git locked to carcara plus immutable first-party AY). FULL-mode
  # only — it resolves the entire graph against the advisory DB, too slow for
  # the <30s --fast pre-push path. The historical state in
  # data/dep_boundary_state.json is explicitly stale after AY's Git migration
  # until this gate is rerun. SKIPs green with a notice if cargo-deny is not
  # installed, so a contributor without the tool is not blocked (install:
  # cargo install cargo-deny --locked). cargo-deny reads the committed
  # Cargo.lock, including AY's immutable Git sources.
  echo "== local gate: dependency trust boundary (cargo-deny) =="
  if command -v cargo-deny >/dev/null 2>&1; then
    targo deny check \
      || fail "dependency trust boundary (targo deny check — advisory/license/ban/source violation; see deny.toml + data/dep_boundary_state.json)"
  else
    echo "  SKIP: cargo-deny not installed (install: targo --unverified install cargo-deny --locked)"
  fi

  # Per-crate supply-chain AUDIT tracker (cargo-vet — paragon axis 1: "every
  # third-party dependency VERIFIED"). Complements the cargo-deny GATE above:
  # deny checks advisories/licenses/bans/sources; vet adds per-crate human/imported
  # audit attestation (supply-chain/config.toml + audits.toml + imports.lock against
  # the trusted Mozilla/Google/Bytecode-Alliance/Embark/ISRG/Zcash registries).
  # SOFT/INFORMATIONAL by design — the historical graph exited 0 because the
  # remaining unaudited crates were carried as exemptions. The recorded state is
  # explicitly stale after AY's Git migration and must be refreshed. This remains
  # a MONOTONIC coverage tracker (audited fraction only rises / exemptions only
  # shrink), NOT a fail-closed gate that blocks every push. It prints the
  # audited-vs-exempted counts as a tracked metric. State: data/dep_audit_state.json.
  # SKIPs green with a notice if cargo-vet is absent (install: cargo install
  # cargo-vet --locked). cargo-vet reads the committed resolved graph.
  echo "== local gate: dependency supply-chain audit (cargo-vet, soft tracker) =="
  if command -v cargo-vet >/dev/null 2>&1; then
    if vet_out="$(targo vet 2>&1)"; then
      vet_line="$(printf '%s\n' "$vet_out" | grep -i 'Vetting Succeeded' || true)"
      echo "  ${vet_line:-$(printf '%s' "$vet_out" | tail -1)}"
      echo "  (informational tracker — monotonic: audited fraction only rises; see data/dep_audit_state.json)"
    else
      # Non-zero vet means a crate is neither audited nor exempted (a NEW unvetted
      # dependency slipped in). Surface it loudly but do NOT fail the gate — this is
      # the warn-mode contract. Refresh the baseline: `cargo vet` then re-run.
      echo "  WARN: targo vet reported unvetted dependencies (a new dep is neither audited nor exempted)."
      echo "        Refresh the baseline and update data/dep_audit_state.json. NOT failing the gate (soft tracker)."
      printf '%s\n' "$vet_out" | tail -8 | sed 's/^/        /'
    fi
  else
    echo "  SKIP: cargo-vet not installed (install: targo --unverified install cargo-vet --locked)"
  fi

  # KernelVerified gate (NON-VACUOUS): re-stamps the pinned, OOM-safe, deterministic
  # slice (data/kv_ratchet_slice.txt) on every run and enforces BOTH the KV ratchet
  # (kernel_verified must not drop below data/mathlib_kv_ratchet.json's baseline;
  # heuristic_kernel_verified must be 0) AND the elision subset gate (KV(opaque) ⊆
  # KV(opaque-and-theorem)). Re-measuring a real slice is what makes these guards
  # bite — a static committed summary or a 0 baseline would catch nothing. SKIPs
  # green inside the script when the clean binary or the Mathlib checkout is absent.
  # Full-mode only: re-stamping the slice costs ~75s, so the --fast pre-push hook
  # skips it (same contract as the elision gate it replaces + the full kernel suite).
  echo "== local gate: KernelVerified gate (re-stamps pinned slice) =="
  KV_GATE_VERDICT_FILE="$(mktemp "${TMPDIR:-/tmp}/kv_verdict.XXXXXX")"
  export KV_GATE_VERDICT_FILE
  _gate_build 12 2 kv-ratchet scripts/kv_ratchet_gate.sh \
    || fail "KernelVerified gate — re-stamping the pinned slice dropped a KernelVerified verdict (ratchet regression or elision subset breach); see data/mathlib_kv_ratchet.json + data/kv_ratchet_slice.txt"
  KV_VERDICT="$(cat "$KV_GATE_VERDICT_FILE" 2>/dev/null || echo 'KV_GATE=unknown')"
  rm -f "$KV_GATE_VERDICT_FILE"; unset KV_GATE_VERDICT_FILE

  # CLEAN_LAZY_CLOSURE no-weaker invariance gate. Now ALWAYS-ON: seeded by the
  # committed Minimal.olean fixture, it runs the truly-independent eager-vs-lazy
  # parity unit tests (clean-olean convert_expr vs the lazy mmap source) so a v3
  # shard-format encoder divergence is caught without a Mathlib checkout. The
  # corpus-scale binary leg still activates when KV_GATE_* are set.
  echo "== local gate: CLEAN_LAZY_CLOSURE no-weaker invariance gate =="
  KVINV_GATE_VERDICT_FILE="$(mktemp "${TMPDIR:-/tmp}/kvinv_verdict.XXXXXX")"
  export KVINV_GATE_VERDICT_FILE
  _gate_build 12 2 kv-invariance scripts/kv_invariance_gate.sh \
    || fail "kv invariance gate — lazy closure loading is not no-weaker than eager (an independent-parity unit test or the corpus leg failed)"
  KVINV_VERDICT="$(cat "$KVINV_GATE_VERDICT_FILE" 2>/dev/null || echo 'KVINV_GATE=unknown')"
  rm -f "$KVINV_GATE_VERDICT_FILE"; unset KVINV_GATE_VERDICT_FILE

  # Full clean-kernel lib suite (slow, ~30min). The soundness step above runs only
  # a name-filtered SUBSET; the full suite catches the rest — e.g. the env::tests
  # add_inductive duplicate-detection regression that sat red for days
  # (2026-06-13..15, fixed in 97e465e3) precisely because no gate ran the whole
  # suite. Full-mode only; the pre-push hook (`--fast`) deliberately skips it.
  echo "== local gate: full clean-kernel --lib suite (slow) =="
  _gate_build 19 2 kernel-lib targo --unverified test -p clean-kernel --lib --locked --features math-overlays -q \
    || fail "clean-kernel --lib suite (full)"

  # GATE-LEG: ay-bv-blast-gated
  #
  # 89 TESTS THAT NO CONFIGURATION COMPILED. `ay-bv-blast` gates six production
  # modules under bridge/ay_backend/proof_reconstruct/ plus crate::proved_gate,
  # and it is enabled by NOTHING: no dependent manifest, no .cargo alias, no
  # justfile recipe, no leg of this file. So `cargo test --workspace` and the
  # workspace clippy compiled zero of it, and 89 tests had never run in this
  # repo's history — 75 in proof_reconstruct, 14 in proved_gate.
  #
  # WHAT IS BEHIND THE FLAG IS THE POINT. proved_gate.rs's refusal tests are
  # the anti-vacuity controls of a PROVED GATE —
  # `proved_gate_kernel_rejects_corrupted_refutation` carries its own
  # `ANTI-VACUITY (LOAD-BEARING)` doc comment, beside
  # `instantiated_path_rejects_retargeted_conclusion`,
  # `..._rejects_wrong_operator_obligation` and `..._rejects_false_ground_shape`.
  # In a repo whose rule is that a gate nobody has seen fail is exit 0, having
  # the anti-vacuity controls themselves never compiled is that defect in its
  # purest form.
  #
  # THE FILTER IS EXACT, and measured so. Every module it names is gated in
  # full, so the nine filters select 89 and only 89 (2272 filtered out). A
  # prefix filter would have selected 692 because 603 UNGATED tests share the
  # proof_reconstruct prefix — and running those adds nothing, since
  # `cargo test --workspace` already covers them.
  #
  # Filtering saves almost no time and is kept for exactness rather than speed:
  # the 89 gated tests are themselves the expensive ones (715.61s of the full
  # configuration's 743.66s). Full-mode only for that cost.
  _gate_build 12 2 ay-bv-blast-gated scripts/cargo_test_nonvacuous.sh ay-bv-blast-gated -- \
    targo --unverified test -p clean-auto --locked --features ay-bv-blast --lib -q -- \
    proved_gate:: bv_blast_reflection:: bv_lowering_bridge:: theory_lemma_bv:: \
    theory_lemma_bv_compute_blast:: pcay_bvmul:: pcay_bvshift:: \
    tests_criterion tests_trust_cg_obligation \
    || fail "ay-bv-blast gated lane — a BV bit-blast proof-reconstruction test failed, or a proved-gate REFUSAL control stopped refusing. These 89 tests are compiled by no other configuration, so nothing else would catch it (crates/clean-auto, --features ay-bv-blast)."

  # GATE-LEG: farkas-constructive-feature
  #
  # A TEST NO CONFIGURATION COMPILED. `[[test]] farkas_constructive_feature`
  # (crates/clean-kernel/Cargo.toml) declares
  # `required-features = ["farkas-constructive"]`, and nothing enabled that
  # feature: no dependent manifest, no .cargo alias, no justfile recipe, no leg
  # of this file. So `cargo test --workspace` and the workspace clippy both
  # compiled ZERO of it, and its single assertion had never run.
  #
  # What it guards is NOT covered elsewhere. `tests/farkas_feature_contract.rs`
  # is ungated and does run, but it compares the metadata whitelist against the
  # cfg-gated modules — the CONTRACT. This one asserts the BEHAVIOUR under the
  # feature: that the narrow feature initializes only the constructive anchor,
  # and that each declaration it registers carries a proof term. Nothing else
  # asks that.
  #
  # It must have its OWN feature set, not a ride along an existing leg: the
  # property is narrowness, so adding math-overlays would defeat the assertion.
  # Measured 2026-09-15 on first compile: builds in 1m09s, runs in 5.53s, peaks
  # 5.74 GB, and PASSES — the test was sound all along and merely unreachable.
  # Full-mode only, for that build cost.
  _gate_build 19 2 farkas-constructive-feature scripts/cargo_test_nonvacuous.sh farkas-constructive-feature -- \
    targo --unverified test -p clean-kernel --locked --features farkas-constructive \
    --test farkas_constructive_feature -q \
    || fail "farkas-constructive feature test — the narrow feature no longer initializes only the constructive anchor, or a declaration it registers lost its proof term (crates/clean-kernel/tests/farkas_constructive_feature.rs). This is the behaviour half of the farkas trust boundary; tests/farkas_feature_contract.rs covers only the module whitelist."

  # GATE-LEG: runtime-lcnf-tests
  #
  # ELEVEN TESTS NO CONFIGURATION COMPILED -- and until 2026-09-15 they were
  # #[ignore]d on top of that. `runtime_lcnf` (crates/clean-compiler/src/lib.rs)
  # is `#[cfg(feature = "runtime-lcnf")]`, its emission half additionally
  # `trust-ir-backend`, and NOTHING enabled either: no dependent manifest, no
  # .cargo alias, no justfile recipe, no leg of this file -- so `cargo test
  # --workspace` and the workspace clippy compiled zero of it. The eleven
  # `actual_*` tests read the real-Lean `RuntimeProbe` module-system triple and
  # the pinned `Init/Prelude.olean`; they used to want two env vars nothing set
  # (CLEAN_RUNTIME_LCNF_FIXTURE / _PRELUDE), hence the #[ignore]. Since
  # 2026-09-15 they compile the fixture at test time from the pinned toolchain
  # (clean_olean::test_support, FAIL-CLOSED when it is absent), so retiring the
  # #[ignore] moved them from "ignored" to "green when invoked by hand, invoked
  # by no gate" -- the silent skip this leg closes. Full-mode only, for the
  # feature build (trust-ir-backend pulls the trust-ir git dependencies already
  # in Cargo.lock). Measured 2026-09-15 through scripts/cargo_test_nonvacuous.sh: 45.4 s wall with the feature build already cached (46 tests, 17.2 s of test time, NONVACUOUS=ok); the converting lane's first cold feature build of the same command was 1m51s wall.
  _gate_build 12 2 runtime-lcnf-tests scripts/cargo_test_nonvacuous.sh runtime-lcnf-tests -- \
    targo --unverified test -p clean-compiler --locked --features runtime-lcnf,trust-ir-backend \
    --lib -q -- runtime_lcnf \
    || fail "runtime-lcnf lane -- a captured-runtime LCNF lowering/emission test failed, or the pinned Lean RuntimeProbe fixture could not be compiled (crates/clean-compiler/src/runtime_lcnf/, features runtime-lcnf,trust-ir-backend). These tests are compiled by no other configuration, so nothing else would catch it."

  # GATE-LEG: dispatch-exhaustive-lint
  #
  # EXHAUSTIVE DISPATCH, BY TYPE. crates/clean-reflect denies clippy's three
  # wildcard lints crate-wide (src/lib.rs; each integration test root repeats
  # it): a catch-all arm over a trust-ir enum compiles unchanged when trust-ir
  # adds a variant, and the new instruction joins a refusal nobody chose for
  # it. The workspace lint above covers the crate too; this leg is the same
  # clippy scoped to the one crate, so that the refusal is demonstrated in a
  # one-crate build (data/gate_demonstrations.json, a wildcard planted over
  # `Inst`) rather than asserted of a 27-crate one, and the failure names the
  # crate. The deny is a default, not a `forbid`: an item-level `#[allow]` /
  # `#[expect]` silences it, so for `Inst` dispatches the refusal of EVERY
  # catch-all -- top level, inside a wrapper around the `Inst`, in a match
  # that names no variant, in a `macro_rules!` body, silenced or not -- is
  # crates/clean-reflect/src/dispatch_exhaustive_tests.rs (verifier r7), which
  # also tests that it reads every target and that every target root carries
  # the deny. Threat model: accidental catch-alls, not obfuscation.
  echo "== local gate: dispatch exhaustiveness (clean-reflect clippy) =="
  _gate_build 12 2 dispatch-exhaustive-lint scripts/rust_frontend.sh clippy --locked -p clean-reflect --all-targets -q -- -D warnings \
    || fail "dispatch-exhaustive-lint -- a warning in crates/clean-reflect, or a catch-all arm over an enum its crate root denies (clippy::wildcard_enum_match_arm, match_wildcard_for_single_variants, wildcard_in_or_patterns)"

  # The self-tests of this repo's own gate and tooling scripts.
  #
  # Twenty suites under scripts/test_* existed with ZERO callers until
  # 2026-08-22: not this gate, not the justfile, not a hook, not a suite row.
  # Running them for the first time found two RED (test_prove_theorem.sh 8/6,
  # test_publish_mathverse_mirror.sh 16/4) and seven that could not even IMPORT
  # without the repo root on PYTHONPATH. Both reds are ledgered with an expiry
  # in data/script_selftest_quarantine.json; the ledger fails closed on an
  # expired row, a stale row (a quarantined suite that starts passing) and a
  # malformed file, so it cannot decay into an off switch.
  #
  # Every test_* under scripts/, nested directories included (2026-11-10).
  # Full mode only: 21 s measured at 2026-08-22's 20 suites; 14 min 38 s
  # wall at 2026-11-10's 57, far over the ~30 s --fast budget.
  echo "== local gate: script self-tests (scripts/**/test_*) =="
  _gate_build 12 2 script-selftests scripts/check_script_selftests.sh \
    || fail "script self-tests — a self-test of one of this repo's gate/tooling scripts is red and unquarantined, or the quarantine ledger has an expired/stale/malformed row (data/script_selftest_quarantine.json)"

  # ── THE TRUST-CORE SOUNDNESS GATES ─────────────────────────────────────────
  #
  # `scripts/kernel_soundness_gate.sh`, `scripts/deny_sorry_gate.sh` and
  # `scripts/axiom_audit_release_check.sh` are the three gates that MINT the
  # trust-core launch evidence (reports/{kernel-soundness,deny-sorry,
  # axiom-audit}-launch-evidence.json) that `clean replacement status` reads.
  # All three are `kind: gate, claims: soundness` in data/gate_registry.json —
  # and until this change NOT ONE OF THEM WAS RUN BY ANYTHING. That is measured,
  # not asserted: the 2026-08-27 wiring audit re-derived every declared
  # `wired_by` edge with a discriminator that can tell a command from a data
  # string, and all four of their declared runners turned out to be REFERENCES —
  # a Rust `const` holding the path, a name inside an error message — never an
  # invocation (docs/analysis/2026-08-27-gate-registry-wiring-audit.md §A, §C).
  # A gate nobody runs is not a gate; three of them, on the rows whose claims
  # column reads `soundness`, is the registry's own UNWIRED class at its worst.
  #
  # The first two are wired HERE. The third is the LAST leg of this file, and
  # the split is deliberate — see the block at the end for why.
  #
  # WHAT WIRING THEM FOUND ON THE FIRST RUN, before a line of this block existed:
  # the committed kernel-soundness and deny-sorry launch evidence both record
  # `"status": "failed"` (1-of-3 and 5-of-6 steps). They are FAILED-RUN artifacts
  # left in the tree by the lane that recorded the demonstration arms
  # (7422b63a0): `--demonstrate` runs the REAL gate on a REAL mutation and
  # restores the file it MUTATED, but the gate also mints its evidence artifact
  # and nothing restores that. Both gates are GREEN at HEAD (measured below).
  # Refreshing those two artifacts is a deliberate, reviewable act; this leg
  # does not do it, and its own mint cannot add to the problem (see below).
  #
  # A MISSING PREREQUISITE IS A REFUSAL, NOT A SKIP — the same contract as the
  # three probe batteries above and for the same reason: a soundness gate that
  # silently does not run is exactly the green stamp this file exists to stop
  # shipping, and downstream a skip is indistinguishable from a pass.
  #
  # READ-ONLY, TWICE OVER, AND THE SECOND HALF IS THE POINT. Each of these three
  # `rm -f`s its tracked evidence artifact at startup and rewrites it at the end,
  # so a plain call would dirty the tree on EVERY gate run — and a gate that
  # dirties the tree is a gate people learn to `git checkout` past. The batteries
  # above solve that by snapshot-and-restore. These three also accept an explicit
  # output path, which is strictly stronger, so the leg does both:
  #   1. `*_EVIDENCE_PATH` points the mint at a temp file, so the tracked
  #      artifact is never opened at all — not deleted, not rewritten, and no
  #      window in which an interrupt leaves it missing;
  #   2. `_battery_readonly` still wraps the call as the BACKSTOP, so a future
  #      edit that re-hardcodes the path inside one of these scripts cannot
  #      silently start dirtying the tree again.
  # Neither weakens anything: the verdict is the exit status and the per-lane
  # lines, all produced before the artifact is written. Since the EV0 review
  # (2026-11-17) the first two scripts never write their committed receipt at
  # all: unset, the path is a fresh temp file, and a path naming the receipt is
  # refused, because only `clean replacement trust-core-evidence` mints it.
  #
  # THE STRIPPED ENV VARS EACH CLOSE A MEASURED FAIL-OPEN PATH, not a
  # hypothetical one:
  #   * REGEN_BASELINE — set, `lean4_parity` and the clean-elab `soundness_gate`
  #     test REGENERATE their Lean 4 baselines instead of checking against them
  #     (crates/clean-elab/tests/soundness_gate/baseline.rs:280).
  #     kernel_soundness_gate.sh unsets it internally; deny_sorry_gate.sh does
  #     NOT, and its steps 4-6 run both of those targets. An operator with it
  #     exported turns that gate into a baseline generator.
  #   * DENY_SORRY — `deny_sorry_not_enabled_in_parent`
  #     (crates/clean-kernel/tests/deny_sorry_gate.rs:212) RETURNS EARLY when it
  #     is set in the parent, so one of the eleven tests the gate counts becomes
  #     a no-op that still reports `ok`. The gate sets DENY_SORRY=1 per lane with
  #     its own `env`, so stripping it here costs those lanes nothing.
  #   * DENY_SORRY_GATE_CHILD — a child-process marker the subprocess test sets
  #     for its own re-exec; a parent that inherits one runs a child body where a
  #     no-op belongs, and the gate pins an exact count of eleven.
  #
  # COST, measured 2026-08-27 at c0d0e44a8 on this box (8 GB, --jobs 2, a second
  # lane building concurrently). Two numbers each, because the spread is the
  # whole story and one number would misinform:
  #                                     WARM      COLD (needs a clean-kernel build)
  #   kernel soundness gate              38 s      124 s
  #   DENY_SORRY clean gate              27 s      178 s
  # WARM is the leg's real steady-state cost — 65 s for the pair — and is what
  # this position buys: both run after the full clean-kernel --lib suite above,
  # so the compile is already paid unless a feature set differs. COLD is the same
  # legs when a clean-kernel edit (here, the other lane's) forces a ~55 s
  # recompile first. Either way it is small beside the 233 s workspace clippy,
  # the ~75 s KV re-stamp and the ~30 min kernel suite this block sits after.
  # They are LAST-BUT-ONE on purpose: `set -e` means a red here would otherwise
  # mask every leg after it, and they must still precede the kernel lint ratchet,
  # which runs `cargo clean -p clean-kernel`.
  declare -F _battery_readonly >/dev/null \
    || fail "internal: _battery_readonly is not defined — the trust-core soundness legs must stay AFTER the probe-battery block that defines it (scripts/local_gate.sh)"

  echo "== local gate: kernel soundness gate (3 lanes, mints trust-core evidence) =="
  ks_evidence="$(mktemp "${TMPDIR:-/tmp}/gate-kernel-soundness-evidence.XXXXXX")"
  _battery_readonly reports/kernel-soundness-launch-evidence.json \
    _gate_build 19 2 kernel-soundness env -u REGEN_BASELINE -u DENY_SORRY KERNEL_SOUNDNESS_EVIDENCE_PATH="$ks_evidence" \
    bash scripts/kernel_soundness_gate.sh \
    || { rm -f "$ks_evidence"; fail "kernel soundness gate — a trust-core soundness lane failed: the differential corpus no longer matches the Lean 4 baseline it was minted against (lane 0), Clean's kernel infers a different type than Lean 4 for a pinned expression (lane 1), or the clean-elab accept/reject corpus no longer splits the way the baseline says (lane 2). The failing lane is named above; reproduce it verbatim with: bash scripts/kernel_soundness_gate.sh"; }
  rm -f "$ks_evidence"

  echo "== local gate: DENY_SORRY clean gate (6 lanes, mints trust-core evidence) =="
  ds_evidence="$(mktemp "${TMPDIR:-/tmp}/gate-deny-sorry-evidence.XXXXXX")"
  _battery_readonly reports/deny-sorry-launch-evidence.json \
    _gate_build 19 2 deny-sorry env -u REGEN_BASELINE -u DENY_SORRY -u DENY_SORRY_GATE_CHILD DENY_SORRY_EVIDENCE_PATH="$ds_evidence" \
    bash scripts/deny_sorry_gate.sh \
    || { rm -f "$ds_evidence"; fail "DENY_SORRY clean gate — a curated sorry-free lane is no longer sorry-free, a production add_decl_* bypass is unaccounted/unsanctioned/over its pinned cap in data/unchecked_decl_ratchet.json, or DENY_SORRY=1 no longer blocks sorry-term creation in a subprocess. The failing step is named above; reproduce it with: bash scripts/deny_sorry_gate.sh -- it writes its run record to a fresh temp file and refuses the committed reports/deny-sorry-launch-evidence.json, which only clean replacement trust-core-evidence --deny-sorry mints"; }
  rm -f "$ds_evidence"

  # Trusted-kernel lint ratchet (audit #6): re-surfaces the dead_code/unused
  # debt that source-level #[allow] attributes hide in clean-kernel (the
  # workspace [lints] set these to warn; --force-warn pierces the attributes
  # — mechanism corrected audit r5 M1). Last because it
  # `cargo clean -p clean-kernel` (force-warn needs a fresh compile), which
  # would otherwise invalidate the suite's artifacts above. Full-mode only.
  echo "== local gate: trusted-kernel lint ratchet =="
  _gate_build 19 2 kernel-lint-ratchet scripts/kernel_lint_ratchet.sh \
    || fail "kernel lint ratchet (clean-kernel dead_code/unused grew — see data/kernel_lint_ratchet.json)"
  # GATE-FULL-ONLY END
fi

# Trust-verify SOUNDNESS ratchet (conditional): if a local Trust stage1 can be
# discovered portably, assert the verifier still leaves the genuinely-false
# canary obligations unproved (no false-proves). An explicitly configured but
# invalid/ambiguous toolchain fails closed; a machine with no Trust checkout
# retains the historical conditional skip. Fast (canaries only); the heavy
# coverage re-verify runs separately: scripts/trust_verify_ratchet.sh --coverage.
#
# FULL MODE ONLY, since 2026-08-25, and the reason is REACH, not cost. The leg
# costs 8.9 s -- cheap enough for any budget -- but the thing it measures is a
# Trust stage1 binary DISCOVERED OUTSIDE THIS REPOSITORY, on a schedule no Clean
# pusher controls. Until this change it sat after the `if [[ $FAST -eq 0 ]]`
# block and therefore ran in `--fast` too, which is the mode CLAUDE.md tells
# every lane to run before pushing: a Trust-side red became a Clean-side red
# that no Clean commit caused and no Clean commit could fix. That is precisely
# how a gate teaches people `--no-verify`. Its own curation row has said
# "Full gate only" since it was written; the code did not, and
# scripts/githooks/gate-legs.txt now carries a MODE column that this
# disagreement can no longer hide in.
#
# NOT SILENCED. It still runs, fail-closed, in full mode -- where it is RED at
# the time of this change, on a real finding (see the COST row in
# scripts/githooks/gate-legs.txt and the `trust_verify_ratchet` waiver in
# data/gate_registry.json). Moving it does not make it green and is not meant to.
if [[ $FAST -eq 1 ]]; then
  echo "  TRUST_VERIFY_SOUNDNESS=SKIPPED reason=fast-mode (reaches a Trust stage1 OUTSIDE this repo; runs in full mode, or directly: scripts/trust_verify_ratchet.sh --soundness)"
else
  # GATE-FULL-ONLY BEGIN
  # GATE-LEG: trust-verify-soundness
  if stage1_bin="$(bash scripts/trust_verify_ratchet.sh --locate-stage1)"; then
    echo "  using Trust stage1: $stage1_bin"
    echo "== local gate: trust-verify soundness ratchet =="
    _gate_build 12 2 trust-verify-soundness bash scripts/trust_verify_ratchet.sh --soundness \
      || fail "trust-verify soundness ratchet — a genuinely-false canary obligation was PROVED (verifier unsoundness; data/trust_verify_ratchet.json)"
  else
    locate_rc=$?
    if [[ "$locate_rc" -eq 2 ]]; then
      echo "== local gate: trust-verify soundness ratchet (SKIP: no local Trust stage1) =="
    else
      fail "Trust stage1 discovery is invalid or ambiguous; set TRUST_STAGE1_BIN explicitly"
    fi
  fi
  # GATE-FULL-ONLY END
fi

# Trust VERIFIED LANE over the crates brought to zero failed obligations
# (ALab Trust migration, 2026-10-02). ADDITIVE: publish/config.sh's
# `targo trust check --allow-l0-gaps --workspace --all-targets --all-features`
# step is untouched (measured 2026-10-01 it fails 17 of the 18 crates it
# reaches). This leg runs one `targo trust check --allow-l0-gaps --locked -p
# <crate> --lib` per crate pinned in data/trust_verified_lane.json, sequentially
# at -j 4, and scripts/check_trust_verified_lane.py refuses, by crate, any FAILED
# obligation, a non-zero exit, a vacuous (zero-obligation) report, or `proved`
# below the pinned floor. Unknown rows never count toward a floor; a green here
# is "nothing failed, the floor proved", NOT "verified".
#
# FULL MODE ONLY, for the same REACH reason as trust-verify-soundness above: it
# runs the Trust verifier from the pinned toolchain, outside this repo, and a
# verifier change can move these counts with no Clean commit. The comparator's
# own refusal arms run in both modes. The environment flags a verified run must
# not inherit (TRUSTFLAGS, RUSTFLAGS, CARGO_ENCODED_*) are stripped, and the
# lane gets its own CARGO_TARGET_DIR (targo's fingerprints never match cargo's).
echo "== local gate: trust verified lane (comparator selftest) =="
tvl_self="$("$GATE_PYTHON" scripts/check_trust_verified_lane.py --selftest 2>&1)" \
  || { printf '%s\n' "$tvl_self" >&2; fail "trust-verified-lane SELFTEST — the floor checker's refusal arms no longer fire, so a green from it means nothing (scripts/check_trust_verified_lane.py --selftest)"; }
echo "  ${tvl_self##*$'\n'}"
if [[ $FAST -eq 1 ]]; then
  echo "  TRUST_VERIFIED_LANE=SKIPPED reason=fast-mode (runs the Trust verifier from the pinned toolchain OUTSIDE this repo, minutes per crate; runs in full mode)"
else
  # GATE-FULL-ONLY BEGIN
  # GATE-LEG: trust-verified-lane
  echo "== local gate: trust verified lane (targo trust check, advisory, per crate) =="
  targo --unverified --version >/dev/null 2>&1 \
    || fail "trust verified lane — \`targo --unverified --version\` is refused, so the targo on PATH is not Trust's targo (a stale stage ships upstream cargo under that name)"
  tvl_crates="$("$GATE_PYTHON" scripts/check_trust_verified_lane.py --crates)" \
    || fail "trust verified lane — data/trust_verified_lane.json is refused (see above)"
  tvl_dir="$(mktemp -d "${TMPDIR:-/tmp}/gate-trust-verified-lane.XXXXXX")"
  tvl_exits=()
  while IFS= read -r tvl_c; do
    [[ -n "$tvl_c" ]] || continue
    mkdir -p "$tvl_dir/$tvl_c"
    tvl_rc=0
    _gate_build 19 4 trust-verified-lane env -u TRUSTFLAGS -u RUSTFLAGS -u RUSTDOCFLAGS -u CARGO_BUILD_RUSTFLAGS \
        -u CARGO_ENCODED_RUSTFLAGS -u CARGO_ENCODED_RUSTDOCFLAGS \
        CARGO_TARGET_DIR="${CLEAN_TRUST_VERIFIED_LANE_TARGET_DIR:-$PWD/target/trust-verified-lane}" \
      targo trust check --allow-l0-gaps --keep-going --locked -j 4 -p "$tvl_c" --lib \
        --report-dir "$tvl_dir/$tvl_c" >"$tvl_dir/$tvl_c/check.log" 2>&1 || tvl_rc=$?
    echo "  $tvl_c: targo trust check exit=$tvl_rc"
    tvl_exits+=(--exit "$tvl_c=$tvl_rc")
  done <<<"$tvl_crates"
  "$GATE_PYTHON" scripts/check_trust_verified_lane.py --reports "$tvl_dir" "${tvl_exits[@]}" \
    || { for l in "$tvl_dir"/*/check.log; do tail -15 "$l" >&2; done; rm -rf "$tvl_dir"; fail "trust verified lane — a pinned crate FAILED an obligation, exited non-zero, proved below its floor, or produced no/vacuous report (named above; pin: data/trust_verified_lane.json)"; }
  rm -rf "$tvl_dir"
  # GATE-FULL-ONLY END
fi

# Trust-ir CODEGEN ratchet (opt-in): compile clean-kernel with trustc and the
# codegen FLIP on, and assert the measured lowering/splicing/flip counts have
# not regressed. This is a DIFFERENT mechanism from the soundness ratchet above
# (`-Ztrust-verify`, the Level-0 verifier); it exercises the crystal's path,
# THIR -> trust-ir -> derived-MIR differential -> codegen flip.
#
# OPT-IN because it is a non-incremental release compile of clean-kernel under a
# compiler that lives outside this repo (~4 min), and because at 1.28% of `fn`
# bodies flipping there is no case for putting it on every local run yet. It is
# additive: nothing here relaxes an existing gate.
#
# The COMPILE stays opt-in, and that is a decision with a reason, not inertia:
# it is a non-incremental release compile of clean-kernel under a compiler that
# lives OUTSIDE this repo and moves on its own schedule. Making it mandatory
# would block every clean-side push on trust-side drift — which is not
# hypothetical, because `lowered`/`spliced` are red at HEAD today by established
# COMPILER DRIFT (reports/trust-ir-ratchet-verdict-2026-08-13.md) with the
# re-baseline deliberately left to the owner.
#
# What is NOT opt-in any more is the SIGNAL. The 2026-08-13 loss of 38 `agreed`
# verdicts went unnoticed for two days because nothing anywhere printed how long
# it had been since anyone measured. The staleness surface below costs no
# compiler and ~0.1 s, and it puts that number in front of a human on EVERY gate
# run, opted in or not.
# GATE-LEG: trust-ir-axes-selftest
echo "== local gate: trust-ir axis comparator (no compiler; ~0.1s) =="
"$GATE_PYTHON" scripts/trust_ir_axes.py selftest \
  || fail "trust-ir axis comparator selftest — the ratchet's own comparator is broken (scripts/trust_ir_axes.py)"
TRUST_IR_AXES_VERDICT="$(
  "$GATE_PYTHON" - <<'PY'
import datetime, json, subprocess, sys
try:
    doc = json.load(open("data/trust_ir_build_baseline.json"))
except (OSError, ValueError) as exc:
    print(f"trust-ir axes: NO BASELINE ({exc})")
    sys.exit(0)
gated = subprocess.run([sys.executable, "scripts/trust_ir_axes.py", "table"],
                       capture_output=True, text=True).stdout.strip().splitlines()[-1]
stamp = doc.get("updated_utc_date", "?")
try:
    # UTC on both sides: the baseline stamp is UTC, and comparing it to a LOCAL
    # date reads "-1d old" for a baseline written minutes ago west of Greenwich.
    today = datetime.datetime.now(datetime.timezone.utc).date()
    age = max(0, (today - datetime.date.fromisoformat(stamp)).days)
except ValueError:
    age = None
label = "STALE" if (age is None or age > 7) else "fresh"
print(f"trust-ir axes: baseline {stamp} ({'?' if age is None else age}d old) — {label}; {gated}")
PY
)"
echo "  ${TRUST_IR_AXES_VERDICT}"
case "$TRUST_IR_AXES_VERDICT" in
  *STALE*) echo "  ^ nobody has re-measured the trust-ir coverage axes in over a week."
           echo "    Run: CLEAN_TRUST_IR_BUILD=1 scripts/local_gate.sh   (or scripts/trust_ir_build.sh)" ;;
esac

# Upstream-Lean drop-in invariant (gap G11 / two-language plan). Cheap and
# compiler-free on the path it takes today, and fail-closed by construction:
# the runner exits non-zero on any probe outcome not covered by an ACTIVE
# exception row, on baseline/MANIFEST pin drift, on a lapsed or malformed
# waiver, on a waiver that covers nothing, and on a crash (never waivable).
#
# It is here rather than behind an opt-in because the two pre-existing
# instruments over the same corpus are BOTH invisible to this gate and neither
# fails on a named regression: crates/clean-parser's lean4_parser_compatibility_suite
# asserts an 85% FLOOR (how many may fail, never which), and
# crates/clean-elab/tests/phase1_full_corpus.rs is print-only and self-skipping
# unless CLEAN_PHASE1_FULL_CORPUS=1. Neither routes a corpus file through
# emit_trust_ir at all, which is the level TrustIr is the contract.
#
# Seeded 2026-09-20 (56 probes); SPLIT 2026-10-07 by measured cost, because the
# probes need `clean --features trust-ir-backend` built FROM THIS TREE and ~20
# min: this leg is the ledger half (`--ledger-only`, hook + fast), the probes are
# the full-only leg below (scripts/githooks/gate-legs.txt says why).
# Adapted to this file's structure at the merge that brought it onto main: a
# `# GATE-LEG:` marker (classified in scripts/githooks/gate-legs.txt), the
# resolved "$GATE_PYTHON" (the runner parses TOML), and its own self-test arms
# FIRST, for the same reason the registry and add_decl legs run theirs: a
# fail-closed runner whose refusals are only checked when somebody remembers
# is a green stamp.
# GATE-LEG: upstream-lean-dropin
echo "== local gate: upstream-Lean drop-in ledger (selftest, then --ledger-only) =="
"$GATE_PYTHON" tests/upstream-lean/run_upstream_lean.py --self-test \
  || fail "upstream-Lean drop-in SELFTEST — the runner's own refusal arms no longer fire, so a green from it means nothing (tests/upstream-lean/run_upstream_lean.py --self-test)"
"$GATE_PYTHON" tests/upstream-lean/run_upstream_lean.py --ledger-only \
  || fail "upstream-Lean drop-in ledger — a ledger row is malformed/lapsed/stale, a corpus pin is invalid, the baseline pin disagrees with tests/lean4_compat/MANIFEST.json, or the unseeded ramp expired (tests/upstream-lean/)"

# Upstream-Lean drop-in PROBES: `--build` measures this tree's `clean` against the
# baseline's Lean library, 240 s of CPU per probe; cold build 35m25s (2026-10-07).
if [[ $FAST -eq 1 ]]; then
  echo "  UPSTREAM_LEAN_PROBES=SKIPPED reason=fast-mode (a release build of clean --features trust-ir-backend plus 56 probes, ~20 min; runs in full mode, or directly: tests/upstream-lean/run_upstream_lean.py --build)"
else
  # GATE-FULL-ONLY BEGIN
  # GATE-LEG: upstream-lean-probes
  echo "== local gate: upstream-Lean drop-in probes (--build: this tree's clean, pinned Lean library) =="
  _gate_build 47 2 upstream-lean-probes "$GATE_PYTHON" tests/upstream-lean/run_upstream_lean.py --build \
    || fail "upstream-Lean drop-in probes — a probe outcome is not covered by its pin or an active exception row, a probe crashed, the subject could not be built from this tree, or the pinned Lean library is not installed (tests/upstream-lean/run_upstream_lean.py --build)"
  # GATE-FULL-ONLY END
fi

# GATE-LEG: trust-ir-codegen-ratchet
if [[ "${CLEAN_TRUST_IR_BUILD:-0}" == "1" ]]; then
  echo "== local gate: trust-ir codegen ratchet =="
  # `set -e` is on, so capture the status without letting a non-zero exit abort
  # the gate before it can distinguish SKIP (2) from FAIL.
  tib_rc=0
  _gate_build 47 2 trust-ir-codegen-ratchet bash scripts/trust_ir_build.sh || tib_rc=$?
  case "$tib_rc" in
    0) ;;
    2) echo "  SKIP: no local Trust stage1 toolchain" ;;
    *) fail "trust-ir codegen ratchet (data/trust_ir_build_baseline.json)" ;;
  esac
else
  echo "== local gate: trust-ir codegen ratchet (SKIP: set CLEAN_TRUST_IR_BUILD=1) =="
fi

# What the KV gates actually DID, not merely that they exited 0. Both have
# skip-green paths that fire routinely (absent corpus, low free RAM), so "the
# local gate is green" does NOT by itself mean the KernelVerified claim was
# re-measured. Surfacing the verdict here means nobody has to reconstruct which
# of the six paths a run took by re-reading stdout.
if [[ -n "${KV_VERDICT:-}${KVINV_VERDICT:-}" ]]; then
  echo "== local gate: KV measurement verdicts =="
  [[ -n "${KV_VERDICT:-}" ]]    && echo "  ${KV_VERDICT}"
  [[ -n "${KVINV_VERDICT:-}" ]] && echo "  ${KVINV_VERDICT}"
  case "${KV_VERDICT:-}" in
    KV_GATE=measured) ;;
    *) echo "  NOTE: the KernelVerified slice was NOT re-measured on this run."
       echo "        A green gate here is the ABSENCE of a measurement, not a passing one."
       echo "        Re-run with KV_GATE_REQUIRE_MEASURED=1 to make that a hard failure." ;;
  esac
fi

# The third trust-core soundness gate, and it is LAST BY DECISION.
#
# `scripts/axiom_audit_release_check.sh` is `kind: gate, claims: soundness` and,
# like its two siblings above, was run by nothing at all before 2026-08-27: both
# of its declared runners were Rust `const`s holding its path
# (docs/analysis/2026-08-27-gate-registry-wiring-audit.md §A). It re-derives
# data/axiom_audit.json — the first-class domain-axiom metric CLAUDE.md's
# soundness rules name — against live kernel output, so it belongs in a gate.
#
# IT IS RED AT HEAD, AND WIRING IT IS STILL THE RIGHT MOVE. Re-measured
# 2026-08-27 at c0d0e44a8: exit 1 in 158 s cold / 100 s warm. Lane 1 is GREEN
# (total_domain_axioms=0, total_all_axioms=0, total_theorems=3242,
# constructive_theorems=265) and lane 2 reports `per-conjecture rows drift from
# verify_gamma_crown --json output` on all FIFTEEN conjecture rows, with the same
# deltas the row's registry waiver recorded on 2026-08-25 (C001 theorems
# 312->329, definitions 361->337, opaques 6->4). The soundness headline does not
# move — 0 domain axioms stored, 0 live, no row gains an axiom — so this is
# bookkeeping drift, and the fix is one command that is deliberately a separate
# reviewable act:  python3 -m scripts.axiom_audit.reconcile
#
# SO WHY HERE, PHYSICALLY LAST. `set -e` means a fail-closed leg masks every leg
# after it. Placed with its siblings it would have hidden the kernel lint
# ratchet, the trust-verify soundness ratchet and the trust-ir axis surface
# behind a red that is already known and already owned. Placed here, after the
# KV verdict summary, it masks NOTHING: every other leg has run and printed, and
# the only thing its refusal costs is the final PASS line — which is the honest
# outcome while a soundness gate is red. It is not silenced and it is not
# skipped; the same shape the trust-verify-soundness leg above already has.
#
# WHAT THOSE NUMBERS DO NOT SAY, twice over: they are the cost to the FIRST failure,
# and a GREEN run costs strictly more (lane 2's constructive-claim closure then
# builds and runs the `clean` binary, which the drift refusal never reached);
# and it includes a clean-kernel rebuild under `--features "test-utils
# math-overlays"` which this position pays again, because kernel_lint_ratchet
# runs `cargo clean -p clean-kernel` above. If that cost ever stops being worth
# paying on every full run, the answer is to reconcile the fifteen rows, not to
# move the leg back where it can mask other work.
#
# `clean_BIN` is stripped: scripts/axiom_audit/verify.py:66 uses it as the
# `clean` binary for the constructive-claim closure, so an exported stale one
# reconciles this tree's audit against a binary that is not this tree's.
if [[ $FAST -eq 1 ]]; then
  echo "  AXIOM_AUDIT_RELEASE=SKIPPED reason=fast-mode (two cargo builds; runs in full mode, or directly: bash scripts/axiom_audit_release_check.sh)"
else
  # GATE-FULL-ONLY BEGIN
  declare -F _battery_readonly >/dev/null \
    || fail "internal: _battery_readonly is not defined — the axiom-audit release leg must stay AFTER the probe-battery block that defines it (scripts/local_gate.sh)"
  echo "== local gate: axiom-audit release check (2 lanes, mints trust-core evidence) =="
  aa_evidence="$(mktemp "${TMPDIR:-/tmp}/gate-axiom-audit-evidence.XXXXXX")"
  _battery_readonly reports/axiom-audit-launch-evidence.json \
    _gate_build 47 2 axiom-audit-release env -u clean_BIN AXIOM_AUDIT_EVIDENCE_PATH="$aa_evidence" \
    bash scripts/axiom_audit_release_check.sh \
    || { rm -f "$aa_evidence"; fail "axiom-audit release check — data/axiom_audit.json has stale aggregates (lane 1), its per-conjecture rows drift from live \`verify_gamma_crown --json\` output (lane 2), or a \`proof_mechanism: constructive\` claim no longer closes over the foundational axioms alone. A lane-2 row-drift red WAS the known state through 2026-08-30 and cleared at 7eca5eb2e (audit r7: a future red here is NEW, not the known one), 0 domain axioms stored and 0 live — see the axiom_audit_release_check waiver in data/gate_registry.json. The drifting rows are named above; refresh them deliberately with: python3 -m scripts.axiom_audit.reconcile"; }
  rm -f "$aa_evidence"
  # GATE-FULL-ONLY END
fi

# THE TRUST-IR BACKEND'S OWN TESTS (two-language roadmap WS6.0).
#
# 162 TESTS NO LEG RAN. `emit_trust_ir` / `emit_trust_ir_tv` / `emit_trust_ir_link`
# (crates/clean-compiler/src/lib.rs) are `#[cfg(feature = "trust-ir-backend")]`,
# and so are their test files -- emit_trust_ir_tests.rs,
# emit_trust_ir_identity_tests.rs, emit_trust_ir_tv_tests.rs,
# emit_trust_ir_link_tests.rs. The runtime-lcnf-tests leg above DOES compile
# the feature, but it filters to `-- runtime_lcnf`, and `cargo test --workspace`
# and the workspace clippy never enable it at all. So the emitter every other
# WS6 increment changes had its tests compiled by a gate configuration and run
# by none.
#
# WHAT ITS FIRST RUN FOUND, measured 2026-09-18 at 25c14240b with the roadmap's
# one-invocation spelling (`-- emit_trust_ir emit_c`, 268 tests: the 162 behind
# the feature -- emit_trust_ir::tests 76, ::identity_tests 16,
# ::perceus_reset_reuse_semantics_tests 1, emit_trust_ir_tv::tests 57,
# emit_trust_ir_link::tests 12 -- plus 106 C-backend tests the default
# workspace run already covers): 259 passed and 9 FAILED, every failure
# `trust-cg: ... failed to deserialize tMBC payload: unsupported version`. The
# nine are the native e2e tests (emit -> .tmbc -> trust-cg -> link -> run).
# They locate trust-cg themselves (emit_trust_ir_tests.rs `find_trust_cg`:
# $CLEAN_TRUST_CG_BIN, then ../trust-cg/target/{debug,release}, then PATH), and
# on this machine PATH holds the aterm-packaged trust-cg 0.6.0, which predates
# the wire version clean's pinned trust-ir writes -- the known packaging lag
# (two-language roadmap F-119). With a trust-cg built from source (684ebe77,
# and origin/main 10ff96f0) all nine pass. That is a real statement about the
# installed consumer, not a Clean defect, so the leg does not hide it: it NAMES
# the consumer the tests will use before running them, and it lets one
# variable select it -- `TRUSTCG_BIN`, the same one the census leg below
# takes -- by forwarding it as CLEAN_TRUST_CG_BIN. A selected path that is not
# an executable file is a refusal here, because the tests' own discovery would
# silently fall through to PATH.
#
# NON-VACUITY, TWO WAYS AT RUN TIME (the cargo-test-selectors leg is the
# static third). Each filter runs through scripts/cargo_test_nonvacuous.sh on
# its own, so a filter that selects zero tests fails the leg (one invocation
# with both filters would pass while either matched nothing). The
# `emit_trust_ir` run then requires each of the four test modules the gap was
# measured on to have PASSED at least one test by name, so a module
# feature-gated or renamed out from under the substring filter is refused
# rather than absorbed by its siblings.
#
# PLACED LAST BUT ONE, AFTER THE AXIOM-AUDIT SOUNDNESS LEG, ON PURPOSE: it
# reaches a trust-cg outside this repo, so a consumer-side red must not mask a
# soundness gate that runs after it (the same argument, and the same
# position, as the axiom-audit leg above). Full mode only: a feature build of
# clean-compiler plus the trust-ir git dependencies.
if [[ $FAST -eq 1 ]]; then
  echo "  TRUST_IR_BACKEND_LIB=SKIPPED reason=fast-mode (a trust-ir-backend feature build; runs in full mode)"
else
  # GATE-FULL-ONLY BEGIN
  # GATE-LEG: trust-ir-backend-lib
  echo "== local gate: trust-ir backend lib tests (emit_trust_ir*, emit_c; --features trust-ir-backend) =="
  # THE FEATURE'S LINT, first: a Clean-side defect needs no trust-cg. The
  # workspace clippy never enables `trust-ir-backend`, so no leg linted this
  # code, and the feature lint was red from emit_trust_ir_link's landing
  # (e0f43ffaf, 2026-09-17) to 2026-10-14 (16 errors in the library, 9 more in
  # the test targets; docs/issues/2026-10-05-trust-ir-backend-feature-clippy-red.md).
  # One run over the four crates that carry the feature, every target.
  _gate_build 17 2 trust-ir-backend-clippy scripts/rust_frontend.sh clippy --locked -p clean-compiler -p clean-native -p clean-cli -p clean \
    --features trust-ir-backend --all-targets -q -- -D warnings \
    || fail "trust-ir-backend-lib (lint) — clippy -D warnings failed under --features trust-ir-backend (clean-compiler, clean-native, clean-cli, clean; every target). The workspace clippy never enables the feature, so no other leg lints this code."
  tir_env=(env)
  tir_cg="${CLEAN_TRUST_CG_BIN:-${TRUSTCG_BIN:-}}"
  if [[ -n "$tir_cg" ]]; then
    [[ -f "$tir_cg" && -x "$tir_cg" ]] \
      || fail "trust-ir-backend-lib — the selected trust-cg '$tir_cg' (CLEAN_TRUST_CG_BIN / TRUSTCG_BIN) is not an executable file; the native e2e tests would silently fall through to whatever trust-cg is on PATH"
    # ABSOLUTE before forwarding: cargo runs the test binary with cwd = the
    # package root, so a path that resolved from HERE would not resolve THERE
    # (measured in the WS6.0 review; find_trust_cg now refuses that instead of
    # falling through to PATH, and this keeps a relative selection working).
    tir_cg="$(cd "$(dirname "$tir_cg")" && pwd -P)/$(basename "$tir_cg")"
    tir_env+=(CLEAN_TRUST_CG_BIN="$tir_cg")
    tir_consumer="$tir_cg (selected)"
  elif [[ -f ../trust-cg/target/debug/trust-cg ]]; then
    tir_consumer="../trust-cg/target/debug/trust-cg (sibling build)"
  elif [[ -f ../trust-cg/target/release/trust-cg ]]; then
    tir_consumer="../trust-cg/target/release/trust-cg (sibling build)"
  else
    tir_consumer="$(command -v trust-cg || echo 'NONE -- the native e2e tests will skip')"
    tir_consumer="$tir_consumer (PATH; select another with TRUSTCG_BIN=<trust-cg>)"
  fi
  echo "  native e2e consumer: $tir_consumer"
  tir_log="$(mktemp "${TMPDIR:-/tmp}/gate-trust-ir-backend-lib.XXXXXX")"
  if ! _gate_build 12 2 trust-ir-backend-lib scripts/cargo_test_nonvacuous.sh trust-ir-backend-lib -- \
      "${tir_env[@]}" targo --unverified test -p clean-compiler --locked --features trust-ir-backend \
      --lib -- emit_trust_ir >"$tir_log" 2>&1; then
    grep -vE '^test .* \.\.\. ok$' "$tir_log" | tail -200 >&2
    rm -f "$tir_log"
    fail "trust-ir-backend-lib (emit_trust_ir) — a trust-ir backend test failed, or the filter selected zero tests (crates/clean-compiler/src/emit_trust_ir*_tests.rs, --features trust-ir-backend). These tests are compiled and run by no other leg. If every failure reads \`unsupported version\`, the consumer named above predates the wire version clean emits (F-119): select a current one with TRUSTCG_BIN=<trust-cg>."
  fi
  grep -E '^(test result:|\[trust-ir-backend-lib\])' "$tir_log"
  for tir_mod in emit_trust_ir::tests:: emit_trust_ir::identity_tests:: \
                 emit_trust_ir_tv::tests:: emit_trust_ir_link::tests::; do
    tir_n="$(grep -cE "^test ${tir_mod}[A-Za-z0-9_:]+ \.\.\. ok$" "$tir_log" || true)"
    echo "  ${tir_mod} ${tir_n} passed"
    if [[ "$tir_n" -eq 0 ]]; then
      rm -f "$tir_log"
      fail "trust-ir-backend-lib — module ${tir_mod} passed ZERO tests under the \`emit_trust_ir\` filter: it was renamed, moved or feature-gated out, and its siblings' results would otherwise have absorbed that silently"
    fi
  done
  rm -f "$tir_log"
  # The same consumer selection applies here: the `emit_c` substring also
  # selects emit_trust_ir::tests::test_emit_trust_ir_differential_matches_emit_c,
  # a native e2e test (measured: 107 selected, 106 of them C-backend tests).
  _gate_build 12 2 trust-ir-backend-lib scripts/cargo_test_nonvacuous.sh trust-ir-backend-lib -- \
    "${tir_env[@]}" targo --unverified test -p clean-compiler --locked --features trust-ir-backend \
    --lib -q -- emit_c \
    || fail "trust-ir-backend-lib (emit_c) — a C-backend test failed under --features trust-ir-backend, or the filter selected zero tests. The filter also selects the emit_trust_ir-vs-emit_c differential, a native e2e test: an \`unsupported version\` failure there is the consumer named above (F-119), not the C backend."
  # WS6.14 (F-109 keep-ratchet): the census LINK oracle over the proof
  # program's 20-root battery lives in clean-native, beside the native_build
  # prelude shim tables it checks, and is behind the same feature -- so it too
  # was run by no leg. No trust-cg is needed: the link is cc against Clean's
  # runtime + the shim TU. Its opt-in trust-cg arm follows the census leg's
  # CLEAN_TRUSTCG_CENSUS=1 switch and the consumer selected above.
  _gate_build 12 2 trust-ir-backend-lib scripts/cargo_test_nonvacuous.sh trust-ir-backend-lib -- \
    "${tir_env[@]}" targo --unverified test -p clean-native --locked --features trust-ir-backend \
    --lib -q -- compile::battery_census_tests:: \
    || fail "trust-ir-backend-lib (battery census) — the F-108/F-109 keep-ratchets over the proof-program battery failed, or the filter selected zero tests (crates/clean-native/src/compile_battery_census_tests.rs, --features trust-ir-backend). An undefined \`l_*\` symbol named here is a prelude shim the emitter now demands and native_build no longer defines."
  # LX0 (designs/2026-09-30-clean-trust-unified-vision.md §5): the experimental
  # `clean run --backend trust-cg` lane's unit tests (licensing, link checks,
  # receipts), behind the same feature and otherwise run by no leg.
  _gate_build 12 2 trust-ir-backend-lib scripts/cargo_test_nonvacuous.sh trust-ir-backend-lib -- \
    "${tir_env[@]}" targo --unverified test -p clean-native --locked --features trust-ir-backend \
    --lib -q -- native_trustcg \
    || fail "trust-ir-backend-lib (native_trustcg) — the experimental trust-cg lane's unit tests failed, or the filter selected zero tests (crates/clean-native/src/native_trustcg_tests.rs, --features trust-ir-backend)."
  # R15 (docs/DECISIONS.md): Clean's program environment, pinned against
  # pinned Lean v4.30.0-rc2 through the compile path's production entry. It
  # needs no feature; it runs here because this leg already builds
  # clean-native's lib tests and no other leg runs them.
  _gate_build 12 2 trust-ir-backend-lib scripts/cargo_test_nonvacuous.sh trust-ir-backend-lib -- \
    "${tir_env[@]}" targo --unverified test -p clean-native --locked --features trust-ir-backend \
    --lib -q -- compile::program_env_tests:: \
    || fail "trust-ir-backend-lib (program environment) — a verdict of Clean's program environment moved off pinned Lean v4.30.0-rc2, or the filter selected zero tests (crates/clean-native/src/compile_program_env_tests.rs). A failing known-gap pin means the gap closed: move it to the agreeing side and update docs/issues/2026-10-08-program-environment-lean-parity.md."
  # `compiler-implemented-by-and-extern-fail-closed` (docs/DECISIONS.md):
  # `@[implemented_by]` and `@[extern]` through the compile path's production
  # entry (chains, the order refusal, the named refusals) and the monad
  # inlining's hiding of attributed constants. Like the run above they need
  # no feature: they ride this leg's `--features trust-ir-backend` build of
  # clean-native's lib tests because no other leg builds those.
  _gate_build 12 2 trust-ir-backend-lib scripts/cargo_test_nonvacuous.sh trust-ir-backend-lib -- \
    "${tir_env[@]}" targo --unverified test -p clean-native --locked --features trust-ir-backend \
    --lib -q -- compile::implemented_by \
    || fail "trust-ir-backend-lib (compiler attributes) — what the native path compiles for an @[implemented_by] or @[extern] declaration moved, or the filter selected zero tests (crates/clean-native/src/compile_implemented_by_tests.rs, compile_implemented_by_order_tests.rs). Expected outputs come from pinned Lean v4.30.0-rc2 (tests/fixtures/native_exec_battery/expected/attr_*)."
  _gate_build 12 2 trust-ir-backend-lib scripts/cargo_test_nonvacuous.sh trust-ir-backend-lib -- \
    "${tir_env[@]}" targo --unverified test -p clean-native --locked --features trust-ir-backend \
    --lib -q -- native_monad_inline:: \
    || fail "trust-ir-backend-lib (monad inlining) — the monad-instance inlining's unit tests failed, or the filter selected zero tests (crates/clean-native/src/native_monad_inline.rs). It must never unfold a constant that carries @[implemented_by] or @[extern]."
  # The ORDER refusal at clean-compiler's public lowering entries
  # (`constant_to_decl`, `expr_to_code`, `compile_lcnf_decls`; Trust's island
  # lane calls the first) and at the Rust ABI, over the record clean-elab
  # writes for a real late `attribute [implemented_by]` source. An integration
  # test so it links one copy of clean-compiler; the Rust ABI half needs the
  # feature.
  _gate_build 12 2 trust-ir-backend-lib scripts/cargo_test_nonvacuous.sh trust-ir-backend-lib -- \
    "${tir_env[@]}" targo --unverified test -p clean-compiler --locked --features trust-ir-backend \
    --test implemented_by_order -q \
    || fail "trust-ir-backend-lib (implemented_by order) — a clean-compiler lowering entry or the Rust ABI compiled code from an environment whose implemented_by order record is not empty, or the test selected zero tests (crates/clean-compiler/tests/implemented_by_order.rs, --features trust-ir-backend). Pinned Lean compiled that code before the binding (tests/fixtures/native_exec_battery/expected/attr_implemented_by_order_noinline.stdout)."
  # The LX0 battery: every native-exec battery program through that lane,
  # against the outcomes pinned in reports/lx0-trustcg-native-battery-2026-09-30.json.
  # The test names its trust-cg explicitly and refuses a PATH fallback, so it
  # runs only when one was selected above; otherwise this says so, loudly.
  if [[ -n "$tir_cg" ]]; then
    _gate_build 12 2 trust-ir-backend-lib scripts/cargo_test_nonvacuous.sh trust-ir-backend-lib -- \
      "${tir_env[@]}" targo --unverified test -p clean --locked --features trust-ir-backend \
      --test native_exec_battery_trustcg -q \
      || fail "trust-ir-backend-lib (LX0 battery) — an outcome moved off reports/lx0-trustcg-native-battery-2026-09-30.json, or the run failed. A move is a RESULT: re-mint with CLEAN_LX0_UPDATE=1 and say why in the commit; a different trust-cg than the report names can move outcomes."
  else
    echo "  LX0_BATTERY=SKIPPED reason=no-trust-cg-selected (select one that accepts --recognize-authority with TRUSTCG_BIN=<trust-cg>)"
  fi
  # WS6.13 (F-119 scout-lean B7/C3, F-118): the packaging smoke on the REAL
  # `clean` binary built the way the atpkg recipe builds it. Its positive arm
  # (`--emit trustir-bin` emits a module `trust-ir validate` accepts) exists
  # only under the feature; the default `-p clean` test leg runs the negative
  # twin (clap refuses the value by name). The archive tests and their
  # mutation control (`ar d runtime_extern.o` -> the link fails by exactly
  # `clean_inc`) are feature-free and ride the `-p clean-native` lib leg.
  _gate_build 12 2 trust-ir-backend-lib scripts/cargo_test_nonvacuous.sh trust-ir-backend-lib -- \
    "${tir_env[@]}" targo --unverified test -p clean --locked --features trust-ir-backend \
    --test trust_ir_backend_packaging \
    || fail "trust-ir-backend-lib (packaging smoke) — the shipped-binary packaging requirement failed, or the test selected zero tests (crates/clean/tests/trust_ir_backend_packaging.rs, --features trust-ir-backend; docs/PACKAGING_TRUST_IR_BACKEND.md). Either \`clean compile --emit trustir-bin\` no longer writes a module \`trust-ir validate\` accepts, \`clean native-runtime\` no longer writes the three-member archive, or \`clean --version\` no longer prints the git sha."
  # GATE-FULL-ONLY END
fi

# GATE-LEG: trustcg-census
#
# THE TRUST-CG LINK+RUN CENSUS, AS A PER-ROW RATCHET (two-language roadmap
# WS6.0). crates/clean-compiler/examples/trustcg_census.rs routes every
# computable prelude root through trust-ir -> trust-cg -> object -> link -> run
# and calls itself "an explicit qualification utility, not a default test";
# nothing gated it. Its only verdict is `assert_eq!(n_ok, total)`, a COUNT.
# This leg compares its TRUSTCG_OUT row by row against the verdicts pinned in
# crates/clean-compiler/examples/trustcg_census.expected.json
# (scripts/check_trustcg_census.py), so a regression -- or an unreviewed change
# of any kind -- is a named root, never a number.
#
# OPT-IN (CLEAN_TRUSTCG_CENSUS=1 plus TRUSTCG_BIN), the same way the
# trust-ir-codegen-ratchet leg is: a release build of clean-compiler plus a
# trust-cg that lives outside this repo. It prints SKIP naming what is unset.
# The comparator's own refusal arms run on every invocation regardless (no
# cargo, well under a second), so its falsifiability is not something checked
# only when somebody opts in. TRUSTCG_LIMIT is stripped: a LIMITED census is
# not a qualification, and the comparator refuses one anyway.
echo "== local gate: trustcg census (comparator selftest; census opt-in) =="
tcc_self="$("$GATE_PYTHON" scripts/check_trustcg_census.py --selftest 2>&1)" \
  || { printf '%s\n' "$tcc_self" >&2; fail "trustcg-census SELFTEST — the census comparator's own refusal arms no longer fire, so a green from it means nothing (scripts/check_trustcg_census.py --selftest)"; }
echo "  ${tcc_self##*$'\n'}"
if [[ "${CLEAN_TRUSTCG_CENSUS:-0}" == "1" && -n "${TRUSTCG_BIN:-}" ]]; then
  tcc_dir="$(mktemp -d "${TMPDIR:-/tmp}/gate-trustcg-census.XXXXXX")"
  tcc_rc=0
  echo "  census consumer: TRUSTCG_BIN=$TRUSTCG_BIN"
  # The subshell keeps bash's own "Abort trap" job notice out of the output:
  # the example writes TRUSTCG_OUT and THEN asserts every row OK, so it exits
  # non-zero whenever the pin carries a non-OK row, and the comparator checks
  # that the exit status agrees with the rows (--census-exit).
  ( _gate_build 47 2 trustcg-census env -u TRUSTCG_LIMIT TRUSTCG_OUT="$tcc_dir/census.tsv" \
      targo --unverified run -p clean-compiler --release --locked --features trust-ir-backend \
      --example trustcg_census >"$tcc_dir/census.log" 2>&1 ) 2>/dev/null || tcc_rc=$?
  sed -n '/TRUST-CG LINK+RUN CENSUS/,/^TV status/p' "$tcc_dir/census.log" | sed 's/^/  /'
  echo "  census exit=$tcc_rc"
  "$GATE_PYTHON" scripts/check_trustcg_census.py "$tcc_dir/census.tsv" --census-exit "$tcc_rc" \
    || { tail -40 "$tcc_dir/census.log" >&2; rm -rf "$tcc_dir"; fail "trustcg census — a root's LINK+RUN verdict differs from its pin (named above), or the census output could not be compared (crates/clean-compiler/examples/trustcg_census.expected.json; re-pin a REVIEWED change with scripts/check_trustcg_census.py <tsv> --write-expected '<where measured>')"; }
  rm -rf "$tcc_dir"
else
  tcc_unset=()
  [[ "${CLEAN_TRUSTCG_CENSUS:-0}" == "1" ]] || tcc_unset+=(CLEAN_TRUSTCG_CENSUS=1)
  [[ -n "${TRUSTCG_BIN:-}" ]] || tcc_unset+=(TRUSTCG_BIN)
  echo "  SKIP: census not run (unset: ${tcc_unset[*]}); set CLEAN_TRUSTCG_CENSUS=1 and TRUSTCG_BIN=<trust-cg>"
fi

# THE FRONTEND MERGE SUITE (roadmap Phase 0, package P0_NET, 2026-09-24).
#
# THE NET OUTSIDE THE SLICE. Measured by the 2026-09-24 process audit
# (reports/lean4-replacement-audit-2026-09-24/process.json): nothing in this
# file, the hook or the suite runner ran the frontend crates' INTEGRATION
# targets or doctests. The first all-targets run after the wave-3 merges found
# three RED targets -- clean-elab structural_recursion_prefix_params,
# clean-parser no_silent_trees, clean-olean prelude_instance_priority_census --
# that run in 0.37 s, 0.06 s and 8.28 s, and cargo's fail-fast had hidden
# every target sorted after the first failure. This leg runs every lib, bin,
# integration and doctest target of clean-parser, clean-olean, clean-macro and
# clean-elab with --no-fail-fast, through scripts/heavy_gate.sh, and refuses on
# any RED target and on any target that was not run. The only exclusion is the
# pinned slow-list (scripts/frontend_merge_suite_slow.txt), whose rows must
# carry a measurement over the budget and are printed as SLOW, never dropped.
#
# The verdict logic's own arms run FIRST, as the trustcg census comparator's
# do, so a green from the suite cannot come from a parser that stopped seeing
# failures. LAST ON PURPOSE: a failure here exits, and placed after every other
# leg it masks none of them. Full mode only -- it is about an hour of cargo
# test (the COST row in scripts/githooks/gate-legs.txt carries the measurement).
if [[ $FAST -eq 1 ]]; then
  echo "  FRONTEND_MERGE_SUITE=SKIPPED reason=fast-mode (every frontend lib/integration/doctest target, about an hour; runs in full mode, or directly: scripts/frontend_merge_suite.sh)"
else
  # GATE-FULL-ONLY BEGIN
  # GATE-LEG: frontend-merge-suite
  echo "== local gate: frontend merge suite (clean-parser, clean-olean, clean-macro, clean-elab; lib + bins + integration + doctests, --no-fail-fast) =="
  fms_self="$(FRONTEND_SUITE_PYTHON="$GATE_PYTHON" scripts/frontend_merge_suite.sh --selftest 2>&1)" \
    || { printf '%s\n' "$fms_self" >&2; fail "frontend-merge-suite SELFTEST — the per-target verdict logic's own refusal arms no longer fire, so a green from the suite would mean nothing (scripts/frontend_merge_suite.sh --selftest names the arm)"; }
  echo "  ${fms_self##*$'\n'}"
  # Build is possibly cold; run/doc retain their real auto classes and any
  # higher completed/partial peak. This scopes a conservative floor, not a cap.
  fms_auto_floor="$(_gate_frontend_auto_floor)" \
    || fail "frontend merge suite — invalid auto reservation floor"
  FRONTEND_SUITE_PYTHON="$GATE_PYTHON" \
    FRONTEND_SUITE_BUILD_GB=47 \
    FRONTEND_SUITE_RUN_GB=auto:frontend-suite-run:47 \
    FRONTEND_SUITE_DOC_GB=auto:frontend-suite-doc:47 \
    HEAVY_GATE_AUTO_FLOOR_GB="$fms_auto_floor" \
    scripts/frontend_merge_suite.sh \
    || fail "frontend merge suite — a frontend target is RED or was never run (the table above names each one; the full cargo output and summary.json are under \$CARGO_TARGET_DIR/frontend-merge-suite, default target/targo-merge-suite). A target that is slow rather than red belongs in scripts/frontend_merge_suite_slow.txt WITH its measurement, never in a name filter."
  # GATE-FULL-ONLY END
fi

report_waived
if (( ${#WAIVED_FAILURES[@]} )); then
  echo "LOCAL GATE: PASS (with ${#WAIVED_FAILURES[@]} waived failure(s) above — nothing here blocks, and every other leg RAN)"
else
  echo "LOCAL GATE: PASS"
fi
