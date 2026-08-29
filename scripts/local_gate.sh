#!/usr/bin/env bash
# Local enforcement gate (roadmap A1, revised 2026-06-10: GitHub CI deleted by
# owner decision — enforcement is local and fail-closed).
#
# Run before pushing main:  scripts/local_gate.sh [--fast]
# Install as a pre-push hook: ln -sf ../../scripts/local_gate.sh .git/hooks/pre-push
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
#      TRUSTCORE_STALENESS=fresh|stale|skipped:<reason>)
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
#      site that dropped --workspace/--all-targets (scripts/check_lint_coverage.py)
#   5. (full mode) workspace LINT (`cargo clippy --locked --workspace
#      --all-targets -- -D warnings`; the former bare `cargo check` obeyed
#      default-members and saw 8 of 27 crates) + NON-VACUOUS KernelVerified gate (re-stamps a
#      pinned OOM-safe slice → KV ratchet + elision subset, scripts/kv_ratchet_gate.sh)
#      + full clean-kernel --lib suite + trusted-kernel lint ratchet (dead_code/
#      unused the workspace allow hides)
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

FAST=0
[[ "${1:-}" == "--fast" ]] && FAST=1
fail() { echo "LOCAL GATE: FAIL — $1" >&2; exit 1; }

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
  || fail "cargo-test selectors — a gate on the enforcement surface runs a \`cargo test\` filter that selects ZERO tests; libtest exits 0 on it, so that gate cannot fail (scripts/check_cargo_test_selectors.py --list)"

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
# under that name. Markdown and JSON only, no cargo, no git: 0.06 s including
# its own 19 arms, which run first for the reason the two legs above do.
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
"$GATE_PYTHON" scripts/check_lint_coverage.py \
  || fail "lint coverage — a tracked crate escaped [workspace] members, or a gate site dropped --workspace/--all-targets (scripts/check_lint_coverage.py)"

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

# GATE-LEG: soundness-cert
echo "== local gate: soundness certificate =="
scripts/cargo_test_nonvacuous.sh soundness-cert -- \
  cargo test -p clean-kernel --lib --locked --features math-overlays -q \
  -- test_soundness_certificate golden_matches_live_axioms tests_false_axiom_prevention soundness_nested_arg \
  || fail "soundness certificate / golden TCB / regression suites"

# GATE-LEG: axiom-audit-consistency
echo "== local gate: axiom-audit <-> cert consistency =="
scripts/cargo_test_nonvacuous.sh axiom-audit-consistency -- \
  cargo test -p clean-kernel --test verify_axiom_audit_integration --locked -q \
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
scripts/cargo_test_nonvacuous.sh prelude-axiom-ratchet -- \
  cargo test -p clean-kernel --lib --locked --features math-overlays -q \
  -- prelude_axiom \
  || fail "default-prelude axiom ratchet — a non-foundational axiom was added to the environment \`clean check\` loads by default, a census count rose, FOUNDATIONAL_AXIOMS was widened, or a Theorem/Definition in that environment now reaches non-foundational debt; see data/prelude_axiom_ratchet.json"

# GATE-LEG: cli-feature-coverage
echo "== local gate: feature coverage =="
cargo test --locked -p clean-cli --test feature_coverage -q \
  || fail "CLI feature coverage"

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
  echo "  SCRIPT_SELFTESTS=SKIPPED reason=fast-mode (21 s; runs in full mode, or directly: scripts/check_script_selftests.sh)"
  echo "  G-AUTO=SKIPPED reason=fast-mode (measured gate runs in full mode, or directly: scripts/tactic_parity/g_auto.sh)"
  echo "  G-SIMP=SKIPPED reason=fast-mode (measured gate runs in full mode, or directly: scripts/tactic_parity/g_simp.sh)"
else
  # GATE-FULL-ONLY BEGIN
  for fam_gate in g_auto g_simp; do
    if scripts/tactic_parity/${fam_gate}.sh; then
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
  scripts/green_artifact_recheck.sh \
    || fail "green-artifact recheck — a checked-in reports/*-green.json no longer reproduces (scripts/green_artifact_recheck.sh)"
  # GATE-FULL-ONLY END
else
  echo "  GREEN_RECHECK=SKIPPED reason=no-prebuilt-binary (cargo build --locked --release -p clean, then rerun)"
fi

# ── THE THREE PROBE BATTERIES ────────────────────────────────────────────────
#
# `scripts/u2_battery.sh` (51 probes over universe/level semantics),
# `scripts/source_frontier_battery.sh` (26 fixtures carrying 33 pinned
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
  echo "  U2_BATTERY=SKIPPED reason=fast-mode (needs target/release/clean; runs in full mode, or directly: scripts/u2_battery.sh)"
  echo "  SOURCE_FRONTIER_BATTERY=SKIPPED reason=fast-mode (needs target/release/clean; runs in full mode, or directly: SRCFRONTIER_REQUIRE_PINNED=1 scripts/source_frontier_battery.sh)"
  echo "  EVERYDAY_BATTERY=SKIPPED reason=fast-mode (a cargo test; runs in full mode, or directly: cargo test --locked -p clean-elab --lib -q -- test_r100_everyday_battery_full)"
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

  # GATE-LEG: u2-battery
  echo "== local gate: U2 universe/level probe battery (51 probes) =="
  [[ -x target/release/clean ]] \
    || fail "U2 battery — REFUSING, not skipping: there is no executable target/release/clean, and a battery that does not run is not a gate. Build it and rerun: cargo build --locked --release -p clean --bin clean"
  _battery_readonly reports/u2-battery.json scripts/u2_battery.sh \
    || fail "U2 universe/level battery — a probe drifted: a PASS-pinned fixture no longer reports its exact declaration count, a MUST_FAIL fixture PASSED (a rung flipped it — re-pin deliberately, with a dated note in the battery), a pinned failure changed SHAPE, or the battery's own inputs are untracked/dirty. The offending fixture and the expected fragment are named above (scripts/u2_battery.sh)"

  # GATE-LEG: source-frontier-battery
  echo "== local gate: Mathlib-source frontier probe battery (26 fixtures) =="
  [[ -x target/release/clean ]] \
    || fail "source-frontier battery — REFUSING, not skipping: there is no executable target/release/clean, and a battery that does not run is not a gate. Build it and rerun: cargo build --locked --release -p clean --bin clean"
  _battery_readonly reports/source-frontier-battery.json \
    env SRCFRONTIER_REQUIRE_PINNED=1 scripts/source_frontier_battery.sh \
    || fail "Mathlib-source frontier battery — a probe drifted in class I (instance search through a def-based alias), class II (dot notation whose target does not resolve) or mask 3 (auto-implicit swallowing an unresolved head): a PASS-pinned fixture no longer reports its exact count, a MUST_FAIL fixture PASSED, a pinned diagnostic fragment changed shape, or (SRCFRONTIER_REQUIRE_PINNED=1) a gate input is untracked/dirty. The offending fixture and fragment are named above (scripts/source_frontier_battery.sh)"

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
    || fail "everyday battery — REFUSING: reports/everyday-battery.json is absent, and the test treats an absent artifact as a PASS (it prints a NOTE and returns), so this leg would measure nothing. Restore it from git, or regenerate it deliberately: CLEAN_EVERYDAY_UPDATE=1 cargo test --locked -p clean-elab --lib -q -- test_r100_everyday_battery_full"
  env -u CLEAN_EVERYDAY_UPDATE \
    scripts/cargo_test_nonvacuous.sh everyday-battery -- \
    cargo test -p clean-elab --lib --locked -q -- test_r100_everyday_battery_full \
    || fail "everyday-language battery — either an R100 LOCKED snippet regressed (the assert names it: those 38 are byte-identical to the 2026-07-20 measurement and may not go backwards) or reports/everyday-battery.json is stale against the live 63-snippet run (a verdict flipped; regenerate with CLEAN_EVERYDAY_UPDATE=1 and commit it, never hand-edit)"
  # GATE-FULL-ONLY END
fi

# Trust-core evidence staleness tripwire. The three trust-core launch-evidence
# artifacts pin the gate logic that minted them (cmd_replacement.rs sha +, for
# kernel-soundness/deny-sorry, the sha256_repo_module_tree digest of every
# non-test .rs under crates/clean-cli/src/cmd_replacement/), so ANY edit there
# silently stales all three — the in-binary validators reject them at read time
# but nothing at push time said so. The script recomputes the IDENTICAL digests
# (byte-identity proven against the Rust-minted pin at 93670bb91) and fails
# loudly on any mismatch. Prints TRUSTCORE_STALENESS=fresh|stale|skipped:<reason>.
# GATE-LEG: trustcore-evidence-staleness
echo "== local gate: trust-core evidence staleness tripwire =="
"$GATE_PYTHON" scripts/check_trustcore_evidence_staleness.py \
  || fail "trust-core evidence staleness — a cmd_replacement/ gate-logic edit outdated the pinned digests in reports/{kernel-soundness,deny-sorry,axiom-audit}-launch-evidence.json; regenerate with a HEAD-built clean binary (clean replacement trust-core-evidence --kernel-soundness / --deny-sorry, clean replacement axiom-audit --verify data/axiom_audit.json --evidence reports/axiom-audit-launch-evidence.json --json) and commit the refreshed artifacts in the SAME change as the gate edit"

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
  # a row nobody runs: this leg replays its 11 refusal arms -- the five
  # verify_prefix refusals (including the body/declaration partition the
  # criterion rests on), the fail-closed indirect-call arm, and the five
  # discharge-core arms (covered / missing-entry / indirect / wider-than-reality
  # refusal / unnamed-residual refusal) -- and validates the committed discharge
  # table parses and names only real targets.
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
        src = open(w, encoding="utf-8", errors="replace").read()
        th = r["theorem"]
        assert (f"def {th} " in src or f"def {th}(" in src or f"{th}:" in src), (name, th, w)
    for k, ent in tgt["escaping_callees"].items():
        # v2: keys are trust-ir callee NAMES (durable), not func_ids (volatile)
        assert isinstance(k, str) and k.strip() and not k.isdigit(), (name, k)
        assert ent["clause"] in ("a", "b"), (name, k)
        if ent["clause"] == "a":
            assert ent.get("model") and ent.get("residual"), (name, k)
        if ent["clause"] == "b":
            th = ent.get("theorem")
            assert th and th in listed, (name, k, th)
# NOTE (audit r1): callee-vs-walk agreement is checked only by the heavy census
# runs against a dump; this leg checks WELL-FORMEDNESS + theorem registration.
print(f"discharge table: {sum(len(t2['escaping_callees']) for t2 in t['targets'].values())} entries across {len(t['targets'])} target(s), well-formed; clause-b theorems source-verified")
PYCHK

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
  # Driven through scripts/rust_frontend.sh since 2026-08-20: the pinned
  # `trust` toolchain has no `cargo-clippy`, so a bare `cargo clippy` exits
  # before linting anything. The resolver picks the frontend the pinned
  # toolchain ships (`targo-tippy` here, plain `cargo clippy` upstream) and
  # passes these flags through untouched.
  #
  # SELFTEST FIRST, same contract as add-decl-ratchet / env-bypass-census /
  # fmt-changed. Since 2026-08-25 this driver RETRIES the Trust
  # ancestor-identity abort class (see its header: the installed stage2 predates
  # its own fix by nine hours), and a retry that is not demonstrated is
  # indistinguishable from a suppression. Three arms, ~3 s: a transient abort
  # that heals goes green and says so; one that never heals REFUSES with the
  # frontend's own status; a real `-D warnings` violation fails on the first
  # attempt and is not retried.
  echo "== local gate: workspace lint (27/27 crates, all targets) =="
  scripts/rust_frontend.sh --selftest \
    || fail "rust_frontend.sh --selftest -- the lint/format driver's retry cannot be shown to refuse a persistent failure, so its green means nothing"
  scripts/rust_frontend.sh clippy --locked --workspace --all-targets -q -- -D warnings \
    || fail "workspace clippy (--workspace --all-targets) — a warning or error outside the default-members inner loop"

  # Format gate. CLAUDE.md has documented `fmt --all --check` as a pre-push leg
  # for months, but NO script ran it, so a fmt-dirty main could and did reach
  # origin (bc0941514, "main was fmt-dirty", three clean-elab files). Same
  # frontend resolver as the clippy leg above. Full mode only: measured 39 s
  # wall, too slow for the <30 s --fast path.
  echo "== local gate: workspace format =="
  scripts/rust_frontend.sh fmt --all --check \
    || fail "workspace rustfmt (--all --check) — run 'just fmt' and commit the result"

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
    cargo deny check \
      || fail "dependency trust boundary (cargo deny check — advisory/license/ban/source violation; see deny.toml + data/dep_boundary_state.json)"
  else
    echo "  SKIP: cargo-deny not installed (install: cargo install cargo-deny --locked)"
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
    if vet_out="$(cargo vet 2>&1)"; then
      vet_line="$(printf '%s\n' "$vet_out" | grep -i 'Vetting Succeeded' || true)"
      echo "  ${vet_line:-$(printf '%s' "$vet_out" | tail -1)}"
      echo "  (informational tracker — monotonic: audited fraction only rises; see data/dep_audit_state.json)"
    else
      # Non-zero vet means a crate is neither audited nor exempted (a NEW unvetted
      # dependency slipped in). Surface it loudly but do NOT fail the gate — this is
      # the warn-mode contract. Refresh the baseline: `cargo vet` then re-run.
      echo "  WARN: cargo vet reported unvetted dependencies (a new dep is neither audited nor exempted)."
      echo "        Refresh the baseline and update data/dep_audit_state.json. NOT failing the gate (soft tracker)."
      printf '%s\n' "$vet_out" | tail -8 | sed 's/^/        /'
    fi
  else
    echo "  SKIP: cargo-vet not installed (install: cargo install cargo-vet --locked)"
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
  scripts/kv_ratchet_gate.sh \
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
  scripts/kv_invariance_gate.sh \
    || fail "kv invariance gate — lazy closure loading is not no-weaker than eager (an independent-parity unit test or the corpus leg failed)"
  KVINV_VERDICT="$(cat "$KVINV_GATE_VERDICT_FILE" 2>/dev/null || echo 'KVINV_GATE=unknown')"
  rm -f "$KVINV_GATE_VERDICT_FILE"; unset KVINV_GATE_VERDICT_FILE

  # Full clean-kernel lib suite (slow, ~30min). The soundness step above runs only
  # a name-filtered SUBSET; the full suite catches the rest — e.g. the env::tests
  # add_inductive duplicate-detection regression that sat red for days
  # (2026-06-13..15, fixed in 97e465e3) precisely because no gate ran the whole
  # suite. Full-mode only; the pre-push hook (`--fast`) deliberately skips it.
  echo "== local gate: full clean-kernel --lib suite (slow) =="
  cargo test -p clean-kernel --lib --locked --features math-overlays -q \
    || fail "clean-kernel --lib suite (full)"

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
  # Full mode only: 21 s measured, over the ~30 s --fast budget.
  echo "== local gate: script self-tests (scripts/test_*) =="
  scripts/check_script_selftests.sh \
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
  # lines, all produced before the artifact is written.
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
    env -u REGEN_BASELINE -u DENY_SORRY KERNEL_SOUNDNESS_EVIDENCE_PATH="$ks_evidence" \
    bash scripts/kernel_soundness_gate.sh \
    || { rm -f "$ks_evidence"; fail "kernel soundness gate — a trust-core soundness lane failed: the differential corpus no longer matches the Lean 4 baseline it was minted against (lane 0), Clean's kernel infers a different type than Lean 4 for a pinned expression (lane 1), or the clean-elab accept/reject corpus no longer splits the way the baseline says (lane 2). The failing lane is named above; reproduce it verbatim with: bash scripts/kernel_soundness_gate.sh"; }
  rm -f "$ks_evidence"

  echo "== local gate: DENY_SORRY clean gate (6 lanes, mints trust-core evidence) =="
  ds_evidence="$(mktemp "${TMPDIR:-/tmp}/gate-deny-sorry-evidence.XXXXXX")"
  _battery_readonly reports/deny-sorry-launch-evidence.json \
    env -u REGEN_BASELINE -u DENY_SORRY -u DENY_SORRY_GATE_CHILD DENY_SORRY_EVIDENCE_PATH="$ds_evidence" \
    bash scripts/deny_sorry_gate.sh \
    || { rm -f "$ds_evidence"; fail "DENY_SORRY clean gate — a curated sorry-free lane is no longer sorry-free, a production add_decl_* bypass is unaccounted/unsanctioned/over its pinned cap in data/unchecked_decl_ratchet.json, or DENY_SORRY=1 no longer blocks sorry-term creation in a subprocess. The failing step is named above; reproduce it verbatim with: bash scripts/deny_sorry_gate.sh"; }
  rm -f "$ds_evidence"

  # Trusted-kernel lint ratchet (audit #6): re-surfaces the dead_code/unused
  # debt the workspace [lints] allow hides in clean-kernel. Last because it
  # `cargo clean -p clean-kernel` (force-warn needs a fresh compile), which
  # would otherwise invalidate the suite's artifacts above. Full-mode only.
  echo "== local gate: trusted-kernel lint ratchet =="
  scripts/kernel_lint_ratchet.sh \
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
    bash scripts/trust_verify_ratchet.sh --soundness \
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

# GATE-LEG: trust-ir-codegen-ratchet
if [[ "${CLEAN_TRUST_IR_BUILD:-0}" == "1" ]]; then
  echo "== local gate: trust-ir codegen ratchet =="
  # `set -e` is on, so capture the status without letting a non-zero exit abort
  # the gate before it can distinguish SKIP (2) from FAIL.
  tib_rc=0
  bash scripts/trust_ir_build.sh || tib_rc=$?
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
    env -u clean_BIN AXIOM_AUDIT_EVIDENCE_PATH="$aa_evidence" \
    bash scripts/axiom_audit_release_check.sh \
    || { rm -f "$aa_evidence"; fail "axiom-audit release check — data/axiom_audit.json has stale aggregates (lane 1), its per-conjecture rows drift from live \`verify_gamma_crown --json\` output (lane 2), or a \`proof_mechanism: constructive\` claim no longer closes over the foundational axioms alone. KNOWN RED AT HEAD on lane-2 row drift ONLY, with 0 domain axioms stored and 0 live — see the axiom_audit_release_check waiver in data/gate_registry.json. The drifting rows are named above; refresh them deliberately with: python3 -m scripts.axiom_audit.reconcile"; }
  rm -f "$aa_evidence"
  # GATE-FULL-ONLY END
fi

echo "LOCAL GATE: PASS"
