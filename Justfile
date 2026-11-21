# Clean — top-level Justfile
#
# Documented command surface for common developer workflows. Each recipe
# is a thin wrapper around an existing targo invocation, `.cargo/config.toml`
# alias, or bucket-D shell script (see docs/SCRIPTS_MIGRATION.md). The
# Justfile does not replace those — it makes them discoverable.
#
# The driver is targo (owner directive 2026-09-28: ALab builds with Trust):
# `targo --unverified <verb>` carries no proof claim; `targo trust <verb>` is
# the verified lane.
#
# Usage:
#   just              # show this menu (alias for `just --list`)
#   just <recipe>     # run a recipe
#
# Conventions:
#   - `--locked` on every targo invocation (CLAUDE.md house rule)
#   - one-line recipes that dispatch to an existing tool
#   - `@` prefix suppresses the recipe-command echo

set shell := ["bash", "-cu"]

# One unchanged authority environment for each phase of the pinned .olean lane.
olean_pinned_env := "CLEAN_OLEAN_REQUIRE_PINNED_LEAN=1 CLEAN_OLEAN_PRELUDE_INTEGRATION=1 CLEAN_OLEAN_INTEGRATION=1 CLEAN_AC1_FULL_VALIDATION=1"

# Default recipe: list available workflows.
default:
    @just --list

# ── Build ──────────────────────────────────────────────────────────────────

# Workspace debug build (all members).
build:
    targo --unverified build --locked --workspace

# Workspace release build (all members).
build-release:
    targo --unverified build --locked --workspace --release

# Quick compile gate over the workspace (no codegen).
check:
    targo --unverified check --locked --workspace

# Warning-free check of clean-auto's lib. The `check-auto` alias alone does not
# deny warnings ([workspace.lints] sets the rustc lints to "warn"), so this runs
# the same check through `rustc -- -D warnings` (no RUSTFLAGS assignment).
check-auto:
    targo --unverified rustc --locked --message-format=short -p clean-auto --lib --profile check -- -D warnings

# ── Test ───────────────────────────────────────────────────────────────────

# Workspace test (all members; slow — runs everything).
test:
    targo --unverified test --locked --workspace

# Fast test: publish smoke surface only (default-members in Cargo.toml).
test-fast:
    targo --unverified test --locked

# Reject stale dependency provenance before compiling or running long CI legs.
vendor-manifest-check:
    python3 scripts/gen_vendor_manifest.py --check

# The Clean half of the authority-site census (self-proof plan unit P1): a new
# authority-shaped label or checker root in crates/**/*.rs, a named mint whose
# kernel call left its function, or a first-risk list above its ceiling fails
# until data/authority_sites.json names it. The Trust half reads the sibling
# checkout at a pinned commit and runs in local_gate.sh full mode only.
authority-sites:
    python3 scripts/check_authority_sites.py --selftest
    python3 scripts/check_authority_sites.py --clean-only

# Integer division regression lane: one feature resolution/build for both SMT
# transports, checked definitions, source tactics and actual native execution.
# Admit through build-slot and heavy_gate.sh. This emits no Trust proof claim.
test-int-division:
    targo --unverified test --locked \
        -p clean-auto -p clean-elab -p clean-kernel -p clean-runtime -p clean-native -p clean \
        --features clean-elab/ay-smt --lib \
        --test int_euclidean_notation --test tostring_instances_cli \
        --test int_division_lean_parity -- \
        integer_division \
        checked_euclidean_definitions_compute_without_a_native_fold_or_axioms \
        checked_floor_definitions_match_lean_on_every_sign_pair \
        int_division_and_remainder_match_lean \
        notation_and_explicit_heads_have_distinct_checked_semantics \
        frontend_refuses_swapping_euclidean_and_truncating_results \
        custom_int_division_dictionaries_are_not_replaced_by_builtin_arithmetic \
        test_int_div_by_zero_is_zero test_int_div_normal \
        test_int_mod_by_zero_preserves_dividend test_int_mod_normal \
        test_native_emit_int_div_program_is_refused_not_miscompiled \
        clean_run_executes_euclidean_int_division_and_remainder \
        clean_run_executes_floor_int_division_and_remainder --test-threads=1

# The reduction-bound theorem family (proofs/reduction_bound.lean): the file
# elaborates and is kernel-checked, the headline statements and the definitions
# under them match their pins, every device mode has its witness, and no theorem
# reaches an axiom outside the kernel's foundations. clean-elab is not a default
# member, so `test-fast` does not build this target. About three minutes after a
# warm build; a cold build peaked at 33 GB, so admit it through build-slot and
# heavy_gate.sh. This emits no Trust proof claim.
test-reduction-bound:
    targo --unverified test --locked -p clean-elab --test reduction_bound_all_lengths

# Authority-bearing .olean library lane. The build must resolve the exact
# repository pin, and Prelude integration tests are opted in explicitly so a
# missing Lean installation cannot be reported as a passing skipped test.
# The AC1 cases each materialize a large Init/Std environment; running several
# harness cases concurrently can exceed host memory and kill the evidence
# process before it reports a verdict. Keep this authority lane serial.
# The two expensive SemR admission/audit replays are ignored in debug builds;
# the release target below runs all seven controls and keeps them in this lane.
# The eqsat_rules replay (PKG-U2: trust-cg's e-graph rules over SemR) and the
# eqsat_decide replay (PKG-U6: the procedure that proves a discovered rule) are
# ignored the same way; the last two lines run them, under this lane's own
# profile.
# Check the cheap native census and full library before expensive imports. The
# remaining phases preserve every binary, example build/test, integration and doctest;
# the library is executed once. Integration failures still finish other binaries
# for discovery, but a stale census/library cannot start that long phase.
test-olean-pinned:
    {{olean_pinned_env}} targo --unverified test --locked --profile authority -p clean-olean --test prelude_collision_census -- --nocapture --test-threads=1
    {{olean_pinned_env}} targo --unverified test --locked --profile authority -p clean-olean --lib -- --nocapture --test-threads=1
    {{olean_pinned_env}} targo --unverified build --locked --profile authority -p clean-olean --examples
    {{olean_pinned_env}} targo --unverified test --locked --profile authority --no-fail-fast -p clean-olean --bins --examples -- --nocapture --test-threads=1
    {{olean_pinned_env}} targo --unverified test --locked --profile authority --no-fail-fast -p clean-olean --test '*' -- --nocapture --test-threads=1
    {{olean_pinned_env}} targo --unverified test --locked --profile authority --no-fail-fast -p clean-olean --doc -- --nocapture --test-threads=1
    CLEAN_OLEAN_REQUIRE_PINNED_LEAN=1 targo --unverified test --locked --release -p clean-olean --test semr_reference -- --test-threads=1
    {{olean_pinned_env}} targo --unverified test --locked --profile authority -p clean-olean --test eqsat_rules -- --include-ignored --nocapture --test-threads=1
    {{olean_pinned_env}} targo --unverified test --locked --profile authority -p clean-olean --test eqsat_decide -- --include-ignored --nocapture --test-threads=1

# Sorry-bypass lint gate (clean-kernel integration test).
lint-sorry:
    targo --unverified test --locked -p clean-kernel --test lint_sorry_bypass

# Sorry-count census + baseline ratchet (clean-cli subcommand).
# Pass `--update` via ARGS to write a new baseline if the count decreased.
sorry-census ARGS='':
    targo --unverified run --locked -p clean-cli --quiet -- sorry-census {{ARGS}}

# Aristotle model-guide corpus gate. Static checks are fast and belong in `just
# ci`; the elaboration sweep needs an elan Lean toolchain (pinned v4.30.0-rc2 —
# the corpus does NOT elaborate under the elan default), so it is separate.
# Catches what the manual landing gate cannot see: vacuous `Classical.propDecidable`
# inhabitants of `Decidable`, and undischarged hypotheses (0 axioms != 0 assumptions).
corpus-gate ARGS='--fast':
    python3 scripts/aristotle_corpus_gate.py {{ARGS}}

# Full corpus re-elaboration under the pinned toolchain (heavy; not in `just ci`).
corpus-gate-full:
    python3 scripts/aristotle_corpus_gate.py --jobs 6

# Crystal revalidation SCOPE (in `scripts/local_gate.sh`, ~0.24 s).
# Binds data/crystal_chain_revalidation_*.json to the clean-kernel SOURCE tree
# it was measured at. RED when a CHAINED body's own source file has moved past
# that tree -- the spec module may no longer transcribe the emitted body, and no
# fixture in this repo can tell you. Whole-crate functy.N/enum.N/struct.N/
# @func.N renumbering moves on any crate item with zero instructions changed, so
# it is printed as a ledgered revalidation debt, never failed; `--strict` fails
# on it too. Re-deriving the record itself needs trustc and is
# scripts/crystal_fixture_freshness.py.
crystal-scope ARGS='':
    python3 scripts/crystal_freshness_scope.py {{ARGS}}

# add_decl_* bypass ratchet, MEASURED from crates/**/*.rs (in scripts/local_gate.sh,
# ~3.4 s). CLAUDE.md's "add_decl_structural / add_decl_unchecked ... only goes
# down" rule had no source scanner until 2026-08-22: the two gates that read
# data/unchecked_decl_ratchet.json only ever checked it against itself. Pass
# --selftest for the 16 mutation arms (13/14 keep the 2026-08-22 snapshot.rs plant
# as a standing demonstration on the real file), --list to see the measured sites.
add-decl-ratchet ARGS='':
    python3 scripts/check_add_decl_ratchet.py {{ARGS}}

# The self-tests of this repo's own gate/tooling scripts (scripts/test_*), as one
# gate (~21 s; in `scripts/local_gate.sh` full mode). Twenty suites with zero
# callers until 2026-08-22; two were red and nothing said so. Known reds are
# ledgered with an expiry in data/script_selftest_quarantine.json, which fails
# closed on an expired, stale or malformed row.
script-selftests ARGS='':
    scripts/check_script_selftests.sh {{ARGS}}

# Axiom-audit release-check gate (clean-cli subcommand, Wave 87).
# Runs the two non-mutating lanes (aggregate consistency + live row
# reconciliation) and writes reports/axiom-audit-launch-evidence.json.
axiom-audit-release-check:
    targo --unverified run --locked -p clean-cli --quiet -- mathverse axiom-audit release-check

# ── Lint / Format ──────────────────────────────────────────────────────────

# Clippy gate (workspace-wide deny level from [workspace.lints.clippy]).
# `--workspace --all-targets` is load-bearing, not decoration: without
# `--workspace` three crates (clean-autoform, clean-ck0, clean-reflect) are not
# compiled at all, and without `--all-targets` the 348 test targets of the 19
# non-default members are never linted. Measured 2026-08-12: 233 s from an empty
# target dir. scripts/check_lint_coverage.py fails closed if either flag is
# dropped here. The driver is `scripts/rust_frontend.sh`, which runs
# `targo tippy` / `targo fmt` with these flags unchanged and has no stock
# fallback.
clippy:
    scripts/rust_frontend.sh clippy --locked --workspace --all-targets -- -D warnings

# Lint-coverage invariant: no tracked crate outside the workspace, no gate site
# that has quietly narrowed its selection, and each standalone crate's tests and
# `-D warnings` clippy RUN by the script itself (the crystal-A2 projector).
lint-coverage:
    python3 scripts/check_lint_coverage.py

# Apply rustfmt to the whole workspace.
fmt:
    scripts/rust_frontend.sh fmt --all

# Verify rustfmt is clean (CI gate).
fmt-check:
    python3 scripts/check_fmt_changed.py --all

# ── Tooling / Codegen ──────────────────────────────────────────────────────

# Regenerate docs/cli/ from the FeatureDescriptor registry.
gen-cli-docs:
    targo --unverified gen-cli-docs

# Run the gamma-crown verifier (15 conjectures through the kernel).
# Pass-through args: e.g. `just verify-gamma-crown --json`.
verify-gamma-crown ARGS='':
    targo --unverified verify-gamma-crown {{ARGS}}

# Foreign-kernel cross-check: export the full clean-verify self-verification
# metatheory and have Lean 4 (pinned v4.30.0-rc2, an INDEPENDENT kernel)
# re-check it. Asserts the invariants (0 lean errors, exactly the 3 foundational
# axioms, 0 skips, 100% coverage, flagships zero-axiom). Heavy + needs an elan
# Lean toolchain, so it is not in `just ci`. See docs/SELF_VERIFICATION_CERTIFICATE.md §4.
self-verify-crosscheck:
    scripts/self_verify_crosscheck.sh

# ── Coverage / Bench ───────────────────────────────────────────────────────

# Code-coverage run (matches docs/COVERAGE.md baseline command). Needs the
# third-party cargo-llvm-cov. The Trust sysroot does ship the coverage runtime
# and tools (measured 2026-09-28: `trustc -Cinstrument-coverage` + its
# llvm-profdata/llvm-cov report a probe), but cargo-llvm-cov re-invokes a
# lane-less `$CARGO test`, and Targo cannot carry a lane into an external
# subcommand -- see the STOCK EXCEPTION line.
# STOCK EXCEPTION (Trust lacks a lane for external cargo subcommands; measured `targo --unverified <ext>` -> "`--unverified` is valid only for a Targo compilation command", and `targo <ext>` re-invoking `$CARGO check` -> "refuses to create an implicitly unverified artifact")
cov:
    CARGO_TARGET_DIR=/tmp/clean-target-coverage cargo llvm-cov --workspace --lib --summary-only --exclude clean-mathverse --exclude clean-verify

# Workspace benchmarks (release profile, criterion).
bench:
    targo --unverified bench --locked --workspace

# ── Supply chain ───────────────────────────────────────────────────────────
# Third-party subcommands (cargo-audit/deny/machete/outdated), dispatched by
# targo exactly as cargo would; none is installed on the migration host.

# Security advisory audit (respects .cargo/audit.toml ignores).
audit:
    targo audit

# License / source / advisory policy gate (deny.toml).
deny:
    targo deny check

# Unused-dependency scan.
machete:
    targo machete

# Out-of-date dependency report (advisory, not a gate).
outdated:
    targo outdated

# Check whether the pinned ay dependency has new upstream commits.
update-ay:
    python3 scripts/check_ay_updates.py

# ── Composite ──────────────────────────────────────────────────────────────

# Full diagnostic: vendor manifest + authority census + fmt + lint coverage +
# workspace clippy + test-fast + the reduction-bound theorem. Run once on merged
# source for a full-CI claim.
# Ordinary source publication qualifies affected checks (CLAUDE.md). Hooks are
# opt-in (R35); fail-closed soundness diagnostics are `just gate`.
ci: vendor-manifest-check authority-sites fmt-check lint-coverage clippy test-fast test-reduction-bound

# Expanded soundness + quality diagnostics; `ci` is the full source diagnostic.
gate:
    scripts/local_gate.sh

# Fast gate: everything EXCEPT the legs inside local_gate.sh's `GATE-FULL-ONLY`
# regions (the ~4 min workspace clippy, workspace fmt, cargo-deny/vet, the KV
# gates, the full clean-kernel --lib suite, the script self-tests, the kernel
# lint ratchet, the green-artifact recheck, and the trust-verify soundness
# ratchet).
#
# It is NOT ~30 s and it is NOT what the pre-push hook runs. Corrected
# 2026-08-25: this comment used to claim both. `--fast` still compiles the
# trusted kernel twice and the CLI once (soundness-cert 410.8 s COLD,
# axiom-audit-consistency 8.0 s, cli-feature-coverage 293.3 s COLD), because
# those legs are excluded from the HOOK, not from this mode. The hook runs a
# curated subset of its own; the split is one reviewed row per leg, with a MODE
# column, in scripts/githooks/gate-legs.txt.
gate-fast:
    scripts/local_gate.sh --fast

# Install the tracked pre-push hook repo-wide (core.hooksPath). Idempotent,
# refuses to take over a foreign hooksPath, migrates a clone configured for the
# pre-2026-08-23 `scripts/hooks` path, and prints the per-worktree rollout split.
# Opt-in, an operator's choice for their own clone: a landing is gated by
# `just ci`, not by this hook (docs/DECISIONS.md R35).
install-hooks:
    bash scripts/install-git-hooks.sh

# Fail-closed test of the ENFORCEMENT PATH, not of the tree: is the pre-push hook
# actually installed, executable, and still covering local_gate.sh's fast legs?
# Run it by hand after `just install-hooks`; nothing runs it for you. It was the
# first dependency of `just ci` until 2026-10-15, when a landing became one
# `just ci` run and the hook stopped gating landings (docs/DECISIONS.md R35):
# it fails closed on a clone without the hook, so there `just ci` could not
# pass. It was a leg of scripts/local_gate.sh until the owner removed it on
# 2026-08-24 (that file records why where the leg sat). The check exists because
# a hook that only exists in the tree is exactly the bug this repo shipped until
# 2026-08-23.
hooks-check:
    bash scripts/install-git-hooks.sh --check

# Q6 candidate evidence only: no independent DDC, production build or genesis claim.
ck0-lineage:
    python3.14 scripts/check_ck0_lineage.py --selftest
    python3.14 scripts/check_ck0_lineage.py --require-stability --runs reports/self-proof-q6-recapture-2026-11-14/captures --production reports/self-proof-q6-recapture-2026-11-14/captures/production.json
    python3.14 scripts/check_ck0_replay_custody.py --runs reports/self-proof-q6-recapture-2026-11-14/captures --source reports/self-proof-q6-recapture-2026-11-14/captures/source.json
    python3.14 scripts/check_ck0_genesis_history.py
