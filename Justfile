# Clean — top-level Justfile
#
# Documented command surface for common developer workflows. Each recipe
# is a thin wrapper around an existing cargo invocation, `.cargo/config.toml`
# alias, or bucket-D shell script (see docs/SCRIPTS_MIGRATION.md). The
# Justfile does not replace those — it makes them discoverable.
#
# Usage:
#   just              # show this menu (alias for `just --list`)
#   just <recipe>     # run a recipe
#
# Conventions:
#   - `--locked` on every cargo invocation (CLAUDE.md house rule)
#   - one-line recipes that dispatch to an existing tool
#   - `@` prefix suppresses the recipe-command echo

set shell := ["bash", "-cu"]

# Default recipe: list available workflows.
default:
    @just --list

# ── Build ──────────────────────────────────────────────────────────────────

# Workspace debug build (all members).
build:
    cargo build --locked --workspace

# Workspace release build (all members).
build-release:
    cargo build --locked --workspace --release

# Quick compile gate over the workspace (no codegen).
check:
    cargo check --locked --workspace

# Strict warning-free check of clean-auto (proxies `cargo check-auto` alias).
check-auto:
    cargo check-auto

# ── Test ───────────────────────────────────────────────────────────────────

# Workspace test (all members; slow — runs everything).
test:
    cargo test --locked --workspace

# Fast test: publish smoke surface only (default-members in Cargo.toml).
test-fast:
    cargo test --locked

# Authority-bearing .olean library lane. The build must resolve the exact
# repository pin, and Prelude integration tests are opted in explicitly so a
# missing Lean installation cannot be reported as a passing skipped test.
# The AC1 cases each materialize a large Init/Std environment; running several
# harness cases concurrently can exceed host memory and kill the evidence
# process before it reports a verdict. Keep this authority lane serial.
test-olean-pinned:
    CLEAN_OLEAN_REQUIRE_PINNED_LEAN=1 CLEAN_OLEAN_PRELUDE_INTEGRATION=1 CLEAN_OLEAN_INTEGRATION=1 CLEAN_AC1_FULL_VALIDATION=1 cargo test --locked -p clean-olean -- --test-threads=1

# Sorry-bypass lint gate (clean-kernel integration test).
lint-sorry:
    cargo test --locked -p clean-kernel --test lint_sorry_bypass

# Sorry-count census + baseline ratchet (clean-cli subcommand).
# Pass `--update` via ARGS to write a new baseline if the count decreased.
sorry-census ARGS='':
    cargo run --locked -p clean-cli --quiet -- sorry-census {{ARGS}}

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
    cargo run --locked -p clean-cli --quiet -- mathverse axiom-audit release-check

# ── Lint / Format ──────────────────────────────────────────────────────────

# Clippy gate (workspace-wide deny level from [workspace.lints.clippy]).
# `--workspace --all-targets` is load-bearing, not decoration: without
# `--workspace` three crates (clean-autoform, clean-ck0, clean-reflect) are not
# compiled at all, and without `--all-targets` the 348 test targets of the 19
# non-default members are never linted. Measured 2026-08-12: 233 s from an empty
# target dir. scripts/check_lint_coverage.py fails closed if either flag is
# dropped here. The driver is `scripts/rust_frontend.sh`, not a bare `cargo`,
# because the pinned `trust` toolchain ships clippy as `targo-tippy` and
# rustfmt as `targo-fmt`; the resolver execs plain `cargo <sub>` everywhere
# else. Same flags, same deny level, either way.
clippy:
    scripts/rust_frontend.sh clippy --locked --workspace --all-targets -- -D warnings

# Lint-coverage invariant (~0.1s): no tracked crate outside the workspace, and
# no gate site that has quietly narrowed its selection.
lint-coverage:
    python3 scripts/check_lint_coverage.py

# Apply rustfmt to the whole workspace.
fmt:
    scripts/rust_frontend.sh fmt --all

# Verify rustfmt is clean (CI gate).
fmt-check:
    scripts/rust_frontend.sh fmt --all --check

# ── Tooling / Codegen ──────────────────────────────────────────────────────

# Regenerate docs/cli/ from the FeatureDescriptor registry.
gen-cli-docs:
    cargo gen-cli-docs

# Run the gamma-crown verifier (15 conjectures through the kernel).
# Pass-through args: e.g. `just verify-gamma-crown --json`.
verify-gamma-crown ARGS='':
    cargo verify-gamma-crown {{ARGS}}

# Foreign-kernel cross-check: export the full clean-verify self-verification
# metatheory and have Lean 4 (pinned v4.30.0-rc2, an INDEPENDENT kernel)
# re-check it. Asserts the invariants (0 lean errors, exactly the 3 foundational
# axioms, 0 skips, 100% coverage, flagships zero-axiom). Heavy + needs an elan
# Lean toolchain, so it is not in `just ci`. See docs/SELF_VERIFICATION_CERTIFICATE.md §4.
self-verify-crosscheck:
    scripts/self_verify_crosscheck.sh

# ── Coverage / Bench ───────────────────────────────────────────────────────

# Code-coverage run (matches docs/COVERAGE.md baseline command).
cov:
    CARGO_TARGET_DIR=/tmp/clean-target-coverage cargo llvm-cov --workspace --lib --summary-only --exclude clean-mathverse --exclude clean-verify

# Workspace benchmarks (release profile, criterion).
bench:
    cargo bench --locked --workspace

# ── Supply chain ───────────────────────────────────────────────────────────

# Security advisory audit (respects .cargo/audit.toml ignores).
audit:
    cargo audit

# License / source / advisory policy gate (deny.toml).
deny:
    cargo deny check

# Unused-dependency scan.
machete:
    cargo machete

# Out-of-date dependency report (advisory, not a gate).
outdated:
    cargo outdated

# Check whether the pinned ay dependency has new upstream commits.
update-ay:
    python3 scripts/check_ay_updates.py

# ── Composite ──────────────────────────────────────────────────────────────

# Quick local check (fmt → lint-coverage → clippy → test-lib). The fail-closed
# soundness gate is `just gate`.
ci: hooks-check fmt-check lint-coverage clippy test-fast

# Local fail-closed soundness + quality gate (GitHub CI is dead). Run before pushing main.
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
install-hooks:
    bash scripts/install-git-hooks.sh

# Fail-closed test of the ENFORCEMENT PATH, not of the tree: is the pre-push hook
# actually installed, executable, and still covering local_gate.sh's fast legs?
# Wired into `just ci` and into scripts/local_gate.sh, because a hook that only
# exists in the tree is exactly the bug this repo shipped until 2026-08-23.
hooks-check:
    bash scripts/install-git-hooks.sh --check
