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

# Sorry-bypass lint gate (clean-kernel integration test).
lint-sorry:
    cargo test --locked -p clean-kernel --test lint_sorry_bypass

# Sorry-count census + baseline ratchet (clean-cli subcommand).
# Pass `--update` via ARGS to write a new baseline if the count decreased.
sorry-census ARGS='':
    cargo run --locked -p clean-cli --quiet -- sorry-census {{ARGS}}

# Axiom-audit release-check gate (clean-cli subcommand, Wave 87).
# Runs the two non-mutating lanes (aggregate consistency + live row
# reconciliation) and writes reports/axiom-audit-launch-evidence.json.
axiom-audit-release-check:
    cargo run --locked -p clean-cli --quiet -- mathverse axiom-audit release-check

# ── Lint / Format ──────────────────────────────────────────────────────────

# Clippy gate (workspace-wide deny level from [workspace.lints.clippy]).
clippy:
    cargo clippy --locked --workspace -- -D warnings

# Apply rustfmt to the whole workspace.
fmt:
    cargo fmt --all

# Verify rustfmt is clean (CI gate).
fmt-check:
    cargo fmt --all --check

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

# ── Composite ──────────────────────────────────────────────────────────────

# Quick local check (fmt → clippy → test-lib). The fail-closed soundness gate is `just gate`.
ci: fmt-check clippy test-fast

# Local fail-closed soundness + quality gate (GitHub CI is dead). Run before pushing main.
gate:
    scripts/local_gate.sh

# Fast gate (skips the workspace cargo check); this is what the installed pre-push hook runs.
gate-fast:
    scripts/local_gate.sh --fast

# Install the tracked pre-push hook repo-wide (core.hooksPath; binds all worktrees).
install-hooks:
    git config core.hooksPath scripts/hooks
    @echo "pre-push gate installed: core.hooksPath=scripts/hooks (runs 'just gate-fast' on push)"
