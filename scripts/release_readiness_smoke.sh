#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

# Copyright 2026 Project Maintainers
# Author: Project Maintainer <maintainer@example.invalid>
# SPDX-License-Identifier: Apache-2.0
#
# Top-level release readiness smoke gate for #3671.
#
# Usage:
#   ./scripts/release_readiness_smoke.sh [--clean-clone-lite] [--launch] [--evidence PATH] [--help]
#
# This is intentionally cheap and deterministic: it verifies that release
# readiness is represented by concrete docs, executable command surfaces, and
# launch-blocking checklist lanes before heavier release commands, networked
# issue review, or artifact-producing benchmark jobs are considered. The
# opt-in clean-clone-lite lane proves the locked Cargo metadata preflight,
# public demo, and benchmark publication checker from a temporary detached
# worktree without running the full release flow.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

failures=0
clean_clone_lite=0
launch_mode=0
evidence_path=""
public_demo_artifacts_dir=""
public_demo_artifacts_copied=0
clean_clone_logs_dir=""
clean_clone_log_index=0
clean_clone_current_log_path=""
last_clean_clone_status_log_path=""
CLEAN_CLONE_TAIL_LINES="${CLEAN_CLONE_TAIL_LINES:-80}"
original_args=("$@")
failure_messages=()
original_command="./scripts/release_readiness_smoke.sh"
if [[ "${#original_args[@]}" -gt 0 ]]; then
    original_command="$original_command ${original_args[*]}"
fi
command_evidence=("$original_command")

usage() {
    cat <<'EOF'
Usage: ./scripts/release_readiness_smoke.sh [--clean-clone-lite] [--launch] [--evidence PATH] [--help]

Runs the cheap local release-readiness contract gate for #3671.
It checks that launch-blocking release lanes are documented with concrete
commands and that the local script/doc surfaces they depend on exist.

Options:
  --clean-clone-lite  Also create a temporary detached git worktree at HEAD,
                      run cargo metadata --locked --no-deps --format-version 1,
                      ./scripts/run_public_demo.sh, and
                      python3 scripts/check_benchmark_publication.py --check
                      there, then verify git status --short remains empty.
                      These cover the locked Cargo metadata preflight, the
                      public demo command, and benchmark publication checker.
  --launch            Require release-grade benchmark publication evidence for
                      public performance claims. This runs
                      python3 scripts/check_benchmark_publication.py --check --launch
                      and fails pending-publication metadata.
  --evidence PATH     Write machine-readable JSON smoke evidence to PATH.
                      The artifact records commit, git status, commands,
                      failure messages, and the final smoke status.
                      With --clean-clone-lite, command logs are preserved at
                      PATH.clean-clone-logs/ and public demo artifacts at
                      PATH.public-demo/.
  -h, --help          Show this help.

Heavy clean-clone builds, Rust factory status JSON/lockfile/gc-log/AY-pin-graph/local-toolchain/remote-update verification,
legacy Python system-health diagnostics, full benchmark
runs, trust-audit cargo lanes, and GitHub issue review remain manual checklist gates
in docs/RELEASE_READINESS.md.
EOF
}

while [[ $# -gt 0 ]]; do
    case "$1" in
    -h | --help)
        usage
        exit 0
        ;;
    --clean-clone-lite)
        clean_clone_lite=1
        ;;
    --launch)
        launch_mode=1
        ;;
    --evidence)
        if [[ $# -lt 2 ]]; then
            printf 'missing value for --evidence\n' >&2
            usage >&2
            exit 2
        fi
        evidence_path="$2"
        shift
        ;;
    *)
        printf 'unknown option: %s\n' "$1" >&2
        usage >&2
        exit 2
        ;;
    esac
    shift
done

validate_evidence_path() {
    local evidence_parent

    if [[ -z "$evidence_path" ]]; then
        return 0
    fi

    evidence_parent="$(dirname "$evidence_path")"
    if [[ ! -d "$evidence_parent" ]]; then
        printf 'ERROR: --evidence parent directory does not exist: %s\n' "$evidence_parent" >&2
        exit 2
    fi
    if [[ -e "$evidence_path" && ! -f "$evidence_path" ]]; then
        printf 'ERROR: --evidence must name a file, got non-file path: %s\n' "$evidence_path" >&2
        exit 2
    fi
}

section() {
    printf '\n--- %s ---\n' "$1"
}

pass() {
    printf 'PASS: %s\n' "$1"
}

fail() {
    printf 'FAIL: %s\n' "$1" >&2
    failure_messages+=("$1")
    failures=$((failures + 1))
}

json_escape() {
    local value="$1"
    value="${value//\\/\\\\}"
    value="${value//\"/\\\"}"
    value="${value//$'\n'/\\n}"
    value="${value//$'\r'/\\r}"
    value="${value//$'\t'/\\t}"
    printf '%s' "$value"
}

write_command_evidence_array() {
    local index

    printf '['
    for index in "${!command_evidence[@]}"; do
        if [[ "$index" -gt 0 ]]; then
            printf ','
        fi
        printf '"%s"' "$(json_escape "${command_evidence[$index]}")"
    done
    printf ']'
}

write_failure_messages_array() {
    local index

    printf '['
    for index in "${!failure_messages[@]}"; do
        if [[ "$index" -gt 0 ]]; then
            printf ','
        fi
        printf '"%s"' "$(json_escape "${failure_messages[$index]}")"
    done
    printf ']'
}

write_evidence() {
    local final_status="$1"
    local release_head
    local current_status

    if [[ -z "$evidence_path" ]]; then
        return 0
    fi

    release_head="$(git rev-parse --verify HEAD 2>/dev/null || printf 'unknown')"
    current_status="$(git status --short 2>/dev/null | sed -n '1,200p;201q' || printf 'unknown')"

    {
        printf '{\n'
        printf '  "issue": "#3671",\n'
        printf '  "script": "./scripts/release_readiness_smoke.sh",\n'
        printf '  "commit": "%s",\n' "$(json_escape "$release_head")"
        printf '  "status": "%s",\n' "$(json_escape "$final_status")"
        printf '  "git_status_short": "%s",\n' "$(json_escape "$current_status")"
        printf '  "public_demo_artifacts_dir": "%s",\n' "$(json_escape "$public_demo_artifacts_dir")"
        printf '  "public_demo_artifacts_copied": %s,\n' "$([[ "$public_demo_artifacts_copied" -eq 1 ]] && printf true || printf false)"
        printf '  "clean_clone_logs_dir": "%s",\n' "$(json_escape "$clean_clone_logs_dir")"
        printf '  "failure_count": %s,\n' "$failures"
        printf '  "commands": '
        write_command_evidence_array
        printf ',\n'
        printf '  "failures": '
        write_failure_messages_array
        printf '\n}\n'
    } >"$evidence_path"
}

validate_evidence_path

require_file() {
    local path="$1"
    if [[ -f "$path" ]]; then
        pass "found $path"
    else
        fail "missing $path"
    fi
}

require_executable() {
    local path="$1"
    require_file "$path"
    if [[ -x "$path" ]]; then
        pass "executable $path"
    else
        fail "not executable: $path"
    fi
}

require_text() {
    local path="$1"
    local pattern="$2"
    if [[ ! -f "$path" ]]; then
        fail "cannot scan missing $path for $pattern"
    elif grep -Fq -- "$pattern" "$path"; then
        pass "$path contains $pattern"
    else
        fail "$path missing $pattern"
    fi
}

require_help() {
    local path="$1"
    local output
    command_evidence+=("$path --help")
    if output="$("$path" --help 2>&1)" && grep -Fq "Usage:" <<<"$output"; then
        pass "$path --help"
    else
        fail "$path --help did not print Usage"
    fi
}

require_python_help() {
    local path="$1"
    local output
    command_evidence+=("python3 $path --help")
    if output="$(python3 "$path" --help 2>&1)" && grep -Fq "usage:" <<<"$output"; then
        pass "python3 $path --help"
    else
        fail "python3 $path --help did not print usage"
    fi
}

first_status_line() {
    local status="$1"
    printf '%s' "${status%%$'\n'*}"
}

cleanup_clean_clone_lite() {
    local checkout_dir="$1"
    local tmpdir="$2"

    if [[ -e "$checkout_dir/.git" ]]; then
        if git -C "$REPO_ROOT" worktree remove --force "$checkout_dir" >/dev/null 2>&1; then
            :
        else
            rm -rf "$checkout_dir"
        fi
    fi
    rm -rf "$tmpdir"
}

preserve_public_demo_artifacts() {
    local checkout_dir="$1"
    local source_dir="$checkout_dir/target/public-demo"

    if [[ -z "$evidence_path" ]]; then
        return 0
    fi

    public_demo_artifacts_dir="${evidence_path}.public-demo"
    if [[ ! -d "$source_dir" ]]; then
        fail "clean checkout public demo artifacts missing at target/public-demo"
        return 0
    fi

    rm -rf "$public_demo_artifacts_dir"
    mkdir -p "$public_demo_artifacts_dir"
    if cp -R "$source_dir"/. "$public_demo_artifacts_dir"/; then
        public_demo_artifacts_copied=1
        pass "preserved public demo artifacts at $public_demo_artifacts_dir"
    else
        fail "cannot preserve public demo artifacts at $public_demo_artifacts_dir"
    fi
}

prepare_clean_clone_logs() {
    if [[ -z "$evidence_path" ]]; then
        return 0
    fi

    clean_clone_logs_dir="${evidence_path}.clean-clone-logs"
    rm -rf "$clean_clone_logs_dir"
    if mkdir -p "$clean_clone_logs_dir"; then
        pass "clean-clone command logs at $clean_clone_logs_dir"
    else
        fail "cannot create clean-clone log directory at $clean_clone_logs_dir"
        clean_clone_logs_dir=""
    fi
}

sanitize_clean_clone_log_label() {
    local value="$1"
    local safe_value

    safe_value="$(printf '%s' "$value" | LC_ALL=C tr -cs 'A-Za-z0-9._-' '-')"
    safe_value="${safe_value#-}"
    safe_value="${safe_value%-}"
    if [[ "${#safe_value}" -gt 80 ]]; then
        safe_value="${safe_value:0:80}"
    fi
    if [[ -z "$safe_value" ]]; then
        safe_value="command"
    fi
    printf '%s' "$safe_value"
}

set_clean_clone_log_path() {
    local command_label="$1"
    local safe_label

    clean_clone_log_index=$((clean_clone_log_index + 1))
    safe_label="$(sanitize_clean_clone_log_label "$command_label")"
    printf -v clean_clone_current_log_path '%s/%02d-%s.log' "$clean_clone_logs_dir" "$clean_clone_log_index" "$safe_label"
}

write_clean_clone_status_log() {
    local checkout_dir="$1"
    local checkout_status="$2"
    local log_path

    last_clean_clone_status_log_path=""
    if [[ -z "$clean_clone_logs_dir" ]]; then
        return 0
    fi

    set_clean_clone_log_path "git status --short"
    log_path="$clean_clone_current_log_path"
    if {
        printf '$ git status --short\n'
        printf 'cwd: %s\n\n' "$checkout_dir"
        printf '%s' "$checkout_status"
        if [[ -n "$checkout_status" ]]; then
            printf '\n'
        fi
        printf '\nexit: 0\n'
    } >"$log_path"; then
        last_clean_clone_status_log_path="$log_path"
    else
        fail "cannot write clean checkout status log: $log_path"
    fi
}

run_clean_checkout_command() {
    local checkout_dir="$1"
    local command_label
    local log_path
    local exit_code
    shift

    command_label="$*"
    command_evidence+=("$command_label")
    log_path=""
    if [[ -n "$clean_clone_logs_dir" ]]; then
        set_clean_clone_log_path "$command_label"
        log_path="$clean_clone_current_log_path"
        if ! {
            printf '$ %s\n' "$command_label"
            printf 'cwd: %s\n\n' "$checkout_dir"
        } >"$log_path"; then
            fail "cannot write clean checkout command log: $log_path"
            log_path=""
        fi
    fi

    if [[ -n "$log_path" ]]; then
        if (cd "$checkout_dir" && "$@") >>"$log_path" 2>&1; then
            exit_code=0
        else
            exit_code=$?
        fi
        printf '\nexit: %s\n' "$exit_code" >>"$log_path" || true
        if [[ "$exit_code" -eq 0 ]]; then
            pass "clean checkout command: $command_label (log: $log_path)"
        else
            printf 'Last %s log lines for failed clean checkout command:\n' "$CLEAN_CLONE_TAIL_LINES" >&2
            tail -n "$CLEAN_CLONE_TAIL_LINES" "$log_path" >&2 || true
            fail "clean checkout command failed: $command_label (exit $exit_code; log: $log_path)"
        fi
    elif (cd "$checkout_dir" && "$@"); then
        pass "clean checkout command: $command_label"
    else
        fail "clean checkout command failed: $command_label"
    fi
}

run_repo_command() {
    command_evidence+=("$*")
    if "$@"; then
        pass "release command: $*"
    else
        fail "release command failed: $*"
    fi
}

run_clean_clone_lite_lane() {
    local release_head
    local tmpdir
    local checkout_dir
    local checkout_status
    local checkout_status_log_path
    local -a benchmark_checker

    section "Clean clone lite"

    if ! release_head="$(git rev-parse --verify HEAD 2>/dev/null)"; then
        fail "cannot resolve HEAD for --clean-clone-lite"
        return 0
    fi

    if ! tmpdir="$(mktemp -d "${TMPDIR:-/tmp}/Clean-clean-clone-lite.XXXXXX")"; then
        fail "cannot create temporary clean-clone-lite directory"
        return 0
    fi
    checkout_dir="$tmpdir/Clean"
    prepare_clean_clone_logs

    if git -C "$REPO_ROOT" worktree add --detach "$checkout_dir" "$release_head"; then
        pass "created clean detached worktree at $release_head"
    else
        fail "cannot create clean detached worktree at $release_head"
        rm -rf "$tmpdir"
        return 0
    fi

    run_clean_checkout_command "$checkout_dir" cargo metadata --locked --no-deps --format-version 1
    run_clean_checkout_command "$checkout_dir" ./scripts/run_public_demo.sh
    benchmark_checker=(python3 scripts/check_benchmark_publication.py --check)
    if [[ "$launch_mode" -eq 1 ]]; then
        benchmark_checker+=(--launch)
    fi
    run_clean_checkout_command "$checkout_dir" "${benchmark_checker[@]}"

    checkout_status_log_path=""
    if ! checkout_status="$(git -C "$checkout_dir" status --short)"; then
        fail "cannot read clean checkout git status"
    elif [[ -n "$checkout_status" ]]; then
        write_clean_clone_status_log "$checkout_dir" "$checkout_status"
        checkout_status_log_path="$last_clean_clone_status_log_path"
        if [[ -n "$checkout_status_log_path" ]]; then
            fail "clean checkout was modified; first status: $(first_status_line "$checkout_status") (log: $checkout_status_log_path)"
        else
            fail "clean checkout was modified; first status: $(first_status_line "$checkout_status")"
        fi
    else
        write_clean_clone_status_log "$checkout_dir" "$checkout_status"
        checkout_status_log_path="$last_clean_clone_status_log_path"
        if [[ -n "$checkout_status_log_path" ]]; then
            pass "clean checkout remained clean (log: $checkout_status_log_path)"
        else
            pass "clean checkout remained clean"
        fi
    fi

    preserve_public_demo_artifacts "$checkout_dir"
    cleanup_clean_clone_lite "$checkout_dir" "$tmpdir"
}

echo "=== Release Readiness Smoke (#3671) ==="

section "Release readiness docs"
require_file "docs/RELEASE_READINESS.md"
require_text "docs/RELEASE_READINESS.md" "#3671"
require_text "docs/RELEASE_READINESS.md" "clean release readiness-smoke"
require_text "docs/RELEASE_READINESS.md" "clean release readiness-smoke --clean-clone-lite"
require_text "docs/RELEASE_READINESS.md" "./scripts/prepare_mathverse_release.sh"
require_text "docs/RELEASE_READINESS.md" "./scripts/run_ay_consumer_smoke.sh"
require_text "docs/RELEASE_READINESS.md" "## Launch Blockers"
require_text "docs/RELEASE_READINESS.md" "## Aggregate Gate Map"
require_text "docs/RELEASE_READINESS.md" "## Clean Clone"
require_text "docs/RELEASE_READINESS.md" "## Build Gate"
require_text "docs/RELEASE_READINESS.md" "## System Health"
require_text "docs/RELEASE_READINESS.md" "## Demo And Consumer Smoke"
require_text "docs/RELEASE_READINESS.md" "## Docs Gate"
require_text "docs/RELEASE_READINESS.md" "## Trust Audit"
require_text "docs/RELEASE_READINESS.md" "## Benchmark Freshness"
require_text "docs/RELEASE_READINESS.md" "## Issue Hygiene"
require_text "docs/RELEASE_READINESS.md" "git clone --no-local"
require_text "docs/RELEASE_READINESS.md" "test -z \"\$(git status --short)\""
require_text "docs/RELEASE_READINESS.md" "cargo metadata --locked --no-deps --format-version 1"
require_text "docs/RELEASE_READINESS.md" "CARGO_BUILD_JOBS=1 cargo build --locked --message-format=short -j 1 --release -p clean --bin clean"
require_text "docs/RELEASE_READINESS.md" "factory status --json"
require_text "docs/RELEASE_READINESS.md" "> /tmp/Clean-system-health.json"
require_text "docs/RELEASE_READINESS.md" "python3 scripts/system_health_check.py --json-output /tmp/Clean-system-health-python-fallback.json"
require_text "docs/RELEASE_READINESS.md" "checks.cargo_lock.status"
require_text "docs/RELEASE_READINESS.md" "checks.git_gc_logs.status"
require_text "docs/RELEASE_READINESS.md" "checks.local_toolchain.status"
require_text "docs/RELEASE_READINESS.md" "checks.ay_path.status"
require_text "docs/RELEASE_READINESS.md" "checks.ay_updates.status"
require_text "docs/RELEASE_READINESS.md" "missing Cargo.lock"
require_text "docs/RELEASE_READINESS.md" ".git/worktrees/*/gc.log"
require_text "docs/RELEASE_READINESS.md" "AY \`refs/heads/main\`"
require_text "docs/RELEASE_READINESS.md" "seven identical AY revisions"
require_text "docs/RELEASE_READINESS.md" "exactly 38 AY Cargo.lock sources"
require_text "docs/RELEASE_READINESS.md" "No sibling AY"
require_text "docs/RELEASE_READINESS.md" "legacy diagnostic output only"
require_text "docs/RELEASE_READINESS.md" "cannot override Rust factory status"
require_text "docs/RELEASE_READINESS.md" "CARGO_BUILD_JOBS=1 cargo test --locked --message-format=short -j 1 -p clean-cli --test docs_drift"
require_text "docs/RELEASE_READINESS.md" "./scripts/run_public_demo.sh"
require_text "docs/RELEASE_READINESS.md" "python3 scripts/sync_readme_metrics.py --check"
require_text "docs/RELEASE_READINESS.md" "python3 scripts/check_benchmark_publication.py --check"
require_text "docs/RELEASE_READINESS.md" "python3 scripts/check_benchmark_publication.py --check --launch"
require_text "docs/RELEASE_READINESS.md" "clean replacement trust-core-evidence --kernel-soundness --evidence reports/kernel-soundness-launch-evidence.json --json"
require_text "docs/RELEASE_READINESS.md" "clean replacement trust-core-evidence --deny-sorry --evidence reports/deny-sorry-launch-evidence.json --json"
require_text "docs/RELEASE_READINESS.md" "clean replacement axiom-audit --verify data/axiom_audit.json --evidence reports/axiom-audit-launch-evidence.json --json"
require_text "docs/RELEASE_READINESS.md" "CLEAN_TRUST_BOUNDARY_AUDIT_PATH=/tmp/Clean-2875-auto.tsv"
require_text "docs/RELEASE_READINESS.md" "CARGO_BUILD_JOBS=1 cargo test --locked --message-format=short -j 1 -p clean-auto --lib"
require_text "docs/RELEASE_READINESS.md" "CLEAN_TRUST_BOUNDARY_AUDIT_PATH=/tmp/Clean-2875-elab.tsv"
require_text "docs/RELEASE_READINESS.md" "CARGO_BUILD_JOBS=1 cargo test --locked --message-format=short -j 1 -p clean-elab --lib --features ay-smt"
require_text "docs/RELEASE_READINESS.md" "python3 scripts/trust_boundary_audit.py"
require_text "docs/RELEASE_READINESS.md" "--input /tmp/Clean-2875-auto.tsv"
require_text "docs/RELEASE_READINESS.md" "--input /tmp/Clean-2875-elab.tsv"
require_text "docs/RELEASE_READINESS.md" "\`data/unchecked_decl_ratchet.json\`"
require_text "docs/RELEASE_READINESS.md" "\`add_decl_structural_count: 1\`"
require_text "docs/RELEASE_READINESS.md" "\`add_decl_unchecked_count: 0\`"
require_text "docs/RELEASE_READINESS.md" "empty legacy \`files\` list"
require_text "docs/RELEASE_READINESS.md" "cargo test -p clean-mathverse verify_incremental --lib"
require_text "docs/RELEASE_READINESS.md" "rg -n \"add_decl_unchecked\" crates/clean-mathverse/src"
require_text "docs/RELEASE_READINESS.md" "which should return no"
require_text "docs/RELEASE_READINESS.md" "proof-status/provenance/spec-filter alignment"
require_text "docs/RELEASE_READINESS.md" "cargo test --locked --message-format=short -j 1 -p clean-verify --test proof_status_invariants --test type_preservation_provenance"
require_text "docs/RELEASE_READINESS.md" "structural 1 / unchecked 0"
require_text "docs/RELEASE_READINESS.md" "readiness remains fail-closed independently of fresh proof output"
require_text "docs/RELEASE_READINESS.md" "./scripts/run_public_benchmarks.sh"
require_text "docs/RELEASE_READINESS.md" "clean release readiness-smoke --clean-clone-lite --launch"
require_text "docs/RELEASE_READINESS.md" "./scripts/bench_regression.sh --compare"
require_text "docs/RELEASE_READINESS.md" "ay_dependency_rev"
require_text "docs/RELEASE_READINESS.md" "ay_lockfile_rev"
require_text "docs/RELEASE_READINESS.md" "ay_lockfile_commit"
require_text "docs/RELEASE_READINESS.md" "ay_remote_rev"
require_text "docs/RELEASE_READINESS.md" "ay_manifest_pin_count"
require_text "docs/RELEASE_READINESS.md" "ay_lock_source_count"
require_text "docs/RELEASE_READINESS.md" "clean replacement release-issue-hygiene --fetch --json"
require_text "docs/RELEASE_READINESS.md" "gh issue list --state open"
require_text "docs/RELEASE_READINESS.md" "Release decision:"
require_text "docs/RELEASE_READINESS.md" "demos/public/kernel_check_success.lean"
require_text "docs/RELEASE_READINESS.md" "demos/public/kernel_check_reject_sorry.lean"
require_text "docs/RELEASE_READINESS.md" "CARGO_BUILD_JOBS=1 cargo run --locked --message-format=short -j 1 -p clean --bin clean -- --help"
require_text "docs/RELEASE_READINESS.md" "clean mathverse download --version <version> --output-dir /tmp/mathverse-dl-test --json"
require_text "docs/RELEASE_READINESS.md" "CARGO_BUILD_JOBS=1 cargo test --locked --message-format=short -j 1 -p clean-cli cmd_mathverse::tests"
require_text "docs/RELEASE_READINESS.md" "mathverse-library-v*.tar.zst"
require_text "docs/RELEASE_READINESS.md" "zero-shard archives"
require_text "docs/RELEASE_READINESS.md" "CARGO_BUILD_JOBS=1 cargo run --locked --message-format=short -j 1 -p clean-mathverse --bin mathverse_shard -- verify data/mathverse-library/"

require_file "docs/MATHVERSE_RELEASE_CHECKLIST.md"
require_text "docs/MATHVERSE_RELEASE_CHECKLIST.md" "clean release readiness-smoke"
require_text "docs/MATHVERSE_RELEASE_CHECKLIST.md" "clean release readiness-smoke --clean-clone-lite --launch"
require_text "docs/MATHVERSE_RELEASE_CHECKLIST.md" "CARGO_BUILD_JOBS=1 cargo test --locked --message-format=short -j 1 -p clean-mathverse --lib"
require_text "docs/MATHVERSE_RELEASE_CHECKLIST.md" "CARGO_BUILD_JOBS=1 cargo run --locked --message-format=short -j 1 -p clean-mathverse --bin mathverse_shard -- verify data/mathverse-library/"
require_file "docs/plans/LEAN4_REPLACEMENT_PLAN.md"
require_file "data/unchecked_decl_ratchet.json"
require_text "data/unchecked_decl_ratchet.json" "\"add_decl_structural_count\": 0"
require_text "data/unchecked_decl_ratchet.json" "\"add_decl_unchecked_count\": 0"

section "Release command surfaces"
require_executable "scripts/release_readiness_smoke.sh"
require_executable "scripts/run_public_demo.sh"
require_executable "scripts/prepare_mathverse_release.sh"
require_executable "scripts/package_mathverse_release.sh"
require_executable "scripts/release_mathverse_shards.sh"
require_executable "scripts/download_mathverse_library.sh"
require_executable "scripts/download_mathverse_shards.sh"
require_executable "scripts/run_ay_consumer_smoke.sh"
require_file "scripts/check_ay_updates.py"
require_text "scripts/run_ay_consumer_smoke.sh" "export CARGO_BUILD_JOBS=\"\${CARGO_BUILD_JOBS:-1}\""
require_text "scripts/run_ay_consumer_smoke.sh" "export PYTEST_DISABLE_PLUGIN_AUTOLOAD=\"\${PYTEST_DISABLE_PLUGIN_AUTOLOAD:-1}\""
require_text "scripts/run_ay_consumer_smoke.sh" "cargo check --locked -p clean-auto --features ay-smt"
require_text "scripts/run_ay_consumer_smoke.sh" "cargo metadata --locked --format-version 1"
require_text "scripts/run_ay_consumer_smoke.sh" "ay_manifest_pin_count"
require_text "scripts/run_ay_consumer_smoke.sh" "ay_lock_source_count"
require_text "scripts/run_ay_consumer_smoke.sh" "--rawfile output"
require_executable "scripts/run_build_regression_gate.sh"
require_executable "scripts/bench_regression.sh"
require_executable "scripts/run_public_benchmarks.sh"
require_file "scripts/trust_boundary_audit.py"
require_file "scripts/sync_readme_metrics.py"
require_file "scripts/check_benchmark_publication.py"
require_file "scripts/release_issue_hygiene.py"
require_file "crates/clean-cli/src/cmd_factory.rs"
require_text "crates/clean-cli/src/cmd_factory.rs" "clean factory status --json"
require_text "crates/clean-cli/src/cmd_factory.rs" "checks.cargo_lock.status"
require_text "crates/clean-cli/src/cmd_factory.rs" "checks.git_gc_logs.status"
require_text "crates/clean-cli/src/cmd_factory.rs" "checks.local_toolchain.status"
require_text "crates/clean-cli/src/cmd_factory.rs" "checks.ay_path.status"
require_text "crates/clean-cli/src/cmd_factory.rs" "checks.ay_updates.status"
require_text "crates/clean-cli/src/cmd_factory.rs" "AY_MANIFEST_KEYS: [&str; 7]"
require_text "crates/clean-cli/src/cmd_factory.rs" "AY_LOCK_SOURCE_COUNT: usize = 38"
require_file "scripts/system_health_check.py"
require_text "scripts/system_health_check.py" "def check_ay_updates()"
require_text "scripts/system_health_check.py" "\"pin_status\""
require_text "scripts/prepare_mathverse_release.sh" "export CARGO_BUILD_JOBS=\"\${CARGO_BUILD_JOBS:-1}\""
require_text "scripts/prepare_mathverse_release.sh" "cargo test --locked -p clean-mathverse --lib --message-format=short -j \"\$CARGO_BUILD_JOBS\""
require_text "scripts/prepare_mathverse_release.sh" "cargo build --locked -p clean-mathverse --release --message-format=short -j \"\$CARGO_BUILD_JOBS\""
require_text "scripts/prepare_mathverse_release.sh" "cargo check --locked -p clean-mathverse --message-format=short -j \"\$CARGO_BUILD_JOBS\""

section "Script help surfaces"
require_help "./scripts/release_readiness_smoke.sh"
require_help "./scripts/prepare_mathverse_release.sh"
require_help "./scripts/package_mathverse_release.sh"
require_help "./scripts/release_mathverse_shards.sh"
require_help "./scripts/download_mathverse_library.sh"
require_help "./scripts/download_mathverse_shards.sh"
require_help "./scripts/run_ay_consumer_smoke.sh"
require_help "./scripts/run_build_regression_gate.sh"
require_help "./scripts/bench_regression.sh"
require_help "./scripts/run_public_benchmarks.sh"
require_python_help "scripts/trust_boundary_audit.py"
require_python_help "scripts/check_benchmark_publication.py"
require_python_help "scripts/release_issue_hygiene.py"

if [[ "$launch_mode" -eq 1 ]]; then
    section "Launch benchmark publication"
    run_repo_command python3 scripts/check_benchmark_publication.py --check --launch
fi

section "Launch evidence docs"
require_file "Cargo.toml"
require_file "README.md"
require_file "CITATION.cff"
require_file "SUPPORT.md"
require_file "docs/BENCHMARKS.md"
require_file "docs/DESIGN.md"
require_file "docs/PUBLIC_DEMO.md"
require_file "docs/VERIFICATION_AUDIT.md"
require_file "demos/public/kernel_check_success.lean"
require_file "demos/public/kernel_check_reject_sorry.lean"
require_text "docs/BENCHMARKS.md" "Last audited:"
require_text "docs/PUBLIC_DEMO.md" "./scripts/run_public_demo.sh"
require_text "docs/PUBLIC_DEMO.md" "demos/public/kernel_check_success.lean"
require_text "docs/PUBLIC_DEMO.md" "demos/public/kernel_check_reject_sorry.lean"
require_text "docs/VERIFICATION_AUDIT.md" "data/axiom_audit.json"
require_text "scripts/run_public_demo.sh" "demos/public/kernel_check_success.lean"
require_text "scripts/run_public_demo.sh" "demos/public/kernel_check_reject_sorry.lean"

if [[ "$clean_clone_lite" -eq 1 ]]; then
    run_clean_clone_lite_lane
fi

if [[ "$failures" -ne 0 ]]; then
    write_evidence "NOT READY"
    echo "=== Release readiness smoke: NOT READY (${failures} failures) ===" >&2
    exit 1
fi

write_evidence "READY"
echo "=== Release readiness smoke: READY ==="
