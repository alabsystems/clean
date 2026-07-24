#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

# Copyright 2026 Project Maintainers
# Author: Project Maintainer <maintainer@example.invalid>
# Licensed under the Apache License, Version 2.0

set -euo pipefail

repo_root="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
cd "$repo_root"

export CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-1}"

demo_dir="$repo_root/target/public-demo"
build_log="$demo_dir/build.log"
accept_stdout="$demo_dir/accept.stdout"
accept_stderr="$demo_dir/accept.stderr"
reject_stdout="$demo_dir/reject.stdout"
reject_stderr="$demo_dir/reject.stderr"
contract_manifest="$demo_dir/contract.env"
transcript="$demo_dir/transcript.txt"

accept_file="demos/public/kernel_check_success.lean"
reject_file="demos/public/kernel_check_reject_sorry.lean"

mkdir -p "$demo_dir"
: >"$build_log"
: >"$accept_stdout"
: >"$accept_stderr"
: >"$reject_stdout"
: >"$reject_stderr"
: >"$contract_manifest"
: >"$transcript"

fail() {
    echo "result: FAIL" >&2
    echo "reason: $*" >&2
    echo "logs: target/public-demo/" >&2
    exit 1
}

sha256_file() {
    if command -v sha256sum >/dev/null 2>&1; then
        sha256sum "$1" | awk '{print $1}'
    elif command -v shasum >/dev/null 2>&1; then
        shasum -a 256 "$1" | awk '{print $1}'
    else
        fail "no SHA-256 tool available; expected sha256sum or shasum"
    fi
}

env_quote() {
    printf "'%s'" "$(printf '%s' "$1" | sed "s/'/'\\\\''/g")"
}

write_env_line() {
    {
        printf "%s=" "$1"
        env_quote "$2"
        printf "\n"
    } >>"$contract_manifest"
}

tool_version() {
    local tool="$1"
    local output

    if ! command -v "$tool" >/dev/null 2>&1; then
        printf "unavailable"
        return 0
    fi

    if output="$("$tool" --version 2>&1)"; then
        printf "%s" "${output%%$'\n'*}"
    else
        printf "unavailable: %s" "${output%%$'\n'*}"
    fi
}

git_status_short() {
    git status --short 2>/dev/null || printf "unknown"
}

canonical_path() {
    local path="$1"
    if [[ "$path" != /* ]]; then
        path="$repo_root/$path"
    fi

    if command -v python3 >/dev/null 2>&1; then
        python3 -c 'import os, sys; print(os.path.realpath(sys.argv[1]))' "$path"
    else
        local dir
        local base
        dir="$(dirname "$path")"
        base="$(basename "$path")"
        if [[ -d "$dir" ]]; then
            (cd "$dir" && printf "%s/%s\n" "$(pwd -P)" "$base")
        else
            printf "%s\n" "$path"
        fi
    fi
}

write_contract_manifest() {
    : >"$contract_manifest"
    write_env_line command "./scripts/run_public_demo.sh"
    write_env_line git_commit "$(git rev-parse HEAD)"
    write_env_line git_status_short "$(git_status_short)"
    write_env_line build_mode "$build_mode"
    write_env_line clean_public_demo_bin_override "${CLEAN_PUBLIC_DEMO_BIN:-}"
    write_env_line clean_public_demo_skip_build "${CLEAN_PUBLIC_DEMO_SKIP_BUILD:-}"
    write_env_line cargo_version "$(tool_version cargo)"
    write_env_line rustc_version "$(tool_version rustc)"
    write_env_line cargo_lock "Cargo.lock"
    write_env_line cargo_lock_sha256 "$(sha256_file Cargo.lock)"
    write_env_line accept_fixture "$accept_file"
    write_env_line accept_fixture_sha256 "$(sha256_file "$accept_file")"
    write_env_line accept_expected "Checked 4 declarations; 4 passed, 0 failed"
    write_env_line reject_fixture "$reject_file"
    write_env_line reject_fixture_sha256 "$(sha256_file "$reject_file")"
    write_env_line reject_expected "explicit sorry rejected; sorry axioms: 1"
    write_env_line allow_sorry "0"
    write_env_line reject_deny_sorry "1"
    write_env_line clean_bin "$clean_bin"
    if [[ -x "$clean_bin" ]]; then
        write_env_line clean_bin_sha256 "$(sha256_file "$clean_bin")"
    else
        write_env_line clean_bin_sha256 ""
    fi
}

target_dir="${CARGO_TARGET_DIR:-$repo_root/target}"
if [[ "$target_dir" != /* ]]; then
    target_dir="$repo_root/$target_dir"
fi

build_mode="cargo-build"
build_status="ok"
if [[ "${CLEAN_PUBLIC_DEMO_SKIP_BUILD:-0}" == "1" ]]; then
    build_mode="skip-build"
    build_status="skipped"
fi

if [[ -n "${CLEAN_PUBLIC_DEMO_BIN:-}" ]]; then
    clean_bin="$(canonical_path "$CLEAN_PUBLIC_DEMO_BIN")"
elif [[ -n "${CARGO_BUILD_TARGET:-}" ]]; then
    clean_bin="$(canonical_path "$target_dir/$CARGO_BUILD_TARGET/debug/clean")"
else
    clean_bin="$(canonical_path "$target_dir/debug/clean")"
fi

write_contract_manifest

if [[ "$build_mode" == "cargo-build" ]]; then
    cargo build --quiet --locked --message-format=short -j "$CARGO_BUILD_JOBS" -p clean --bin clean >"$build_log" 2>&1 ||
        fail "cargo build failed; see target/public-demo/build.log"
else
    printf "build skipped via CLEAN_PUBLIC_DEMO_SKIP_BUILD=1\n" >"$build_log"
fi

[[ -x "$clean_bin" ]] || fail "clean binary is not executable: $clean_bin"
write_contract_manifest

"$clean_bin" check "$accept_file" >"$accept_stdout" 2>"$accept_stderr" ||
    fail "accepted demo file failed to check"

grep -F "Checked 4 declarations" "$accept_stdout" >/dev/null ||
    fail "accepted demo output did not report 4 declarations"
grep -F "  4 passed, 0 failed" "$accept_stdout" >/dev/null ||
    fail "accepted demo output did not report 4 passed, 0 failed"
if grep -F "Trust summary:" "$accept_stdout" >/dev/null; then
    fail "accepted demo unexpectedly reported trust debt"
fi

if "$clean_bin" check "$reject_file" >"$reject_stdout" 2>"$reject_stderr"; then
    fail "sorry rejection fixture unexpectedly passed"
fi

grep -F "warning: declaration 'demoRejectSorry' uses explicit sorry" "$reject_stdout" >/dev/null ||
    fail "rejection output did not report explicit sorry"
grep -F "  0 passed, 1 failed" "$reject_stdout" >/dev/null ||
    fail "rejection output did not report 0 passed, 1 failed"
grep -F "Trust summary:" "$reject_stdout" >/dev/null ||
    fail "rejection output did not include a trust summary"
grep -F "  sorry axioms: 1" "$reject_stdout" >/dev/null ||
    fail "rejection output did not count one sorry axiom"
grep -F "demoRejectSorry: declaration uses explicit sorry" "$reject_stdout" >/dev/null ||
    fail "rejection output did not classify explicit sorry as the error"

cat >"$transcript" <<EOF
Clean public demo
command: ./scripts/run_public_demo.sh
build: $build_status
accept: demos/public/kernel_check_success.lean
  expected: Checked 4 declarations; 4 passed, 0 failed
  observed: ok
trust-reject: demos/public/kernel_check_reject_sorry.lean
  expected: explicit sorry rejected
  observed: rejected with sorry axioms: 1
evidence: target/public-demo/contract.env
result: PASS
EOF
cat "$transcript"
