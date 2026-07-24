#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

set -euo pipefail

usage() {
    cat <<'USAGE'
Usage: ./scripts/run_public_benchmarks.sh [OPTIONS]

Run the public benchmark suite and update publication metadata.

This runner does not have a dry-run, list, or check-only mode. Use --help to
inspect the contract, or run `python3 scripts/check_benchmark_publication.py
--check` to validate existing metadata without producing artifacts.

Options:
  --run-id RUN_ID          Publication run directory name.
  --root DIR               Repository root to run from.
  --publication-root DIR   Root directory for benchmark publication metadata.
  --fresh-days DAYS        Freshness window to publish, default 14.
  --force                  Replace the selected run directory if it exists.
  -h, --help               Show this help text.

Environment:
  CLEAN_PUBLIC_BENCHMARK_RUN_ID              Default run id.
  CLEAN_PUBLIC_BENCHMARK_ROOT                Default repository root.
  CLEAN_PUBLIC_BENCHMARK_PUBLICATION_ROOT    Default publication root.
  CLEAN_PUBLIC_BENCHMARK_ALLOW_DIRTY=1       Skip the preflight dirty-check.
  CARGO_BUILD_JOBS                           Cargo build job bound, default 1.

Artifact output:
  reports/benchmarks/publication/<run-id>/run_context.json
  reports/benchmarks/publication/<run-id>/raw/kernel_bench.stdout.txt
  reports/benchmarks/publication/<run-id>/raw/cert_macro_bench.stdout.txt
  reports/benchmarks/publication/<run-id>/raw/server_ops.stdout.txt
  reports/benchmarks/publication/<run-id>/logs/kernel_bench.stderr.log
  reports/benchmarks/publication/<run-id>/logs/cert_macro_bench.stderr.log
  reports/benchmarks/publication/<run-id>/logs/server_ops.stderr.log
  reports/benchmarks/publication/<run-id>/raw/criterion/kernel_bench
  reports/benchmarks/publication/<run-id>/raw/criterion/cert_macro_bench
  reports/benchmarks/publication/<run-id>/raw/criterion/server_ops

Benchmark commands:
  cargo bench --locked --message-format=short -j 1 --package clean-kernel --bench kernel_bench -- --output-format bencher
  cargo bench --locked --message-format=short -j 1 --package clean-kernel --bench cert_macro_bench -- --output-format bencher
  cargo bench --locked --message-format=short -j 1 --package clean-server --bench server_ops -- --output-format bencher
USAGE
}

require_option_value() {
    local option="$1"
    local value="${2-}"

    if [[ -z "$value" || "$value" == --* ]]; then
        echo "error: $option requires a value" >&2
        exit 2
    fi
}

absolute_existing_dir() {
    local label="$1"
    local path="$2"

    if [[ ! -d "$path" ]]; then
        echo "error: $label is not a directory: $path" >&2
        exit 2
    fi

    cd "$path"
    pwd -P
}

absolute_path_from() {
    local base="$1"
    local path="$2"

    if [[ "$path" == /* ]]; then
        printf '%s\n' "$path"
    else
        printf '%s/%s\n' "$base" "$path"
    fi
}

validate_run_id() {
    local value="$1"

    if [[ -z "$value" || "$value" == /* || "$value" == *"/"* || "$value" == *"\\"* || "$value" == *".."* ]]; then
        echo "error: --run-id must be a non-empty safe slug without path separators or traversal" >&2
        exit 2
    fi
    if [[ ! "$value" =~ ^[A-Za-z0-9][A-Za-z0-9._-]{0,127}$ ]]; then
        echo "error: --run-id must use only ASCII letters, digits, dot, underscore, and dash" >&2
        exit 2
    fi
}

dir_has_entries() {
    local path="$1"

    [[ -d "$path" ]] && [[ -n "$(find "$path" -mindepth 1 -maxdepth 1 -print -quit)" ]]
}

assert_run_dir_inside_publication_root() {
    local path="$1"
    local parent
    local name
    local resolved_parent
    local resolved_path

    parent="$(dirname "$path")"
    name="$(basename "$path")"
    if [[ ! -d "$parent" ]]; then
        echo "error: selected run directory parent does not exist: $parent" >&2
        exit 2
    fi

    resolved_parent="$(cd "$parent" && pwd -P)"
    resolved_path="$resolved_parent/$name"
    case "$resolved_path/" in
    "$publication_root"/*) ;;
    *)
        echo "error: refusing to remove run directory outside publication root: $resolved_path" >&2
        exit 2
        ;;
    esac

    if [[ "$resolved_path" == "$publication_root" ]]; then
        echo "error: refusing to remove publication root as a run directory" >&2
        exit 2
    fi

    printf '%s\n' "$resolved_path"
}

run_benchmark() {
    local package="$1"
    local target="$2"
    local criterion_home="$out/raw/criterion/$target"
    local stderr_log="$out/logs/$target.stderr.log"

    mkdir -p "$criterion_home"
    CRITERION_HOME="$criterion_home" \
        cargo bench --locked --message-format=short -j "$CARGO_BUILD_JOBS" --package "$package" --bench "$target" -- --output-format bencher \
        >"$out/raw/$target.stdout.txt" \
        2>"$stderr_log"
}

start_dir="$(pwd -P)"
run_id="${CLEAN_PUBLIC_BENCHMARK_RUN_ID:-}"
root_arg="${CLEAN_PUBLIC_BENCHMARK_ROOT:-}"
publication_root_arg="${CLEAN_PUBLIC_BENCHMARK_PUBLICATION_ROOT:-}"
fresh_days="14"
force=0
export CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-1}"

while [[ $# -gt 0 ]]; do
    case "$1" in
    --run-id)
        require_option_value "$1" "${2-}"
        run_id="$2"
        shift 2
        ;;
    --run-id=*)
        run_id="${1#*=}"
        require_option_value "--run-id" "$run_id"
        shift
        ;;
    --root)
        require_option_value "$1" "${2-}"
        root_arg="$2"
        shift 2
        ;;
    --root=*)
        root_arg="${1#*=}"
        require_option_value "--root" "$root_arg"
        shift
        ;;
    --publication-root)
        require_option_value "$1" "${2-}"
        publication_root_arg="$2"
        shift 2
        ;;
    --publication-root=*)
        publication_root_arg="${1#*=}"
        require_option_value "--publication-root" "$publication_root_arg"
        shift
        ;;
    --fresh-days)
        require_option_value "$1" "${2-}"
        fresh_days="$2"
        shift 2
        ;;
    --fresh-days=*)
        fresh_days="${1#*=}"
        require_option_value "--fresh-days" "$fresh_days"
        shift
        ;;
    --force)
        force=1
        shift
        ;;
    -h | --help)
        usage
        exit 0
        ;;
    *)
        echo "error: unknown option: $1" >&2
        exit 2
        ;;
    esac
done

if [[ ! "$fresh_days" =~ ^[0-9]+$ ]]; then
    echo "error: --fresh-days must be a non-negative integer" >&2
    exit 2
fi

if [[ -n "$root_arg" ]]; then
    root_arg="$(absolute_path_from "$start_dir" "$root_arg")"
    repo_root="$(absolute_existing_dir "--root" "$root_arg")"
else
    repo_root="$(git rev-parse --show-toplevel 2>/dev/null || pwd -P)"
    repo_root="$(absolute_existing_dir "repository root" "$repo_root")"
fi
cd "$repo_root"

if [[ "${CLEAN_PUBLIC_BENCHMARK_ALLOW_DIRTY:-0}" != "1" ]]; then
    if [[ -n "$(git status --porcelain=v1)" ]]; then
        echo "error: public benchmarks must start from a clean checkout" >&2
        echo "       set CLEAN_PUBLIC_BENCHMARK_ALLOW_DIRTY=1 only for local experiments" >&2
        exit 2
    fi
fi

if [[ -z "$run_id" ]]; then
    run_id="$(date -u +%Y-%m-%d)-$(git rev-parse --short HEAD)"
fi
validate_run_id "$run_id"

if [[ -n "$publication_root_arg" ]]; then
    publication_root_arg="$(absolute_path_from "$start_dir" "$publication_root_arg")"
else
    publication_root_arg="$repo_root/reports/benchmarks/publication"
fi
mkdir -p "$publication_root_arg"
publication_root="$(cd "$publication_root_arg" && pwd -P)"
out="$publication_root/$run_id"

if [[ -L "$out" ]]; then
    echo "error: run output path must not be a symlink: $out" >&2
    exit 2
fi
if [[ -e "$out" && ! -d "$out" ]]; then
    echo "error: run output path exists and is not a directory: $out" >&2
    exit 2
fi

if [[ "$force" == "1" ]]; then
    safe_out="$(assert_run_dir_inside_publication_root "$out")"
elif dir_has_entries "$out"; then
    echo "error: run output directory already exists and is not empty: $out" >&2
    echo "       pass --force to replace only this run directory" >&2
    exit 2
fi

env_tmp="$(mktemp "${TMPDIR:-/tmp}/Clean-public-benchmark-env.XXXXXX")"
cleanup() {
    rm -f "$env_tmp"
}
trap cleanup EXIT

python3 scripts/capture_benchmark_env.py \
    --json \
    --command "public-benchmark-suite-v1" \
    >"$env_tmp"

if [[ "$force" == "1" && -e "$safe_out" ]]; then
    rm -rf "$safe_out"
fi

mkdir -p "$out/raw" "$out/logs"
cp "$env_tmp" "$out/run_context.json"

run_benchmark "clean-kernel" "kernel_bench"
run_benchmark "clean-kernel" "cert_macro_bench"
run_benchmark "clean-server" "server_ops"

python3 scripts/check_benchmark_publication.py \
    --repo-root "$repo_root" \
    --publication-root "$publication_root" \
    --write-current \
    --status published \
    --run-id "$run_id" \
    --fresh-days "$fresh_days" \
    --check

artifact_path="$out"
case "$artifact_path" in
"$repo_root"/*)
    artifact_path="${artifact_path#"$repo_root"/}"
    ;;
esac
echo "public benchmark artifacts: $artifact_path"
