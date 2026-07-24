#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# verify_mathlib.sh — Run verify_olean_batch on Mathlib .olean files
# Part of #3133: verify-olean on Mathlib: 7,873 .olean files
#
# Usage:
#   ./scripts/verify_mathlib.sh [OPTIONS]
#
# Options (forwarded to verify_olean_batch):
#   --limit N          Process at most N modules (default: all)
#   --load-only        Only load modules, skip type-checking
#   --parallel N       Type-check with N threads (default: 1)
#   --json             Output structured JSON report to stdout
#   --json-report P    Write comprehensive verification report to file
#   --full-validation  Run full add_decl validation (infer_sort + check_type)
#   --cache-file P     Path to incremental cache file (JSON)
#   --help             Show this help
#
# Environment:
#   MATHLIB_PATH       Override path to Mathlib .olean root
#   LEAN_TOOLCHAIN     Override path to Lean toolchain lib/lean/
#   RUST_LOG           Log level (default: warn)
#
# Examples:
#   # Load-only test (no type-checking, fastest)
#   ./scripts/verify_mathlib.sh --load-only
#
#   # Type-check first 500 modules
#   ./scripts/verify_mathlib.sh --limit 500
#
#   # Full verification with JSON report
#   ./scripts/verify_mathlib.sh --json-report reports/mathlib_verify.json
#
#   # Parallel type-checking with 4 threads
#   ./scripts/verify_mathlib.sh --parallel 4

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

# --- Binary discovery ---------------------------------------------------------

find_binary() {
    local candidates=(
        "$REPO_ROOT/target/user/release/verify_olean_batch"
        "$REPO_ROOT/target/release/verify_olean_batch"
        "$REPO_ROOT/target/user/debug/verify_olean_batch"
        "$REPO_ROOT/target/debug/verify_olean_batch"
    )
    for bin in "${candidates[@]}"; do
        if [[ -x "$bin" ]]; then
            echo "$bin"
            return 0
        fi
    done
    echo "ERROR: verify_olean_batch binary not found." >&2
    echo "  Build with: cargo build --release --message-format=short -j 1 --bin verify_olean_batch" >&2
    return 1
}

# --- Mathlib discovery --------------------------------------------------------

find_mathlib_root() {
    if [[ -n "${MATHLIB_PATH:-}" ]]; then
        if [[ -d "$MATHLIB_PATH" ]]; then
            echo "$MATHLIB_PATH"
            return 0
        fi
        echo "ERROR: MATHLIB_PATH=$MATHLIB_PATH does not exist" >&2
        return 1
    fi

    # Also check the git toplevel (may differ from REPO_ROOT in worktrees)
    local git_root
    git_root="$(git -C "$REPO_ROOT" rev-parse --show-toplevel 2>/dev/null)" || true
    # For worktrees, also check the main working tree
    local main_tree
    main_tree="$(git -C "$REPO_ROOT" worktree list --porcelain 2>/dev/null | head -1 | sed 's/^worktree //')" || true

    local candidates=(
        "$REPO_ROOT/data/raw/mathlib4/.lake/build/lib/lean"
        "$REPO_ROOT/data/raw/mathlib4/.lake/build/lib"
    )
    if [[ -n "${git_root:-}" ]] && [[ "$git_root" != "$REPO_ROOT" ]]; then
        candidates+=(
            "$git_root/data/raw/mathlib4/.lake/build/lib/lean"
            "$git_root/data/raw/mathlib4/.lake/build/lib"
        )
    fi
    if [[ -n "${main_tree:-}" ]] && [[ "$main_tree" != "$REPO_ROOT" ]] && [[ "$main_tree" != "${git_root:-}" ]]; then
        candidates+=(
            "$main_tree/data/raw/mathlib4/.lake/build/lib/lean"
            "$main_tree/data/raw/mathlib4/.lake/build/lib"
        )
    fi
    candidates+=(
        "/tmp/mathlib4/.lake/build/lib/lean"
        "/tmp/mathlib4/.lake/build/lib"
    )
    for dir in "${candidates[@]}"; do
        if [[ -d "$dir" ]] && { [[ -f "$dir/Mathlib.olean" ]] || [[ -d "$dir/Mathlib" ]]; }; then
            echo "$dir"
            return 0
        fi
    done

    echo "ERROR: Mathlib .olean files not found." >&2
    echo "  Set MATHLIB_PATH or place Mathlib under data/raw/mathlib4/" >&2
    echo "  Checked:" >&2
    for dir in "${candidates[@]}"; do
        echo "    $dir" >&2
    done
    return 1
}

find_mathlib_project_root() {
    local mathlib_root="$1"
    local dir="$mathlib_root"
    while [[ "$dir" != "/" ]]; do
        if [[ -f "$dir/lakefile.lean" ]]; then
            echo "$dir"
            return 0
        fi
        dir="$(dirname "$dir")"
    done
    return 1
}

# --- Lean toolchain discovery -------------------------------------------------

find_lean_toolchain() {
    if [[ -n "${LEAN_TOOLCHAIN:-}" ]]; then
        echo "$LEAN_TOOLCHAIN"
        return 0
    fi

    local mathlib_root="$1"
    local project_root
    project_root="$(find_mathlib_project_root "$mathlib_root")" || true

    # Read toolchain version from mathlib project
    local toolchain_version=""
    if [[ -n "$project_root" ]] && [[ -f "$project_root/lean-toolchain" ]]; then
        toolchain_version=$(sed 's|leanprover/lean4:||' "$project_root/lean-toolchain")
    fi

    local elan_dir="$HOME/.elan/toolchains"

    # Try exact match first
    if [[ -n "$toolchain_version" ]]; then
        local exact="$elan_dir/leanprover--lean4---$toolchain_version/lib/lean"
        if [[ -d "$exact" ]]; then
            echo "$exact"
            return 0
        fi
    fi

    # Fall back to latest installed toolchain
    local latest
    latest=$(ls -d "$elan_dir"/leanprover--lean4---v*/lib/lean 2>/dev/null | sort -V | tail -1)
    if [[ -n "${latest:-}" ]]; then
        echo "$latest"
        return 0
    fi

    echo "ERROR: Lean toolchain not found. Install via elan." >&2
    return 1
}

# --- Search path construction -------------------------------------------------

build_search_path_args() {
    local mathlib_root="$1"
    local init_path="$2"
    local args=()

    args+=(--init-path "$init_path")

    local project_root
    project_root="$(find_mathlib_project_root "$mathlib_root")" || true

    if [[ -n "$project_root" ]]; then
        local packages_dir="$project_root/.lake/packages"
        if [[ -d "$packages_dir" ]]; then
            for pkg in "$packages_dir"/*/; do
                for base in "build/lib" "build/lib/lean" ".lake/build/lib" ".lake/build/lib/lean"; do
                    local lib_path="${pkg}${base}"
                    if [[ -d "$lib_path" ]]; then
                        args+=(--init-path "$lib_path")
                    fi
                done
            done
        fi
    fi

    printf '%s\n' "${args[@]}"
}

# --- Main ---------------------------------------------------------------------

main() {
    local binary mathlib_root init_path
    binary="$(find_binary)"
    mathlib_root="$(find_mathlib_root)"
    init_path="$(find_lean_toolchain "$mathlib_root")"

    echo "=== Mathlib .olean Verification ===" >&2
    echo "Binary:       $binary" >&2
    echo "Mathlib root: $mathlib_root" >&2
    echo "Init path:    $init_path" >&2

    local olean_count
    olean_count=$(find "$mathlib_root" -name "*.olean" | wc -l | tr -d ' ')
    echo "Mathlib files: $olean_count .olean" >&2
    echo "" >&2

    # Build search path arguments (one per line, then convert to array)
    local search_args=()
    while IFS= read -r arg; do
        search_args+=("$arg")
    done < <(build_search_path_args "$mathlib_root" "$init_path")

    # Forward remaining CLI arguments to the binary
    RUST_LOG="${RUST_LOG:-warn}" exec "$binary" "$mathlib_root" "${search_args[@]}" "$@"
}

main "$@"
