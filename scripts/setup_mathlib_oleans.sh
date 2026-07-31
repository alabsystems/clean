#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Download Mathlib4 and prepare compiled .olean files for verification.
# Prefers prebuilt caches via `lake exe cache get`, with `lake build` as fallback.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
DATA_DIR="${1:-$REPO_ROOT/data}"
RAW_DIR="$DATA_DIR/raw"
PRIMARY_MATHLIB_DIR="$RAW_DIR/mathlib4"
FALLBACK_MATHLIB_DIR="/tmp/mathlib4"

log() {
    echo "[setup_mathlib_oleans] $*"
}

warn() {
    echo "[setup_mathlib_oleans] WARNING: $*" >&2
}

die() {
    echo "[setup_mathlib_oleans] ERROR: $*" >&2
    exit 1
}

count_oleans_in_dir() {
    local dir="$1"

    if [ ! -d "$dir" ]; then
        echo "0"
        return 0
    fi

    find "$dir" -type f -name '*.olean' | wc -l | tr -d '[:space:]'
}

detect_build_dir() {
    local mathlib_dir="$1"
    local candidate

    # LAKE LAYOUT: current Lake emits oleans under .lake/build/lib/lean/, older
    # versions used .lake/build/lib/. Probe the new path FIRST. Missing it made
    # this script die "build completed without producing usable .olean files"
    # even after a fully successful `lake exe cache get` + `lake build` — the
    # 8,310 oleans were sitting one directory below where it looked.
    # scripts/kv_ratchet_gate.sh:28 and scripts/lib/mathlib_rebuild_lib.sh:42
    # already used the lib/lean path; only this script was stale.
    for candidate in "$mathlib_dir/.lake/build/lib/lean" "$mathlib_dir/.lake/build/lib" "$mathlib_dir/build/lib/lean" "$mathlib_dir/build/lib"; do
        if [ -f "$candidate/Mathlib.olean" ] || [ -d "$candidate/Mathlib" ]; then
            echo "$candidate"
            return 0
        fi
    done

    echo "$mathlib_dir/.lake/build/lib/lean"
}

count_all_oleans() {
    local mathlib_dir="$1"

    if [ ! -d "$mathlib_dir" ]; then
        echo "0"
        return 0
    fi

    find "$mathlib_dir" \
        -path "$mathlib_dir/.git" -prune -o \
        -type f -name '*.olean' -print | wc -l | tr -d '[:space:]'
}

mathlib_is_ready() {
    local mathlib_dir="$1"
    local build_dir
    local build_count

    build_dir="$(detect_build_dir "$mathlib_dir")"
    if [ ! -d "$build_dir" ]; then
        return 1
    fi

    if [ ! -f "$build_dir/Mathlib.olean" ] && [ ! -d "$build_dir/Mathlib" ]; then
        return 1
    fi

    build_count="$(count_oleans_in_dir "$build_dir")"
    [ "$build_count" -gt 0 ]
}

choose_mathlib_dir() {
    if [ -d "$PRIMARY_MATHLIB_DIR" ]; then
        echo "$PRIMARY_MATHLIB_DIR"
        return 0
    fi

    if mkdir -p "$RAW_DIR" 2>/dev/null; then
        echo "$PRIMARY_MATHLIB_DIR"
        return 0
    fi

    warn "Could not create $RAW_DIR; falling back to $FALLBACK_MATHLIB_DIR"
    mkdir -p /tmp
    echo "$FALLBACK_MATHLIB_DIR"
}

ensure_command() {
    local cmd="$1"
    local help="$2"

    if ! command -v "$cmd" >/dev/null 2>&1; then
        die "$cmd is not installed. $help"
    fi
}

ensure_lean_toolchain() {
    if ! command -v lake >/dev/null 2>&1; then
        die "lake is not installed. Install Lean 4 via elan, then rerun this script."
    fi

    if ! command -v elan >/dev/null 2>&1; then
        warn "elan is not installed or not on PATH; continuing because lake is available"
    fi

    if ! command -v lean >/dev/null 2>&1 && ! command -v lean4 >/dev/null 2>&1; then
        warn "lean/lean4 is not on PATH; checking whether lake can resolve the toolchain"
    fi

    if ! (cd "$MATHLIB_DIR" && lake env lean --version >/dev/null 2>&1); then
        die "Lean 4 is not available to lake. Install elan and a Lean 4 toolchain, then rerun."
    fi
}

ensure_checkout() {
    # A DANGLING SYMLINK is the common failure on this layout: data/raw/* are
    # symlinks into /tmp, and /tmp gets cleaned. `[ -d ]` is false for a dangling
    # link, so the old code fell through to `git clone`, which then failed with
    # the opaque "could not create work tree dir: File exists" — the link itself
    # exists. Detect and clear it, and clone through to the link target so the
    # established data/raw/<corpus> -> /tmp/<corpus> layout is preserved.
    if [ -L "$MATHLIB_DIR" ] && [ ! -e "$MATHLIB_DIR" ]; then
        _link_target="$(readlink "$MATHLIB_DIR")"
        log "Dangling symlink $MATHLIB_DIR -> $_link_target (target gone; /tmp cleaned?)"
        if [ -n "$_link_target" ]; then
            log "Cloning into the link target $_link_target so the symlink layout is kept"
            mkdir -p "$(dirname "$_link_target")"
            MATHLIB_DIR="$_link_target"
        else
            rm -f "$MATHLIB_DIR"
        fi
    fi

    if [ -d "$MATHLIB_DIR" ]; then
        if [ -f "$MATHLIB_DIR/lakefile.lean" ] || [ -f "$MATHLIB_DIR/lakefile.toml" ]; then
            log "Mathlib checkout already exists at $MATHLIB_DIR"
            return 0
        fi

        die "$MATHLIB_DIR exists but does not look like a Mathlib checkout"
    fi

    ensure_command "git" "Install git to clone mathlib4."
    mkdir -p "$(dirname "$MATHLIB_DIR")"

    log "Cloning mathlib4 into $MATHLIB_DIR"
    git clone --depth 1 "https://github.com/leanprover-community/mathlib4" "$MATHLIB_DIR"
}

build_mathlib_path() {
    local build_dir="$1"
    local packages_dir="$MATHLIB_DIR/.lake/packages"
    local entry
    local dep_dir
    local result=""
    local entries=()

    entries+=("$build_dir")

    if [ -d "$packages_dir" ]; then
        while IFS= read -r -d '' dep_dir; do
            if [ -d "$dep_dir/build/lib" ]; then
                entries+=("$dep_dir/build/lib")
            fi
            if [ -d "$dep_dir/.lake/build/lib/lean" ]; then
                entries+=("$dep_dir/.lake/build/lib/lean")
            elif [ -d "$dep_dir/.lake/build/lib" ]; then
                entries+=("$dep_dir/.lake/build/lib")
            fi
        done < <(find "$packages_dir" -mindepth 1 -maxdepth 1 -type d -print0)
    fi

    for entry in "${entries[@]}"; do
        if [ ! -d "$entry" ]; then
            continue
        fi

        case ":$result:" in
            *":$entry:"*) ;;
            *)
                if [ -n "$result" ]; then
                    result="$result:$entry"
                else
                    result="$entry"
                fi
                ;;
        esac
    done

    echo "$result"
}

finalize_and_report() {
    local build_dir
    local total_oleans

    build_dir="$(detect_build_dir "$MATHLIB_DIR")"
    if [ ! -d "$build_dir" ]; then
        die "Mathlib build output not found under $MATHLIB_DIR"
    fi

    export MATHLIB_PATH
    MATHLIB_PATH="$(build_mathlib_path "$build_dir")"
    if [ -z "$MATHLIB_PATH" ]; then
        die "Failed to compute MATHLIB_PATH from $build_dir"
    fi

    total_oleans="$(count_all_oleans "$MATHLIB_DIR")"

    log "Mathlib .olean setup complete"
    log "Checkout directory: $MATHLIB_DIR"
    log "Primary build output: $build_dir"
    log "Exported MATHLIB_PATH=$MATHLIB_PATH"
    log "Final .olean file count: $total_oleans"
}

echo "============================================================"
echo "Mathlib4 .olean setup"
echo "============================================================"

MATHLIB_DIR="$(choose_mathlib_dir)"
log "Requested data directory: $DATA_DIR"
log "Using Mathlib checkout: $MATHLIB_DIR"

if mathlib_is_ready "$MATHLIB_DIR"; then
    log "Mathlib .olean files already exist; skipping download and build"
    finalize_and_report
    exit 0
fi

ensure_checkout

if mathlib_is_ready "$MATHLIB_DIR"; then
    log "Mathlib .olean files found after checkout; skipping build"
    finalize_and_report
    exit 0
fi

ensure_lean_toolchain

log "Attempting to download prebuilt Mathlib .olean files via lake cache"
if (cd "$MATHLIB_DIR" && lake exe cache get); then
    log "Successfully downloaded prebuilt Mathlib cache"
else
    warn "lake exe cache get failed; falling back to lake build"
fi

if ! mathlib_is_ready "$MATHLIB_DIR"; then
    log "Compiling Mathlib from source with lake build"
    (cd "$MATHLIB_DIR" && lake build)
fi

if ! mathlib_is_ready "$MATHLIB_DIR"; then
    die "Mathlib build completed without producing usable .olean files"
fi

finalize_and_report
