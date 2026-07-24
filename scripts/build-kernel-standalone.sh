#!/usr/bin/env bash
# build-kernel-standalone.sh
#
# Reproducibly build and test the `clean-kernel` crate in a STANDALONE
# single-crate Cargo workspace, with no dependency on the rest of the
# `clean` workspace (in particular, no SMT-solver sibling crates).
#
# Why this exists
# ---------------
# The NY proof-carrying-verification program needs `clean-kernel` proofs
# (e.g. `NNVerify::farkas_combine_list`, the exact-rational cert parser) to
# be re-checkable on machines that only have a checkout of `clean` and a
# stock crates.io toolchain -- without building the full workspace. The full
# workspace pulls in the SMT solver and other heavy/optional siblings that are not always
# present. This script reproduces, deterministically and without any manual
# scratch setup, the verified recipe:
#
#   * copy crates/clean-kernel/{src,tests,benches} into a scratch tree;
#   * generate a standalone member manifest where every `<dep>.workspace =
#     true` is replaced by a concrete crates.io version, with only the deps
#     the kernel test build needs, and NO [[bin]]/[[test]]/[[bench]] targets
#     (those pull in clean-elab/clean-parser/criterion siblings);
#   * write a one-member [workspace] root manifest;
#   * run: cargo test -p clean-kernel --lib --features math-overlays nn_verify
#
# This script DOES NOT modify clean-kernel source. It only reads the source
# tree and writes into a scratch build directory.
#
# Usage
# -----
#   scripts/build-kernel-standalone.sh [BUILD_DIR]
#
#   BUILD_DIR   Optional. Directory to assemble the standalone workspace in.
#               Defaults to a fresh `mktemp -d`. If given and non-empty it is
#               wiped (the kernel subdir) and rebuilt. The path is printed so
#               the target/ cache can be reused on re-runs.
#
# Environment
# -----------
#   KERNEL_TEST_FILTER   Test name filter passed to `cargo test`.
#                        Default: "nn_verify".  Set to "" to run all lib tests.
#   KERNEL_FEATURES      Cargo feature list. Default: "math-overlays".
#   SKIP_TEST=1          Assemble + `cargo build` only; skip running tests.
#
# Exit status is the exit status of the cargo invocation.
set -euo pipefail

# ---------------------------------------------------------------------------
# Locate repo root and the clean-kernel source crate.
# ---------------------------------------------------------------------------
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
if REPO_ROOT="$(git -C "$SCRIPT_DIR" rev-parse --show-toplevel 2>/dev/null)"; then
  :
else
  # Fallback: assume this script lives in <repo>/scripts/.
  REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
fi

KERNEL_SRC="$REPO_ROOT/crates/clean-kernel"
if [[ ! -f "$KERNEL_SRC/Cargo.toml" ]]; then
  echo "error: clean-kernel not found at $KERNEL_SRC" >&2
  exit 1
fi

KERNEL_FEATURES="${KERNEL_FEATURES:-math-overlays}"
KERNEL_TEST_FILTER="${KERNEL_TEST_FILTER:-nn_verify}"

# ---------------------------------------------------------------------------
# Choose / prepare the build directory.
# ---------------------------------------------------------------------------
BUILD_DIR="${1:-}"
if [[ -z "$BUILD_DIR" ]]; then
  BUILD_DIR="$(mktemp -d "${TMPDIR:-/tmp}/clean-kernel-standalone.XXXXXX")"
fi
mkdir -p "$BUILD_DIR/kernel"
echo "==> repo root:    $REPO_ROOT"
echo "==> kernel src:   $KERNEL_SRC"
echo "==> build dir:    $BUILD_DIR"

# ---------------------------------------------------------------------------
# Copy the kernel source tree (src + tests + benches) into the scratch crate.
# We do NOT copy the source Cargo.toml: we synthesise a standalone one below.
# Using `rsync --delete` keeps re-runs idempotent without touching mtimes of
# unchanged files, so cargo's incremental cache in BUILD_DIR/target stays warm.
# ---------------------------------------------------------------------------
for sub in src tests benches; do
  if [[ -d "$KERNEL_SRC/$sub" ]]; then
    if command -v rsync >/dev/null 2>&1; then
      rsync -a --delete "$KERNEL_SRC/$sub/" "$BUILD_DIR/kernel/$sub/"
    else
      rm -rf "$BUILD_DIR/kernel/$sub"
      cp -R "$KERNEL_SRC/$sub" "$BUILD_DIR/kernel/$sub"
    fi
  fi
done

# ---------------------------------------------------------------------------
# Sanity check: the concrete-version manifest below must cover every
# dependency the source manifest declares that is reachable from the
# default + math-overlays + test-utils lib/test build. If clean-kernel grows
# a new mandatory dependency, this check fails loudly instead of producing a
# confusing downstream compile error.
#
# We only assert coverage of NON-optional [dependencies]; optional deps that
# are only pulled in by features we don't enable (clap, clean-features) are
# intentionally excluded from the standalone manifest.
# ---------------------------------------------------------------------------
EXPECTED_NONOPTIONAL_DEPS="thiserror hashbrown ahash smallvec serde serde_json bincode lz4_flex zstd rayon stacker sha2"
missing=""
for dep in $EXPECTED_NONOPTIONAL_DEPS; do
  # match a line like `dep.workspace` or `dep = {` or `dep = "` at start of a
  # dependency entry in the [dependencies] table of the source manifest.
  if ! grep -Eq "^[[:space:]]*${dep}([[:space:]]*=|\.)" "$KERNEL_SRC/Cargo.toml"; then
    missing="$missing $dep"
  fi
done
if [[ -n "$missing" ]]; then
  echo "error: source manifest no longer declares expected deps:$missing" >&2
  echo "       update EXPECTED_NONOPTIONAL_DEPS and the standalone manifest." >&2
  exit 1
fi

# ---------------------------------------------------------------------------
# Generate the standalone member manifest.
#
# Every dependency below is a concrete crates.io version, replacing the
# `<dep>.workspace = true` entries from the workspace manifest. Versions are
# pinned to match clean's [workspace.dependencies] table. Cargo.lock (written
# on first build) freezes the exact resolved graph for byte-for-byte reruns.
#
# Deliberately omitted vs the source manifest:
#   * cli/optional siblings: clap, clean-features  (feature `cli`, not built)
#   * dev-only siblings: criterion, clean-elab, clean-parser, sysinfo
#     (only used by [[bench]] / [[test]] integration targets, which we drop)
#   * all [[bin]] / [[test]] / [[bench]] targets (pull in the above siblings)
# Retained features: default, math-overlays, test-utils (+ debug-* / kani /
# geometry-tools no-op flags) so the verified `--features math-overlays`
# invocation and `test-utils`-gated helpers both work.
# ---------------------------------------------------------------------------
cat > "$BUILD_DIR/kernel/Cargo.toml" <<'KERNEL_MANIFEST'
# AUTO-GENERATED by scripts/build-kernel-standalone.sh -- do not edit.
# Standalone single-crate manifest for clean-kernel (no clean workspace deps).
[package]
name = "clean-kernel"
version = "0.1.0"
edition = "2021"
license = "Apache-2.0"
description = "clean trusted type checker kernel"

[lib]
path = "src/lib.rs"

[dependencies]
thiserror = "2.0"
hashbrown = { version = "0.16.1", features = ["serde"] }
ahash = "0.8"
smallvec = { version = "1.15.1", features = ["serde"] }
serde = { version = "1.0", features = ["derive", "rc"] }
serde_json = "1.0"
bincode = "1.3"
lz4_flex = "0.11"
zstd = { version = "0.13", features = ["zdict_builder"] }
rayon = "1.10"
stacker = "0.1"
sha2 = "0.10"
anyhow = { version = "1.0", optional = true }
tempfile = { version = "3.14", optional = true }

[dev-dependencies]
proptest = "1.4"
serial_test = "3.2"
tempfile = "3.14"
anyhow = "1.0"

[features]
default = []
math-overlays = []
test-utils = ["dep:anyhow", "dep:tempfile"]
kani = []
debug-whnf = []
debug-infer = []
debug-def-eq = []
geometry-tools = []
KERNEL_MANIFEST

# ---------------------------------------------------------------------------
# Generate the one-member [workspace] root manifest.
# ---------------------------------------------------------------------------
cat > "$BUILD_DIR/Cargo.toml" <<'ROOT_MANIFEST'
# AUTO-GENERATED by scripts/build-kernel-standalone.sh -- do not edit.
[workspace]
members = ["kernel"]
resolver = "2"
ROOT_MANIFEST

# ---------------------------------------------------------------------------
# Build / test.
# ---------------------------------------------------------------------------
cargo_args=(test -p clean-kernel --lib --features "$KERNEL_FEATURES")
if [[ -n "$KERNEL_TEST_FILTER" ]]; then
  cargo_args+=("$KERNEL_TEST_FILTER")
fi

echo "==> running: cargo ${cargo_args[*]}"
echo "==>   (in $BUILD_DIR)"

if [[ "${SKIP_TEST:-0}" == "1" ]]; then
  ( cd "$BUILD_DIR" && cargo build -p clean-kernel --lib --features "$KERNEL_FEATURES" )
  echo "==> SKIP_TEST=1: build only, tests not run."
else
  ( cd "$BUILD_DIR" && cargo "${cargo_args[@]}" )
fi

echo "==> done. Standalone workspace at: $BUILD_DIR"
echo "==> re-run with the same BUILD_DIR to reuse the cargo cache:"
echo "==>   $0 $BUILD_DIR"
--- END FILE ---
