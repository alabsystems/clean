#!/bin/sh
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0

# Build the four public-release library test binaries in one Cargo invocation
# so their shared dependencies use the same feature-unified graph. Execute the
# memory-sensitive clean-auto binary in verified, serial process shards, then
# use bounded parallelism for the larger non-solver suites.
set -eu

# Cargo applies this repository default to processes it launches, but the
# helper executes the compiled libtest binaries directly after Cargo exits.
# Re-establish the same default without overriding an explicit caller value.
if [ "${RUST_MIN_STACK+x}" != x ]; then
  RUST_MIN_STACK=67108864
fi
export RUST_MIN_STACK

# WORKSPACE PACKAGE SPECS, DERIVED PER RUN -- NOT WRITTEN DOWN.
#
# This helper died at `cargo test`, exit 101, before it measured anything:
#
#     error: specification `clean-kernel` is ambiguous
#       clean-kernel@0.1.0
#       clean-kernel@0.4.0
#
# It is not a stale query. There really are two `clean-kernel` packages in the
# resolved graph. `trust-ir` (pinned by Git rev) declares
# `clean-kernel = { version = "0.1.0", git = ".../clean.git", rev = 429df01e }`,
# and this workspace's root `[patch."https://github.com/alabsystems/clean.git"]`
# exists precisely to collapse that back onto `crates/clean-kernel`. A Cargo
# patch only applies while the LOCAL version satisfies the dependency's
# requirement, so `chore(release): 0.1.0 -> 0.2.0` (ed45a281c, 2026-08-20) made
# the patch inert without a word, and the same commit regenerated Cargo.lock and
# wrote the second `clean-kernel` into it. Measured, not inferred: at
# `ed45a281c^` the lock holds ONE clean-kernel (0.1.0, no `source`); at
# ed45a281c it holds two. Setting the workspace version back to 0.1.0 in a
# throwaway tree makes the Git copy vanish from the lock entirely.
#
# Only `-p clean-auto` drags it into spec scope (clean-auto depends on trust-ir
# directly), which is why `cargo test -p clean-kernel` alone still resolves and
# nothing on the daily path noticed.
#
# The fix here is the SPEC, and deliberately not a version-qualified one.
# `-p clean-kernel@0.4.0` resolves today and breaks at the next `pub bump
# --minor` -- a producer-local identity that drifts is the wrong identity. So
# each spec is derived from the member's own manifest at run time: the path is
# the stable part, the version is not.
# Resolved into variables BEFORE the cargo call on purpose. Inlining these as
# `-p "$(workspace_spec clean-kernel)"` puts the helper in a COMMAND
# SUBSTITUTION, where its `exit 1` ends only the subshell: cargo would then be
# handed `-p ""` and fail with a message about an empty package name instead of
# the real one. `set -e` aborts on a failed assignment; it does not abort on a
# failed substitution inside an argument list.
workspace_spec() {
  spec=$(cargo pkgid --locked --manifest-path "crates/$1/Cargo.toml")
  if [ -z "$spec" ]; then
    echo "error: no workspace package id for crates/$1/Cargo.toml" >&2
    return 1
  fi
  printf '%s\n' "$spec"
}

SPEC_KERNEL=$(workspace_spec clean-kernel)
SPEC_OLEAN=$(workspace_spec clean-olean)
SPEC_AUTO=$(workspace_spec clean-auto)
SPEC_MATHVERSE=$(workspace_spec clean-mathverse)

# The duplication itself is NOT fixed by the line above and must not look fixed.
# Two Clean kernels stay in the graph, and clean-auto's test binary links the
# stale one; the real repair is to move trust-ir's version requirement forward
# (upstream trust-ir already says `version = "0.4.0"` as of 1541c0e), i.e. to
# advance this repo's seven `trust-ir` Git pins -- a producer bump the crystal
# lane owns, not this helper. Report it every run so it cannot go quiet again.
if grep -q 'source = "git+https://github.com/alabsystems/clean.git' Cargo.lock 2>/dev/null; then
  echo "NOTICE: the root [patch] for https://github.com/alabsystems/clean.git is INERT --"
  echo "        Cargo.lock still resolves a second copy of a Clean crate from Git."
  grep -B2 'source = "git+https://github.com/alabsystems/clean.git' Cargo.lock \
    | grep -E '^(name|version) = ' | paste - - | sed 's/^/          /'
  echo "        Cause: a Cargo patch is version-gated; trust-ir requires clean-kernel"
  echo "        ^0.1.0 and this workspace is past it (introduced by ed45a281c)."
  echo "        Remedy: advance the trust-ir Git pins, NOT the lock -- regenerating the"
  echo "        lock is what encoded the duplication in the first place."
fi

cargo test --locked --lib \
  -p "$SPEC_KERNEL" \
  -p "$SPEC_OLEAN" \
  -p "$SPEC_AUTO" \
  -p "$SPEC_MATHVERSE" \
  --no-run

target_root=${CARGO_TARGET_DIR:-target}
case "$target_root" in
  /*) ;;
  *) target_root="$PWD/$target_root" ;;
esac
deps_dir="$target_root/debug/deps"

find_library_test_binary() {
  stem=$1
  binary=

  for candidate in "$deps_dir/$stem"-*; do
    if [ ! -f "$candidate" ] || [ ! -x "$candidate" ]; then
      continue
    fi
    if [ -n "$binary" ]; then
      echo "error: multiple executable test binaries found for $stem" >&2
      echo "  $binary" >&2
      echo "  $candidate" >&2
      exit 1
    fi
    binary=$candidate
  done

  if [ -z "$binary" ]; then
    echo "error: no executable test binary found for $stem in $deps_dir" >&2
    exit 1
  fi

  printf '%s\n' "$binary"
}

run_sharded_library_tests() {
  stem=$1
  partition=$2
  max_tests=$3
  jobs=$4
  workers=$5
  binary=$(find_library_test_binary "$stem")

  python3 scripts/run_public_release_test_shards.py \
    --binary "$binary" \
    --label "$stem" \
    --partition "$partition" \
    --max-tests "$max_tests" \
    --jobs "$jobs" \
    --test-threads "$workers"
}

run_library_tests() {
  stem=$1
  workers=$2
  binary=$(find_library_test_binary "$stem")

  echo "== running $stem library tests with $workers worker(s)"
  "$binary" "--test-threads=$workers"
}

run_sharded_library_tests clean_auto namespace 100 1 1
run_sharded_library_tests clean_kernel character 40 5 2
run_library_tests clean_olean 4
run_library_tests clean_mathverse 4
