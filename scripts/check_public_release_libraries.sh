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

cargo test --locked --lib \
  -p clean-kernel \
  -p clean-olean \
  -p clean-auto \
  -p clean-mathverse \
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
