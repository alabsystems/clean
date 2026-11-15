#!/bin/sh
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0

# Build the four public-release library test binaries in one Cargo invocation
# so their shared dependencies use the same feature-unified graph. Execute the
# memory-sensitive clean-auto binary in verified, serial process shards, then
# use bounded parallelism for the larger non-solver suites.
set -eu

# An explicit phase driver admits each build and runtime separately. The
# orchestration shell itself then holds no legacy CPU grant across a native
# Targo invocation. An unset driver retains the ordinary direct route.
if [ "${CLEAN_PUBLIC_RELEASE_PHASE_DRIVER+x}" = x ]; then
  case "$CLEAN_PUBLIC_RELEASE_PHASE_DRIVER" in
    /*) ;;
    *) echo "error: CLEAN_PUBLIC_RELEASE_PHASE_DRIVER must name an absolute executable" >&2; exit 2 ;;
  esac
  if [ ! -f "$CLEAN_PUBLIC_RELEASE_PHASE_DRIVER" ] || [ -L "$CLEAN_PUBLIC_RELEASE_PHASE_DRIVER" ] || [ ! -x "$CLEAN_PUBLIC_RELEASE_PHASE_DRIVER" ]; then
    echo "error: CLEAN_PUBLIC_RELEASE_PHASE_DRIVER must name a regular non-symlink executable" >&2
    exit 2
  fi
fi

run_phase() {
  phase=$1
  shift
  if [ "${CLEAN_PUBLIC_RELEASE_PHASE_DRIVER+x}" = x ]; then
    "$CLEAN_PUBLIC_RELEASE_PHASE_DRIVER" "$phase" -- "$@"
  else
    "$@"
  fi
}

# THE DRIVER IS TARGO, NOT CARGO. The owner directive is that every ALab build
# and release gate runs through the Trust pipeline, and publish/config.sh's
# CHECK_CMD_DEFAULT does. This helper used to call bare `cargo`, which in the
# public export then resolved to a stock pin and so ran the one test step the
# gate delegates here on upstream Rust.
# `rustup run trust targo` names the sealed toolchain explicitly, so neither the
# export's rust-toolchain.toml nor the inherited PATH picks the compiler.
# The build is `targo --unverified test`: a build-quality check with NO proof
# claim. The gate's proof claim is its separate `targo trust check
# --allow-l0-gaps` step (`targo trust test` refuses every execution subject
# with a proc macro in its TCB, by design). `TARGO` may name one explicit
# driver executable instead (same contract as scripts/test_atpkg_recipe.py).
targo() {
  if [ -n "${TARGO:-}" ]; then
    run_phase targo "$TARGO" "$@"
  else
    run_phase targo rustup run trust targo "$@"
  fi
}

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
  spec=$(targo pkgid --locked --manifest-path "crates/$1/Cargo.toml")
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

target_root=${CARGO_TARGET_DIR:-target}
case "$target_root" in
  /*) ;;
  *) target_root="$PWD/$target_root" ;;
esac
mkdir -p "$target_root"

# THE BINARIES ARE THE ONES THIS BUILD REPORTS, NOT WHAT `deps/` HOLDS.
# Cargo names each test binary `<crate>-<hash>`, and the hash moves with the
# feature set and the profile, so a target directory that has built a crate's
# lib tests twice (a feature-unified workspace build, a `--features` build of a
# dependent) holds one executable per hash. Globbing `deps/<crate>-*` refused
# such a directory ("multiple executable test binaries"), measured 2026-10-18
# on a developer target dir that holds two `clean_auto` lib-test binaries, and
# could never say which of them this invocation built. Cargo's own artifact
# report can: one `compiler-artifact` message per test target, fresh or rebuilt,
# with the path of the executable it stands for.
artifacts="$target_root/public-release-libraries.artifacts.jsonl"
targo --unverified test --locked --lib \
  -p "$SPEC_KERNEL" \
  -p "$SPEC_OLEAN" \
  -p "$SPEC_AUTO" \
  -p "$SPEC_MATHVERSE" \
  --no-run --message-format=json-render-diagnostics >"$artifacts"

# Exactly one lib-test executable named `stem` in this build's report, or exit 1.
find_library_test_binary() {
  python3 - "$artifacts" "$1" <<'PY'
import json
import sys

report, stem = sys.argv[1], sys.argv[2]
found = set()
with open(report, encoding="utf-8") as lines:
    for line in lines:
        try:
            message = json.loads(line)
        except ValueError:
            continue
        if not isinstance(message, dict) or message.get("reason") != "compiler-artifact":
            continue
        target = message.get("target") or {}
        if (
            target.get("name") == stem
            and "lib" in (target.get("kind") or [])
            and (message.get("profile") or {}).get("test")
            and message.get("executable")
        ):
            found.add(message["executable"])
if len(found) != 1:
    sys.stderr.write(
        f"error: this build reports {len(found)} lib-test executables for {stem} "
        f"(expected exactly 1): {sorted(found)} in {report}\n"
    )
    sys.exit(1)
print(found.pop())
PY
}

run_sharded_library_tests() {
  stem=$1
  partition=$2
  max_tests=$3
  jobs=$4
  workers=$5
  binary=$(find_library_test_binary "$stem")

  run_phase runtime python3 scripts/run_public_release_test_shards.py \
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
  run_phase runtime "$binary" "--test-threads=$workers"
}

run_sharded_library_tests clean_auto namespace 100 1 1
run_sharded_library_tests clean_kernel character 40 5 2
run_library_tests clean_olean 4
run_library_tests clean_mathverse 4
