#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Check that the source census of by-name references the dependency-closed
# replay can reach (crates/clean-olean/src/recheck_closed/by_name_census_tests.rs)
# over-approximates what the LINKER keeps for a binary that calls only
# `recheck_closed` (crates/clean-olean/examples/replay_reachability_probe.rs).
#
# Usage: scripts/replay_reachability_census.sh [target-dir]
#   target-dir  where the probe, the census dump and the symbol list are built
#               (default: an inherited $CARGO_TARGET_DIR, else
#               target/replay-census). An inherited CARGO_TARGET_DIR is honoured
#               ON PURPOSE: the gate-registry demonstrator exports the sandbox's
#               own target dir and evicts the crate an arm mutated from THAT
#               directory, so a script that overrode it would keep the planted
#               unit in a directory nothing evicts, and the next replay's
#               unmutated baseline would link the plant (docs/GATE_REGISTRY.md,
#               the 2026-09-08 note).
#   DEMANGLE    optional: a Rust v0 demangler reading symbols on stdin and
#               printing the alternate (hash-free) form, one per line (e.g.
#               rustfilt). Unset, the Trust sysroot's own `llvm-nm --demangle`
#               reads the probe: the toolchain that mangled the symbols
#               demangles them, and nothing outside the sysroot is needed.
#               Until 2026-10-07 the default was `rustfilt`, which is not part
#               of any Trust install, so on a host without it the pipeline died
#               at `rustfilt: command not found` and the census never ran.
#
# Exit 0: every linker-kept kernel item with a source definition is in the
# census's reached set. Exit 1: the census missed one (listed). Exit 2: no
# demangler (DEMANGLE unset and the sysroot carries no llvm-nm) -- a refusal,
# never a skip: a census that did not run says nothing.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
T=${1:-${CARGO_TARGET_DIR:-$ROOT/target/replay-census}}
export CARGO_TARGET_DIR=$T
cd "$ROOT"
# The canonical Trust targo (scripts/rust_frontend.sh --targo), never PATH's:
# ~/.cargo/bin/targo is a rustup symlink that targo refuses to run as.
TARGO=$(bash "$ROOT/scripts/rust_frontend.sh" --targo)
# The demangler, resolved BEFORE anything builds, so a host that cannot read
# the probe refuses in a second instead of after the build.
NM=""
if [ -z "${DEMANGLE:-}" ]; then
  SYSROOT=$("$(dirname "$TARGO")/rustc" --print sysroot)
  HOST=$("$(dirname "$TARGO")/rustc" -vV | sed -n 's/^host: //p')
  NM="$SYSROOT/lib/rustlib/$HOST/bin/llvm-nm"
  if [ ! -x "$NM" ]; then
    echo "replay_reachability_census: REFUSED -- DEMANGLE is unset and the Trust sysroot carries no $NM (the llvm-tools component); set DEMANGLE=<a Rust v0 demangler> to run the census" >&2
    exit 2
  fi
fi
# No optimisation: nothing is inlined away, so every reachable function keeps
# its symbol; an executable is linked with dead-code stripping.
"$TARGO" --unverified build --locked -p clean-olean --example replay_reachability_probe
# The census test writes its dump before it asserts anything. Both inputs of
# the comparison are deleted first: the target dir persists between runs, so a
# test that failed to BUILD would otherwise leave the previous run's dump in
# place and `test -s` below would compare a census this tree never produced.
rm -f "$T/census.tsv" "$T/probe.symbols"
CLEAN_BY_NAME_CENSUS_DUMP=$T/census.tsv \
  "$TARGO" --unverified test --locked -p clean-olean --lib by_name_census || true
test -s "$T/census.tsv"
BIN=$T/debug/examples/replay_reachability_probe
if [ -n "$NM" ]; then
  "$NM" --demangle --just-symbol-name "$BIN"
elif nm -j "$BIN" >/dev/null 2>&1; then
  nm -j "$BIN" | $DEMANGLE
else
  nm --format=just-symbols "$BIN" | $DEMANGLE
fi | grep clean_kernel > "$T/probe.symbols"
python3 "$ROOT/scripts/replay_reachability_census.py" "$T/probe.symbols" "$T/census.tsv"
