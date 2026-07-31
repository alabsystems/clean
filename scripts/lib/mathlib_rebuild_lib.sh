# shellcheck shell=bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Shared, PORTABLE helpers for the Mathlib KernelVerified rebuild toolchain.
#
# The historical stamp_mathlib_*.sh scripts each open-coded corpus discovery and
# LEAN_PATH construction, and several hardcoded one contributor's machine paths
# (absolute contributor checkout paths, `/tmp/mathlib_lean_path.txt`) so they only ran
# on that box. This library centralizes that logic so every rebuild entry point
# resolves the corpus the SAME portable way:
#
#   1. $MATHLIB_CHECKOUT            (explicit override — highest precedence)
#   2. $REPO_ROOT/data/raw/mathlib4 (what scripts/setup_mathlib_oleans.sh writes)
#   3. /tmp/mathlib4                (setup's fallback location)
#
# Sourcing this file only defines functions + sets defaults; it takes no lock and
# runs nothing. bash-3.2 safe (macOS system bash).

# mlr_repo_root: absolute repo root, derived from THIS file's location.
mlr_repo_root() { ( cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd ); }

# mlr_resolve_checkout: echo the Mathlib checkout dir whose build tree contains
# compiled Mathlib oleans, or return 1 if none is found. Never hardcodes a
# contributor path.
mlr_resolve_checkout() {
  local root cand
  root="$(mlr_repo_root)"
  for cand in "${MATHLIB_CHECKOUT:-}" "$root/data/raw/mathlib4" "/tmp/mathlib4"; do
    [ -n "$cand" ] || continue
    if [ -d "$cand/.lake/build/lib/lean/Mathlib" ]; then
      printf '%s' "$cand"
      return 0
    fi
  done
  return 1
}

# mlr_mllib <checkout>: echo the Lean library root inside a checkout (the dir
# that is passed as --closure-root and holds Mathlib/*.olean).
mlr_mllib() { printf '%s' "$1/.lake/build/lib/lean"; }

# mlr_build_lean_path <checkout>: echo a LEAN_PATH covering the Mathlib lib, the
# pinned toolchain's Lean core stdlib (read from the checkout's lean-toolchain),
# and every Lake dependency package build dir. Mirrors the resolution the
# committed gate (scripts/kv_ratchet_gate.sh) uses, so a rebuild and its gate
# resolve identical closures.
mlr_build_lean_path() {
  local chk="$1" mllib core lp p tc
  mllib="$(mlr_mllib "$chk")"
  lp="$mllib"
  if [ -f "$chk/lean-toolchain" ]; then
    tc="$(tr -d ' \t\r\n' < "$chk/lean-toolchain" | sed 's#/#--#; s#:#---#')"
    core="$HOME/.elan/toolchains/$tc/lib/lean"
    [ -d "$core" ] && lp="$lp:$core"
  fi
  for p in "$chk"/.lake/packages/*/.lake/build/lib/lean; do
    [ -d "$p" ] && lp="$lp:$p"
  done
  printf '%s' "$lp"
}

# mlr_resolve_clean_bin: echo a usable `clean` binary path or return 1.
# Precedence: $CLEAN_BIN > repo target/release > repo target/debug > PATH. The
# LOCAL build wins over any globally-installed `clean` so a rebuild always
# re-checks with the kernel under test, never a stale one.
mlr_resolve_clean_bin() {
  local root; root="$(mlr_repo_root)"
  if [ -n "${CLEAN_BIN:-}" ] && [ -x "$CLEAN_BIN" ]; then printf '%s' "$CLEAN_BIN"; return 0; fi
  if [ -x "$root/target/release/clean" ]; then printf '%s' "$root/target/release/clean"; return 0; fi
  if [ -x "$root/target/debug/clean" ]; then printf '%s' "$root/target/debug/clean"; return 0; fi
  local onpath; onpath="$(command -v clean 2>/dev/null || true)"
  [ -n "$onpath" ] && { printf '%s' "$onpath"; return 0; }
  return 1
}

# mlr_lean_path_roots <lean_path>: echo the count of ':'-separated roots (for
# plan/dry-run reporting).
mlr_lean_path_roots() { printf '%s' "$1" | tr ':' '\n' | grep -c .; }
