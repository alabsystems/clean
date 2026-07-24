#!/usr/bin/env bash
# Copyright 2026 Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Cross-check: the F* lemmas that clean-mathverse `fstar_ay` admits to BEDROCK
# via ay proof reconstruction are GENUINE F*-verified lemmas.
#
# F* discharges each lemma by SMT (Z3) — no CIC proof term. ay then re-proves
# the same statement and reconstructs a Clean CIC proof reducing to the 3
# foundational axioms, with Z3 OUT of the trusted base. This script runs the F*
# side (proving F* agrees the lemmas hold); the Clean side is the CI gate
# `fstar_ay::tests::ay_proven_fstar_facts_admitted_and_reverify`.
#
# Requirements (auto-detected; install hints printed if missing):
#   - F* (Darwin-arm64 binary release) at $FSTAR_HOME/bin/fstar.exe
#   - Z3 4.13.3 as `z3-4.13.3` on PATH (F* pins this exact version)
#
# Reproduce the toolchain install (macOS arm64):
#   curl -sL -o /tmp/fstar.tgz \
#     https://github.com/FStarLang/FStar/releases/download/v2026.06.21/fstar-v2026.06.21-Darwin-arm64.tar.gz
#   tar -xzf /tmp/fstar.tgz -C "$HOME"   # -> $HOME/fstar
#   curl -sL -o /tmp/z3.zip \
#     https://github.com/Z3Prover/z3/releases/download/z3-4.13.3/z3-4.13.3-arm64-osx-13.7.zip
#   unzip -oq /tmp/z3.zip -d /tmp && cp /tmp/z3-4.13.3-*/bin/z3 "$HOME/fstar/bin/z3-4.13.3"
set -euo pipefail

FSTAR_HOME="${FSTAR_HOME:-$HOME/fstar}"
FSTAR="$FSTAR_HOME/bin/fstar.exe"
FIXTURE="$(cd "$(dirname "$0")/.." && pwd)/crates/clean-mathverse/tests/fixtures/fstar/FstarAyCrosscheck.fst"

if [[ ! -x "$FSTAR" ]]; then
  echo "SKIP: F* not found at $FSTAR (see install hints in this script's header)." >&2
  exit 0
fi
export PATH="$FSTAR_HOME/bin:$PATH"

echo "=== F* verifying the ay-admitted lemmas ($FIXTURE) ==="
out="$("$FSTAR" --log_queries "$FIXTURE" 2>&1)" || { echo "$out" >&2; exit 1; }
echo "$out" | tail -3

if echo "$out" | grep -q "All verification conditions discharged successfully"; then
  echo "OK: F* confirms every ay-admitted lemma holds (each discharged by Z3/SMT)."
  echo "    The Clean side re-proves the SAME statements to the 3 axioms via ay"
  echo "    reconstruction — gate: cargo test -p clean-mathverse fstar_ay::tests"
else
  echo "FAIL: F* did not discharge all lemmas." >&2
  exit 1
fi
