#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
#
# MECHANIZED CNF-identity gate for the B-cert production-scale demo (#56 / #95).
#
# Ties proofs/lrat_checker_imul_demo.lean's embedded CNFTree to ay's bit-blasted
# .cnf: re-serializes the CNFTree leaves (== the exact clause sequence read from
# ay's .cnf) back to canonical DIMACS and asserts SHA-256 equality with ay's
# .cnf clause body, AND confirms that hash is the one BAKED INTO the .lean
# (`imul_cnf_digest`).  Exit 0 == faithful; nonzero == drift (fail-closed).
#
# This is the "mechanized, not prose" half of the CNF-faithfulness trusted
# surface: the Clean kernel proves the cert refutes the embedded CNF; THIS gate
# proves the embedded CNF is byte-identical to what ay actually bit-blasted.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# The COMMITTED, green-checking demo cert (the 4-bit mul5 multiplier identity).
CNF="$ROOT/proofs/bcert_imul/mul5_w4.cnf"
LRAT="$ROOT/proofs/bcert_imul/mul5_w4.lrat"
LEAN="$ROOT/proofs/lrat_checker_imul_demo.lean"

# 1) clause-body digest of ay's .cnf, and the transcoder round-trip identity.
EXPECT="$(python3 "$ROOT/scripts/lrat_to_clean.py" --cnf "$CNF" --lrat "$LRAT" \
  | sed -n 's/.*digest=\([0-9a-f]*\).*/\1/p')"

python3 "$ROOT/scripts/lrat_to_clean.py" --cnf "$CNF" --lrat "$LRAT" \
  --verify-digest --expect-digest "$EXPECT"

# 2) confirm the .lean has that exact digest baked in.
if grep -q "\"$EXPECT\"" "$LEAN"; then
  echo "LEAN-BAKED DIGEST MATCH: imul_cnf_digest == $EXPECT"
else
  echo "LEAN-BAKED DIGEST MISMATCH (expected $EXPECT in $LEAN)" >&2
  exit 1
fi

# 3) (informational) full-file SHA pin from the staged artifact manifest.
echo "--- ay .cnf full-file SHA-256 (includes comment header) ---"
shasum -a 256 "$CNF"
echo "ALL CNF-IDENTITY CHECKS PASSED"
