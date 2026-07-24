#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# SPDX-License-Identifier: Apache-2.0
#
# Thin shell wrapper around the Python module
# `scripts.axiom_audit.aggregates` (#3613).
#
# Default: recompute and write the top-level aggregate fields
# (`total_domain_axioms`, `total_theorems`, `constructive_theorems`) in
# `data/axiom_audit.json` from the per-conjecture sub-trees.
#
# Flags are forwarded verbatim to the Python module:
#
#   scripts/recompute_axiom_audit_aggregates.sh             # write (default)
#   scripts/recompute_axiom_audit_aggregates.sh --check     # verify, exit 1 on drift
#   scripts/recompute_axiom_audit_aggregates.sh --audit <path> --check
#
# Exit codes (propagated from the Python module):
#   0 — aggregates match / were written successfully
#   1 — aggregates stale, null, or otherwise invalid (check mode)
#   2 — schema error / input file missing

set -euo pipefail

REPO_ROOT="$(git rev-parse --show-toplevel 2>/dev/null || cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

exec python3 -m scripts.axiom_audit.aggregates "$@"
