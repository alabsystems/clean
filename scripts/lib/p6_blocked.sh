#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
#
# p6_blocked <script> — refuse to run a Mathlib "KernelVerified corpus" script
# under unit P6, slice 1a (docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md;
# designs/2026-11-16-p6-acceptance-identity.md; docs/DECISIONS.md, 2026-11-16).
#
# Each script that sources this one exists to produce, assemble, count or cite
# STORED `KernelVerified` shard headers minted by `stamp-verified` from a
# development run. P6 deleted that stamp: a legacy-profile acceptance is
# development tier and confers no label (P2 clause 1), and the reference
# producer that will mint labels, with receipts, is slice 1b. Run now, these
# scripts would either count zero and report it as a regression, or re-count
# pre-P6 stamps, which are claims and not evidence. There is no override: slice
# 1b re-points them onto the reference producer and removes this guard.
p6_blocked() {
  echo "BLOCKED (P6 slice 1a): $1 builds or reads a stored-KernelVerified Mathlib corpus." >&2
  echo "  No lane in this build stamps a header from a development run (P2 clause 1); the" >&2
  echo "  reference producer lands in P6 slice 1b. Development acceptances are in each run's" >&2
  echo "  kernel-verified.json (read them with scripts/acceptance_manifest.py)." >&2
  exit 2
}
