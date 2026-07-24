#!/usr/bin/env bash
#
# Generate the UNIFIED codegen-recheck manifest — the durable, checksum-pinned
# seed of the path that ties criterion 3 (durable seed) to criterion 2 (compiler
# out of the TCB): from this pinned source, the kernel independently re-checks a
# REAL trust-cg compiler lowering to trust_count == 0.
#
# Run from anywhere inside the clean repo.
#
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

OUT="genesis/codegen-recheck/MANIFEST.txt"

if command -v sha256sum >/dev/null 2>&1; then SHA() { sha256sum "$@"; }; else SHA() { shasum -a 256 "$@"; }; fi

# The load-bearing codegen-recheck source: the kernel's width-N bitvector
# gate-fidelity, the non-reflexive lowering bridge, the criterion-2 re-check
# test, the theory-lemma blast, the PROVEN sub-quadratic resolution checker
# (checkRefutes3) + its kernel-checked soundness theorem (checkRefutes3_sound,
# which the lowering bridge now discharges Unsat through), and the dependency
# lockfile (pins the trust-cg GVN-pass dev-dep commit).
FILES="$( {
  echo crates/clean-kernel/src/bitvec_compute.rs
  echo crates/clean-kernel/src/resolution_check.rs
  echo crates/clean-kernel/src/resolution_soundness.rs
  echo crates/clean-auto/src/bridge/ay_backend/proof_reconstruct/bv_lowering_bridge.rs
  echo crates/clean-auto/src/bridge/ay_backend/proof_reconstruct/bv_blast_reflection.rs
  echo crates/clean-auto/src/bridge/ay_backend/proof_reconstruct/tests_criterion2_gvn_lowering.rs
  echo crates/clean-auto/src/bridge/ay_backend/proof_reconstruct/theory_lemma_bv_compute_blast.rs
  echo Cargo.lock
} )"

TRUSTCG_COMMIT="$( (cd "$HOME/trust-cg" 2>/dev/null && git rev-parse HEAD) || echo unknown )"

{
  echo "# UNIFIED codegen-recheck seed — durable checksum-pinned: seed -> kernel re-checks a real trust-cg lowering to trust_count==0"
  echo "#"
  echo "# Reproduce:  genesis/codegen-recheck/reproduce.sh"
  echo "#   -> verifies these checksums, then builds + runs the kernel re-check of the"
  echo "#      REAL trust_cg_opt::gvn commutative-canonicalization lowering identity, asserting"
  echo "#      kernel trust_count == 0 (non-vacuous; a tampered lowering FAILS). Exit 0 == reproduced."
  echo "#"
  echo "clean_commit    = $(git rev-parse HEAD)"
  echo "trustcg_commit  = ${TRUSTCG_COMMIT}"
  echo "rustc           = $(rustc --version)"
  echo "host            = $(rustc -vV | grep '^host:' | cut -d' ' -f2)"
  echo "test            = clean-auto :: criterion2_gvn_{commute(ADD),xor,and,or}_commute_lowering_*_trust_count_zero"
  echo "kernel          = clean-kernel (codegen-recheck bitvector gate-fidelity layer)"
  echo "scope           = FOUR real trust_cg_opt::gvn commutative-canonicalization lowering KINDS, each non-vacuous"
  echo "                  (tamper-FAILS + forge->Bool.false): ADD (ripple-carry xor3/maj gate-fidelity, re-checked"
  echo "                  through width-16) + XOR/AND/OR (the three bitwise per-bit Bool.xor/and/or gate-fidelities,"
  echo "                  no carry). All -> kernel bvEq -> trust_count == 0."
  echo "honest_floor    = the codegen re-check uses clean-kernel's bitvec layer; the minimal-ck0 codegen port is the"
  echo "                  remaining unification (ck0 already re-checks math/software/AI — genesis/ck0/). rustc/LLVM are"
  echo "                  NOT trusted for the re-checked lowering. ISA model + the statement: the irreducible named floor."
  echo "# --- checksums (sha256) ---"
  while IFS= read -r f; do SHA "$f"; done <<< "$FILES"
} > "$OUT"

echo "wrote $OUT (pinned clean=$(git rev-parse --short HEAD) trust-cg=$(echo "$TRUSTCG_COMMIT" | cut -c1-9))"
