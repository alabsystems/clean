// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-typecheck companions for LRA boundary success-path fixtures.
//!
//! Each test mirrors a success fixture from `lra_boundary.rs` and verifies
//! that the reconstructed proof term actually type-checks in the kernel.
//! Post-#2896, the zero-coefficient case is the only remaining direct
//! success-path fixture in `lra_boundary.rs`; the formerly similar symbolic
//! tail variants are semantic-boundary regressions covered in
//! `lra_boundary_semantic_boundary.rs`.
//!
//! For semantic-boundary failure assertions (proof_term.is_none()), see
//! `lra_boundary_semantic_boundary.rs`.
//!
//! Part of #2912.

use super::support::kernel::{assert_lra_proof_type_checks, mk_lra_kernel_env};
use super::support::semantic::{mk_raw_le, register_int_const, register_int_var};
use super::{
    attempt_reconstruction, Expr, FarkasAnnotation, Name, Proof, TermStore, VariableMapping,
};

#[test]
fn test_lra_boundary_zero_coefficient_ignores_symbolic_tail_type_checks_in_kernel() {
    // Companion to lra_boundary::test_theory_lemma_lra_farkas_zero_coefficient_ignores_symbolic_tail.
    // After zero-coefficient pruning, only the two concrete bounds remain:
    // ¬(3≤2) and ¬(5≤4). The reconstruction succeeds and the proof term should
    // type-check in the kernel.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let three = register_int_const(&mut terms, &mut map, "const3", 3);
    let two = register_int_const(&mut terms, &mut map, "const2", 2);
    let five = register_int_const(&mut terms, &mut map, "const5", 5);
    let four = register_int_const(&mut terms, &mut map, "const4", 4);
    let x = register_int_var(&mut terms, &mut map, "fvar_31", 31);
    let y = register_int_var(&mut terms, &mut map, "fvar_32", 32);

    let le_3_2 = mk_raw_le(&mut terms, three, two);
    let le_5_4 = mk_raw_le(&mut terms, five, four);
    let le_xy = terms.mk_le(x, y);
    let not_le_3_2 = terms.mk_not(le_3_2);
    let not_le_5_4 = terms.mk_not(le_5_4);
    let not_le_xy = terms.mk_not(le_xy);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1, 0]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_3_2, not_le_5_4, not_le_xy], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(
        result.stats.reconstructed_steps, 1,
        "zero-coefficient success fixture should reconstruct exactly one theory-lemma step: {:?}",
        result.stats.first_diagnostic
    );
    assert_eq!(
        result.stats.trust_boundary_steps, 0,
        "zero-coefficient success fixture should stay off the trust boundary"
    );
    assert_eq!(
        result.stats.trust_fallback_steps, 0,
        "zero-coefficient success fixture should not fall back to trust"
    );
    let proof_term = result
        .proof_term
        .expect("zero-coefficient success fixture should produce a proof term");

    let env = mk_lra_kernel_env();
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    assert_lra_proof_type_checks(
        &env,
        &proof_term,
        &[
            (clean_kernel::FVarId::new(31), "x", int_ty.clone()),
            (clean_kernel::FVarId::new(32), "y", int_ty),
        ],
        "zero-coefficient boundary success fixture",
    );
}
