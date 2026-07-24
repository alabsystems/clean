// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-typecheck companions for LRA boundary trust-boundary regressions.

use super::support::boundary::{assert_lra_trust_boundary, register_int_const_as_var};
use super::support::semantic::register_int_var;
use super::{
    attempt_reconstruction, Expr, FarkasAnnotation, Name, Proof, ReconstructionError, TermStore,
    VariableMapping,
};

fn assert_semantic_boundary_type_checks(result: &super::super::ReconstructionResult, msg: &str) {
    assert_lra_trust_boundary(result, 0);
    let diagnostic = result
        .stats
        .first_diagnostic
        .as_ref()
        .expect("semantic-boundary result should record first_diagnostic");
    assert!(
        matches!(&diagnostic.error, ReconstructionError::TrustBoundary { .. }),
        "expected trust-boundary diagnostic, got {:?}",
        diagnostic.error
    );
    let ReconstructionError::TrustBoundary { description, .. } = &diagnostic.error else {
        unreachable!()
    };
    assert!(
        description.starts_with("Farkas semantic validation failed:"),
        "synthetic constant fixture should fail semantic validation, got {description:?}"
    );
    // After #2986, proof_term is None when reconstructed_steps == 0,
    // so kernel type-checking is no longer applicable for total-failure cases.
    assert!(
        result.proof_term.is_none(),
        "{msg}: total-failure trust-boundary should not produce a proof term"
    );
}

#[test]
fn test_lra_boundary_zero_coefficient_symbolic_tail_semantic_boundary_type_checks() {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let three = register_int_const_as_var(&mut terms, &mut map, "const3", 3);
    let two = register_int_const_as_var(&mut terms, &mut map, "const2", 2);
    let five = register_int_const_as_var(&mut terms, &mut map, "const5", 5);
    let four = register_int_const_as_var(&mut terms, &mut map, "const4", 4);
    let x = register_int_var(&mut terms, &mut map, "fvar_31", 31);
    let y = register_int_var(&mut terms, &mut map, "fvar_32", 32);

    let le_3_2 = terms.mk_le(three, two);
    let le_5_4 = terms.mk_le(five, four);
    let le_xy = terms.mk_le(x, y);

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_farkas(
        "LRA",
        vec![
            terms.mk_not(le_3_2),
            terms.mk_not(le_5_4),
            terms.mk_not(le_xy),
        ],
        FarkasAnnotation::from_ints(&[1, 1, 0]),
    );

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_semantic_boundary_type_checks(
        &result,
        "zero-coefficient LRA boundary semantic trust proof",
    );
}

#[test]
fn test_lra_boundary_single_concrete_bound_semantic_boundary_type_checks() {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let five = register_int_const_as_var(&mut terms, &mut map, "const5", 5);
    let three = register_int_const_as_var(&mut terms, &mut map, "const3", 3);
    let x = register_int_var(&mut terms, &mut map, "fvar_31", 31);
    let y = register_int_var(&mut terms, &mut map, "fvar_32", 32);

    let le_5_3 = terms.mk_le(five, three);
    let le_xy = terms.mk_le(x, y);

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_farkas(
        "LRA",
        vec![terms.mk_not(le_5_3), terms.mk_not(le_xy)],
        FarkasAnnotation::from_ints(&[1, 1]),
    );

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_semantic_boundary_type_checks(
        &result,
        "single concrete LRA boundary semantic trust proof",
    );
}

#[test]
fn test_lra_boundary_concrete_subset_additive_semantic_boundary_type_checks() {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let three = register_int_const_as_var(&mut terms, &mut map, "const3", 3);
    let two = register_int_const_as_var(&mut terms, &mut map, "const2", 2);
    let five = register_int_const_as_var(&mut terms, &mut map, "const5", 5);
    let four = register_int_const_as_var(&mut terms, &mut map, "const4", 4);
    let x = register_int_var(&mut terms, &mut map, "fvar_31", 31);
    let y = register_int_var(&mut terms, &mut map, "fvar_32", 32);

    let le_3_2 = terms.mk_le(three, two);
    let le_5_4 = terms.mk_le(five, four);
    let le_xy = terms.mk_le(x, y);

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_farkas(
        "LRA",
        vec![
            terms.mk_not(le_3_2),
            terms.mk_not(le_5_4),
            terms.mk_not(le_xy),
        ],
        FarkasAnnotation::from_ints(&[1, 1, 1]),
    );

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_semantic_boundary_type_checks(
        &result,
        "concrete-subset additive LRA boundary semantic trust proof",
    );
}
