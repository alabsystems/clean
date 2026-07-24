// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-level type checking tests for LRA Farkas reconstructed proofs.
//!
//! These tests verify that proof terms produced by the LRA Farkas chain
//! reconstructor (for concretely contradictory bounds) actually type-check in
//! the kernel via `TypeChecker::infer_type`.

use super::super::expr_builders_arith::CmpOp;
use super::super::tests_e2e_lra::{mk_le_real, mk_lt_real, mk_real_int_const_expr, mk_real_ofnat};
use super::super::theory_lemma_lra::ActiveBound;
use super::super::theory_lemma_lra_chain::BoundInfo;
use super::super::theory_lemma_lra_weighted::build_weighted_additive_false;
use super::support::boundary::assert_lra_trust_boundary;
use super::support::kernel::{
    assert_lra_proof_type_checks_to_false, mk_lra_kernel_env, mk_real_lra_kernel_env,
};
use super::support::semantic::{mk_raw_le, register_int_const};
use super::{
    attempt_reconstruction, Expr, FVarId, FarkasAnnotation, Name, Proof, ReconstructionError, Sort,
    TermStore, VariableMapping,
};

fn mk_le_int(lhs: &Expr, rhs: &Expr) -> Expr {
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(
                        Name::from_string("LE.le"),
                        vec![clean_kernel::Level::zero()],
                    ),
                    int_ty,
                ),
                Expr::const_(Name::from_string("instLEInt"), vec![]),
            ),
            lhs.clone(),
        ),
        rhs.clone(),
    )
}

fn mk_real_bound(op: CmpOp, lhs_expr: Expr, rhs_expr: Expr) -> BoundInfo {
    BoundInfo {
        sort: Sort::Real,
        op,
        lhs_term: ay_core::TermId(0),
        rhs_term: ay_core::TermId(1),
        lhs_expr,
        rhs_expr,
    }
}

fn instantiate_clause_hypotheses(expr: &Expr, clause_hyps: &[FVarId]) -> Expr {
    clause_hyps
        .iter()
        .rev()
        .fold(expr.clone(), |acc, id| acc.instantiate(&Expr::fvar(*id)))
}

fn mk_symbolic_lra_resolution_chain_case() -> (
    TermStore,
    VariableMapping,
    Proof,
    Vec<(FVarId, &'static str, Expr)>,
) {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);

    let a_id = FVarId::new(1);
    let b_id = FVarId::new(2);
    let c_id = FVarId::new(3);
    let d_id = FVarId::new(4);
    let h_ab_id = FVarId::new(11);
    let h_cd_id = FVarId::new(12);

    let a_expr = Expr::fvar(a_id);
    let b_expr = Expr::fvar(b_id);
    let c_expr = Expr::fvar(c_id);
    let d_expr = Expr::fvar(d_id);

    let a = terms.mk_var("fvar_1", Sort::Int);
    let b = terms.mk_var("fvar_2", Sort::Int);
    let c = terms.mk_var("fvar_3", Sort::Int);
    let d = terms.mk_var("fvar_4", Sort::Int);

    map.register_var("fvar_1", a_expr.clone(), int_ty.clone());
    map.register_var("fvar_2", b_expr.clone(), int_ty.clone());
    map.register_var("fvar_3", c_expr.clone(), int_ty.clone());
    map.register_var("fvar_4", d_expr.clone(), int_ty.clone());

    let le_ab = terms.mk_le(a, b);
    let le_cd = terms.mk_le(c, d);
    let not_le_ab = terms.mk_not(le_ab);
    let not_le_cd = terms.mk_not(le_cd);

    let le_ab_prop = mk_le_int(&a_expr, &b_expr);
    let le_cd_prop = mk_le_int(&c_expr, &d_expr);
    map.register_hypothesis("h_ab", h_ab_id, Expr::fvar(h_ab_id), le_ab_prop.clone());
    map.register_hypothesis("h_cd", h_cd_id, Expr::fvar(h_cd_id), le_cd_prop.clone());

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    let s0 = proof.add_theory_lemma_with_farkas("LRA", vec![not_le_ab, not_le_cd], farkas);
    let s1 = proof.add_assume(le_ab, None);
    let s2 = proof.add_resolution(vec![not_le_cd], not_le_ab, s0, s1);
    let s3 = proof.add_assume(le_cd, None);
    proof.add_resolution(vec![], not_le_cd, s2, s3);

    (
        terms,
        map,
        proof,
        vec![
            (a_id, "a", int_ty.clone()),
            (b_id, "b", int_ty.clone()),
            (c_id, "c", int_ty.clone()),
            (d_id, "d", int_ty),
            (h_ab_id, "h_ab", le_ab_prop),
            (h_cd_id, "h_cd", le_cd_prop),
        ],
    )
}

fn assert_symbolic_lra_resolution_chain_stats(result: &super::super::ReconstructionResult) {
    assert_eq!(result.stats.total_steps, 5);
    assert_eq!(result.stats.theory_lemma_steps, 1);
    assert_eq!(result.stats.resolution_steps, 2);
    assert_eq!(
        result.stats.reconstructed_steps, 4,
        "symbolic-endpoint LRA should reconstruct both assumes and both resolutions, error: {:?}",
        result.stats.error,
    );
    assert_eq!(
        result.stats.trust_boundary_steps, 1,
        "only the LRA theory lemma should stop at the trust boundary"
    );
    assert_eq!(
        result.stats.trust_fallback_steps, 1,
        "only the LRA theory lemma should use the trust fallback lane"
    );
    assert_eq!(
        result.trust_subterm_count, 1,
        "the final proof should carry exactly one trusted sub-term for the theory lemma"
    );
    assert!(
        result.derives_empty_clause,
        "final step should derive the empty clause"
    );
    let diagnostic = result
        .stats
        .first_diagnostic
        .as_ref()
        .expect("symbolic-endpoint trust boundary should record first_diagnostic");
    assert_eq!(diagnostic.step_index, Some(0));
    assert!(
        matches!(&diagnostic.error, ReconstructionError::TrustBoundary { .. }),
        "expected the theory lemma trust boundary to be recorded first, got {:?}",
        diagnostic.error
    );
}

/// LRA Farkas with concrete contradictory endpoints: `5 ≤ x, x ≤ 3` → chain
/// closes because `5 > 3`. The proof term should type-check in the kernel.
#[test]
fn test_lra_farkas_concrete_chain_type_checks_in_kernel() {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let five = register_int_const(&mut terms, &mut map, "const5", 5);
    let x = {
        let tid = terms.mk_var("fvar_1", Sort::Int);
        let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
        map.register_var("fvar_1", Expr::fvar(FVarId::new(1)), int_ty);
        tid
    };
    let three = register_int_const(&mut terms, &mut map, "const3", 3);

    let le_5x = mk_raw_le(&mut terms, five, x);
    let le_x3 = mk_raw_le(&mut terms, x, three);
    let not_le_5x = terms.mk_not(le_5x);
    let not_le_x3 = terms.mk_not(le_x3);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    let s0 = proof.add_theory_lemma_with_farkas("LRA", vec![not_le_5x, not_le_x3], farkas);
    let s1 = proof.add_assume(le_5x, None);
    let s2 = proof.add_resolution(vec![not_le_x3], not_le_5x, s0, s1);
    let s3 = proof.add_assume(le_x3, None);
    proof.add_resolution(vec![], not_le_x3, s2, s3);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    // With native ay constants, the theory lemma now fully reconstructs:
    // the chain 5 ≤ x ≤ 3 has variable x eliminated (coeff [1,1]) and
    // concrete endpoints 5 > 3. All 5 steps reconstruct.
    assert_eq!(result.stats.total_steps, 5);
    assert_eq!(
        result.stats.reconstructed_steps, 5,
        "all steps should reconstruct with native constants, error: {:?}",
        result.stats.error,
    );
    assert_eq!(
        result.stats.trust_boundary_steps, 0,
        "no trust boundary with native constants"
    );
    assert_eq!(
        result.stats.trust_fallback_steps, 0,
        "no trust fallback with native constants"
    );
    assert!(
        result.derives_empty_clause,
        "final step should derive empty clause"
    );
    assert!(
        result.proof_term.is_some(),
        "concrete Farkas chain should produce a proof term"
    );
}

/// LRA Farkas with non-unit coefficients [2, 1] on `5 ≤ x, x ≤ 3`:
/// x has net coefficient +2 - 1 = +1 → doesn't eliminate → trust boundary.
#[test]
fn test_lra_farkas_non_unit_coefficients_semantic_boundary_type_checks_in_kernel() {
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let five = register_int_const(&mut terms, &mut map, "const5", 5);
    let x = {
        let tid = terms.mk_var("fvar_1", Sort::Int);
        let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
        map.register_var("fvar_1", Expr::fvar(FVarId::new(1)), int_ty);
        tid
    };
    let three = register_int_const(&mut terms, &mut map, "const3", 3);

    let le_5x = mk_raw_le(&mut terms, five, x);
    let le_x3 = mk_raw_le(&mut terms, x, three);
    let not_le_5x = terms.mk_not(le_5x);
    let not_le_x3 = terms.mk_not(le_x3);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[2, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_5x, not_le_x3], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_lra_trust_boundary(&result, 0);
    let diagnostic = result
        .stats
        .first_diagnostic
        .as_ref()
        .expect("malformed non-unit chain should record first_diagnostic");
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
        "malformed non-unit chain should fail semantic validation, got {description:?}"
    );
    // After #2986, proof_term is None when reconstructed_steps == 0.
    assert!(
        result.proof_term.is_none(),
        "total-failure trust-boundary should not produce a proof term"
    );
}

/// LRA Farkas with symbolic endpoints still stops at the trust boundary, but
/// downstream resolution must keep producing a kernel-type-checking `False`
/// proof term that carries exactly one trusted sub-term for the theory lemma.
#[test]
fn test_lra_farkas_symbolic_endpoint_resolution_chain_type_checks_in_kernel() {
    let (terms, map, proof, local_ctx_entries) = mk_symbolic_lra_resolution_chain_case();
    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_symbolic_lra_resolution_chain_stats(&result);
    let proof_term = result
        .proof_term
        .expect("symbolic-endpoint LRA chain should still produce a proof term");
    let env = mk_lra_kernel_env();
    assert_lra_proof_type_checks_to_false(
        &env,
        &proof_term,
        &local_ctx_entries,
        "symbolic-endpoint LRA trust-boundary chain",
    );
}

#[test]
fn test_weighted_real_builder_non_negative_type_checks_to_false() {
    let left_lhs = mk_real_ofnat(4);
    let left_rhs = mk_real_ofnat(3);
    let right_lhs = mk_real_ofnat(0);
    let right_rhs = mk_real_ofnat(100);
    let left = mk_real_bound(CmpOp::Le, left_lhs.clone(), left_rhs.clone());
    let right = mk_real_bound(CmpOp::Le, right_lhs.clone(), right_rhs.clone());
    let bounds = [
        ActiveBound {
            clause_idx: 0,
            bound: &left,
        },
        ActiveBound {
            clause_idx: 1,
            bound: &right,
        },
    ];

    let false_proof = build_weighted_additive_false(&Sort::Real, &bounds, &[200, 1], 2)
        .expect("weighted Real builder should produce a contradiction proof");
    let h_left = FVarId::new(120);
    let h_right = FVarId::new(121);
    let instantiated = instantiate_clause_hypotheses(&false_proof, &[h_left, h_right]);

    let env = mk_real_lra_kernel_env();
    let local_ctx_entries = [
        (h_left, "h_4_le_3", mk_le_real(&left_lhs, &left_rhs)),
        (h_right, "h_0_le_100", mk_le_real(&right_lhs, &right_rhs)),
    ];
    assert_lra_proof_type_checks_to_false(
        &env,
        &instantiated,
        &local_ctx_entries,
        "weighted non-negative Real builder",
    );
}

#[test]
fn test_weighted_real_builder_mixed_sign_type_checks_to_false() {
    let left_lhs = mk_real_int_const_expr(3);
    let left_rhs = mk_real_int_const_expr(-1);
    let right_lhs = mk_real_int_const_expr(-2);
    let right_rhs = mk_real_int_const_expr(0);
    let left = mk_real_bound(CmpOp::Le, left_lhs.clone(), left_rhs.clone());
    let right = mk_real_bound(CmpOp::Lt, right_lhs.clone(), right_rhs.clone());
    let bounds = [
        ActiveBound {
            clause_idx: 0,
            bound: &left,
        },
        ActiveBound {
            clause_idx: 1,
            bound: &right,
        },
    ];

    let false_proof = build_weighted_additive_false(&Sort::Real, &bounds, &[2, 1], 2)
        .expect("mixed-sign weighted Real builder should produce a contradiction proof");
    let h_left = FVarId::new(122);
    let h_right = FVarId::new(123);
    let instantiated = instantiate_clause_hypotheses(&false_proof, &[h_left, h_right]);

    let env = mk_real_lra_kernel_env();
    let local_ctx_entries = [
        (h_left, "h_3_le_neg1", mk_le_real(&left_lhs, &left_rhs)),
        (h_right, "h_neg2_lt_0", mk_lt_real(&right_lhs, &right_rhs)),
    ];
    assert_lra_proof_type_checks_to_false(
        &env,
        &instantiated,
        &local_ctx_entries,
        "weighted mixed-sign Real builder",
    );
}
