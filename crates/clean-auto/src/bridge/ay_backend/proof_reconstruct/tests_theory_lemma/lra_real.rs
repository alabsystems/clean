// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Real-sort chain, boundary, and cyclic LRA Farkas tests.
//!
//! Additive Real tests are in `lra_real_additive.rs`.

use super::support::boundary::assert_lra_trust_boundary;
use super::support::semantic::{mk_real_int_const, register_real_var};
use super::{
    attempt_reconstruction, Expr, ExprKind, FarkasAnnotation, Name, Proof, Sort, TermStore,
    VariableMapping,
};
use clean_kernel::Level;

pub(super) fn mk_real_ofnat_expr(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Real.ofNat"), vec![]),
        Expr::nat_lit(n),
    )
}

pub(super) fn mk_real_ofint_expr(int_expr: &Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Real.ofInt"), vec![]),
        int_expr.clone(),
    )
}

pub(super) fn mk_real_add_expr(a: &Expr, b: &Expr) -> Expr {
    super::expr_builders::mk_add(&Sort::Real, a, b)
}

pub(super) fn mk_le_real_prop(a: &Expr, b: &Expr) -> Expr {
    let real_ty = Expr::const_(Name::from_string("Real"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
                    real_ty,
                ),
                Expr::const_(Name::from_string("instLEReal"), vec![]),
            ),
            a.clone(),
        ),
        b.clone(),
    )
}

#[test]
fn test_theory_lemma_lra_farkas_real_lt_chain() {
    // Real sort strict inequality chain with symbolic endpoints must stop at
    // the trust boundary instead of synthesizing `trustedArith`.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let x = register_real_var(&mut terms, &mut map, "fvar_1", 1);
    let b = register_real_var(&mut terms, &mut map, "fvar_2", 2);
    let y = register_real_var(&mut terms, &mut map, "fvar_3", 3);

    let lt_xb = terms.mk_lt(x, b);
    let lt_by = terms.mk_lt(b, y);
    let not_lt_xb = terms.mk_not(lt_xb);
    let not_lt_by = terms.mk_not(lt_by);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_lt_xb, not_lt_by], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_lra_trust_boundary(&result, 0);
}

#[test]
fn test_theory_lemma_lra_farkas_real_mixed_le_lt_chain() {
    // Real sort mixed chain with symbolic endpoints must stop at the trust
    // boundary instead of synthesizing `trustedArith`.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let x = register_real_var(&mut terms, &mut map, "fvar_1", 1);
    let b = register_real_var(&mut terms, &mut map, "fvar_2", 2);
    let y = register_real_var(&mut terms, &mut map, "fvar_3", 3);

    let le_xb = terms.mk_le(x, b);
    let lt_by = terms.mk_lt(b, y);
    let not_le_xb = terms.mk_not(le_xb);
    let not_lt_by = terms.mk_not(lt_by);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_xb, not_lt_by], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_lra_trust_boundary(&result, 0);
}

#[test]
fn test_theory_lemma_lra_farkas_real_three_bound_chain() {
    // Real sort 3-bound chain: x ≤ b, b ≤ c, c ≤ y → x ≤ y via iterated
    // Real.le_trans.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let x = register_real_var(&mut terms, &mut map, "fvar_1", 1);
    let b = register_real_var(&mut terms, &mut map, "fvar_2", 2);
    let c = register_real_var(&mut terms, &mut map, "fvar_3", 3);
    let y = register_real_var(&mut terms, &mut map, "fvar_4", 4);

    let le_xb = terms.mk_le(x, b);
    let le_bc = terms.mk_le(b, c);
    let le_cy = terms.mk_le(c, y);
    let not_le_xb = terms.mk_not(le_xb);
    let not_le_bc = terms.mk_not(le_bc);
    let not_le_cy = terms.mk_not(le_cy);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_xb, not_le_bc, not_le_cy], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_lra_trust_boundary(&result, 0);
}

#[test]
fn test_theory_lemma_lra_farkas_real_concrete_chain() {
    // Real-sort chain with concrete integer-valued Rational endpoints.
    // Bounds: 5 ≤ x (Real), x ≤ 3 (Real) → chain: 5 ≤ x ≤ 3 → 5 ≤ 3 (violated).
    // Uses Constant::Rational for the numeric constants.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let x = register_real_var(&mut terms, &mut map, "fvar_1", 1);
    let five = mk_real_int_const(&mut terms, 5);
    let three = mk_real_int_const(&mut terms, 3);

    let le_5x = terms.mk_le(five, x);
    let le_x3 = terms.mk_le(x, three);
    let not_le_5x = terms.mk_not(le_5x);
    let not_le_x3 = terms.mk_not(le_x3);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_5x, not_le_x3], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(
        result.stats.reconstructed_steps, 1,
        "Real-sort Rational concrete chain should reconstruct, error: {:?}",
        result.stats.error,
    );
    assert!(
        result.proof_term.is_some(),
        "Real Rational concrete chain should produce a proof term"
    );
}

#[test]
fn test_theory_lemma_lra_farkas_real_cyclic_lt_irrefl() {
    // Real-sort cyclic chain with strict inequality.
    // Bounds: x < y (Real), y ≤ x (Real) → cycle: x < y ≤ x → x < x.
    // Should use lt_irrefl (Real.lt_irrefl) to close, not trustedArith.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let x = register_real_var(&mut terms, &mut map, "fvar_1", 1);
    let y = register_real_var(&mut terms, &mut map, "fvar_2", 2);

    let lt_xy = terms.mk_lt(x, y);
    let le_yx = terms.mk_le(y, x);
    let not_lt_xy = terms.mk_not(lt_xy);
    let not_le_yx = terms.mk_not(le_yx);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_lt_xy, not_le_yx], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_eq!(
        result.stats.reconstructed_steps, 1,
        "Real cyclic Lt chain should reconstruct, error: {:?}",
        result.stats.error,
    );
    let proof_term = result
        .proof_term
        .expect("Real cyclic Lt chain should produce a proof term");

    fn contains_lt_irrefl(e: &Expr) -> bool {
        match e.kind() {
            ExprKind::Const(name, _) => name.to_string() == "Real.lt_irrefl",
            ExprKind::App(f, a) => contains_lt_irrefl(f) || contains_lt_irrefl(a),
            ExprKind::Lam(_, ty, body) => contains_lt_irrefl(ty) || contains_lt_irrefl(body),
            ExprKind::Pi(_, ty, body) => contains_lt_irrefl(ty) || contains_lt_irrefl(body),
            _ => false,
        }
    }
    assert!(
        contains_lt_irrefl(&proof_term),
        "Real cyclic Lt chain should use Real.lt_irrefl, not trustedArith"
    );
}

#[test]
fn test_theory_lemma_lra_farkas_real_non_chaining_trust_boundary() {
    // Real-sort non-chaining bounds.
    // Bounds: x ≤ a (Real), b ≤ y (Real) — no shared intermediate term.
    // These now stop at the LRA trust boundary.
    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let x = register_real_var(&mut terms, &mut map, "fvar_1", 1);
    let a = register_real_var(&mut terms, &mut map, "fvar_2", 2);
    let b = register_real_var(&mut terms, &mut map, "fvar_3", 3);
    let y = register_real_var(&mut terms, &mut map, "fvar_4", 4);

    let le_xa = terms.mk_le(x, a);
    let le_by = terms.mk_le(b, y);
    let not_le_xa = terms.mk_not(le_xa);
    let not_le_by = terms.mk_not(le_by);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_xa, not_le_by], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_lra_trust_boundary(&result, 0);
}
