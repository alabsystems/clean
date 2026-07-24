// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! NF closeout tests for LRA Farkas reconstruction (Part of #2422).
//!
//! Tests that symbolic additive endpoints (Int and Real) are closed via
//! normal-form cancellation instead of falling through to the trust
//! boundary. Covers both 2-bound chain NF and N-bound additive NF.

use super::support::boundary::assert_lra_trust_boundary;
use super::support::semantic::{register_int_var, register_real_var};
use super::{
    attempt_reconstruction, expr_builders, Expr, FarkasAnnotation, Name, Proof, Sort, TermStore,
    VariableMapping,
};

fn register_int_expr_as_var(
    terms: &mut TermStore,
    map: &mut VariableMapping,
    name: &str,
    expr: Expr,
) -> ay_core::TermId {
    let tid = terms.mk_var(name, Sort::Int);
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    map.register_var(name, expr, int_ty);
    tid
}

fn register_real_expr_as_var(
    terms: &mut TermStore,
    map: &mut VariableMapping,
    name: &str,
    expr: Expr,
) -> ay_core::TermId {
    let tid = terms.mk_var(name, Sort::Real);
    let real_ty = Expr::const_(Name::from_string("Real"), vec![]);
    map.register_var(name, expr, real_ty);
    tid
}

/// Two-bound Int chain with symbolic additive endpoints — NF closeout
/// cancels the shared variable to expose a concrete contradiction.
///
/// Bounds: (x + 3) ≤ y, y ≤ (x + 1)
/// Chain:  (x + 3) ≤ (x + 1)
/// NF:    cancel x → 3 ≤ 1 → contradiction
///
/// Part of #2422.
#[test]
fn test_theory_lemma_lra_farkas_int_chain_symbolic_additive_nf_closeout() {
    let int_add = Expr::const_(Name::from_string("Int.add"), vec![]);
    let int_ofnat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);

    let x_expr = Expr::fvar(clean_kernel::FVarId::new(1));
    let three_expr = Expr::app(int_ofnat.clone(), Expr::nat_lit(3));
    let one_expr = Expr::app(int_ofnat, Expr::nat_lit(1));

    // x + 3
    let x_plus_3 = Expr::app(Expr::app(int_add.clone(), x_expr.clone()), three_expr);
    // x + 1
    let x_plus_1 = Expr::app(Expr::app(int_add, x_expr), one_expr);

    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let x_plus_3_tid = register_int_expr_as_var(&mut terms, &mut map, "xp3", x_plus_3);
    let y = register_int_var(&mut terms, &mut map, "fvar_42", 42);
    let x_plus_1_tid = register_int_expr_as_var(&mut terms, &mut map, "xp1", x_plus_1);

    let le_xp3_y = terms.mk_le(x_plus_3_tid, y);
    let le_y_xp1 = terms.mk_le(y, x_plus_1_tid);
    let not_le_xp3_y = terms.mk_not(le_xp3_y);
    let not_le_y_xp1 = terms.mk_not(le_y_xp1);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_xp3_y, not_le_y_xp1], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_lra_trust_boundary(&result, 0);
}

/// Two-bound Real chain with symbolic additive endpoints — NF closeout
/// downcasts to Int and cancels the shared variable to expose a concrete
/// contradiction.
///
/// Bounds: Real.ofNat(x) + Real.ofNat(3) ≤ y, y ≤ Real.ofNat(x) + Real.ofNat(1)
/// Chain:  (Real.ofNat(x) + Real.ofNat(3)) ≤ (Real.ofNat(x) + Real.ofNat(1))
/// Downcast to Int: (Int.ofNat(x) + Int.ofNat(3)) ≤ (Int.ofNat(x) + Int.ofNat(1))
/// NF: cancel Int.ofNat(x) → 3 ≤ 1 → contradiction
///
/// Part of #2422.
#[test]
fn test_theory_lemma_lra_farkas_real_chain_symbolic_additive_nf_closeout() {
    let real_ofnat = |n: u64| -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Real.ofNat"), vec![]),
            Expr::nat_lit(n),
        )
    };

    let x_real = Expr::app(
        Expr::const_(Name::from_string("Real.ofNat"), vec![]),
        Expr::fvar(clean_kernel::FVarId::new(1)),
    );

    // Build Real.ofNat(x) + Real.ofNat(3) and Real.ofNat(x) + Real.ofNat(1)
    // using the standard HAdd.hAdd builder so decompose_real_add recognizes them.
    let x_plus_3 = expr_builders::mk_add(&Sort::Real, &x_real, &real_ofnat(3));
    let x_plus_1 = expr_builders::mk_add(&Sort::Real, &x_real, &real_ofnat(1));

    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let xp3_tid = register_real_expr_as_var(&mut terms, &mut map, "xp3", x_plus_3);
    let y = register_real_var(&mut terms, &mut map, "fvar_42", 42);
    let xp1_tid = register_real_expr_as_var(&mut terms, &mut map, "xp1", x_plus_1);

    let le_xp3_y = terms.mk_le(xp3_tid, y);
    let le_y_xp1 = terms.mk_le(y, xp1_tid);
    let not_le_xp3_y = terms.mk_not(le_xp3_y);
    let not_le_y_xp1 = terms.mk_not(le_y_xp1);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le_xp3_y, not_le_y_xp1], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_lra_trust_boundary(&result, 0);
}

/// Four-bound Int cyclic additive system — NF closeout cancels all four
/// shared variables to expose a concrete contradiction.
///
/// Bounds: (x+5) ≤ y, (y+3) ≤ z, (z+2) ≤ w, w ≤ x
/// Additive combination (all coefficient 1):
///   LHS = (x+5) + (y+3) + (z+2) + w = x+y+z+w+10
///   RHS = y + z + w + x             = x+y+z+w
///   NF: cancel {x,y,z,w} → 10 ≤ 0 → contradiction
///
/// Part of #2422.
#[test]
fn test_theory_lemma_lra_farkas_int_4bound_additive_nf_full_cancellation() {
    let int_add = Expr::const_(Name::from_string("Int.add"), vec![]);
    let int_ofnat = Expr::const_(Name::from_string("Int.ofNat"), vec![]);

    let x_expr = Expr::fvar(clean_kernel::FVarId::new(1));
    let y_expr = Expr::fvar(clean_kernel::FVarId::new(2));
    let z_expr = Expr::fvar(clean_kernel::FVarId::new(3));

    let five_expr = Expr::app(int_ofnat.clone(), Expr::nat_lit(5));
    let three_expr = Expr::app(int_ofnat.clone(), Expr::nat_lit(3));
    let two_expr = Expr::app(int_ofnat, Expr::nat_lit(2));

    // Composite endpoint expressions: x+5, y+3, z+2
    let x_plus_5 = Expr::app(Expr::app(int_add.clone(), x_expr.clone()), five_expr);
    let y_plus_3 = Expr::app(Expr::app(int_add.clone(), y_expr.clone()), three_expr);
    let z_plus_2 = Expr::app(Expr::app(int_add, z_expr.clone()), two_expr);

    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    // Register ay variables for composite endpoints
    let xp5 = register_int_expr_as_var(&mut terms, &mut map, "xp5", x_plus_5);
    let yp3 = register_int_expr_as_var(&mut terms, &mut map, "yp3", y_plus_3);
    let zp2 = register_int_expr_as_var(&mut terms, &mut map, "zp2", z_plus_2);

    // Register ay variables for plain fvar endpoints
    let y = register_int_var(&mut terms, &mut map, "fvar_y", 2);
    let z = register_int_var(&mut terms, &mut map, "fvar_z", 3);
    let w = register_int_var(&mut terms, &mut map, "fvar_w", 4);
    let x = register_int_var(&mut terms, &mut map, "fvar_x", 1);

    // Bounds: (x+5) ≤ y, (y+3) ≤ z, (z+2) ≤ w, w ≤ x
    let le1 = terms.mk_le(xp5, y);
    let le2 = terms.mk_le(yp3, z);
    let le3 = terms.mk_le(zp2, w);
    let le4 = terms.mk_le(w, x);
    let not_le1 = terms.mk_not(le1);
    let not_le2 = terms.mk_not(le2);
    let not_le3 = terms.mk_not(le3);
    let not_le4 = terms.mk_not(le4);

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[1, 1, 1, 1]);
    proof.add_theory_lemma_with_farkas("LRA", vec![not_le1, not_le2, not_le3, not_le4], farkas);

    let negated_goal = Expr::const_(Name::from_string("_neg_goal"), vec![]);
    let result = attempt_reconstruction(&proof, &terms, &map, &negated_goal);

    assert_lra_trust_boundary(&result, 0);
}
