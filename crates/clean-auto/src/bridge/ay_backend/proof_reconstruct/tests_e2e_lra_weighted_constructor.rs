// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! E2E regression coverage for weighted symbolic Real LRA replay when concrete
//! constants arrive in constructor form (`Real.ofNat (Nat.succ ...)`).
//!
//! Part of #2422.

use super::tests_e2e_lra::mk_le_real;
use super::{attempt_reconstruction, VariableMapping};
use ay::Sort;
use ay_core::{FarkasAnnotation, Proof, TermStore};
use clean_kernel::name::Name;
use clean_kernel::{Expr, FVarId};

fn negated_false_goal() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Not"), vec![]),
        Expr::const_(Name::from_string("False"), vec![]),
    )
}

fn mk_real_add_expr(a: &Expr, b: &Expr) -> Expr {
    super::expr_builders::mk_add(&Sort::Real, a, b)
}

fn mk_real_ofint_expr(a: &Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Real.ofInt"), vec![]),
        a.clone(),
    )
}

fn mk_constructor_nat(n: u64) -> Expr {
    let mut nat = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    for _ in 0..n {
        nat = Expr::app(Expr::const_(Name::from_string("Nat.succ"), vec![]), nat);
    }
    nat
}

fn mk_constructor_real_ofnat(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Real.ofNat"), vec![]),
        mk_constructor_nat(n),
    )
}

fn mk_constructor_weighted_symbolic_real_lra_ay_proof() -> (
    TermStore,
    VariableMapping,
    Proof,
    Vec<(FVarId, &'static str, Expr)>,
) {
    let real_ty = Expr::const_(Name::from_string("Real"), vec![]);
    let four_real = mk_constructor_real_ofnat(4);
    let one_real = mk_constructor_real_ofnat(1);
    let two_real = mk_constructor_real_ofnat(2);
    let test_x = mk_real_ofint_expr(&Expr::const_(Name::from_string("testXI"), vec![]));
    let test_y = mk_real_ofint_expr(&Expr::const_(Name::from_string("testYI"), vec![]));

    let mut terms = TermStore::new();
    let mut map = VariableMapping::new();

    let ay_four = terms.mk_var("const4", Sort::Real);
    let ay_one = terms.mk_var("const1", Sort::Real);
    let ay_two = terms.mk_var("const2", Sort::Real);
    let ay_x = terms.mk_var("testX", Sort::Real);
    let ay_y = terms.mk_var("testY", Sort::Real);

    map.register_var("const4", four_real.clone(), real_ty.clone());
    map.register_var("const1", one_real.clone(), real_ty.clone());
    map.register_var("const2", two_real.clone(), real_ty.clone());
    map.register_var("testX", test_x.clone(), real_ty.clone());
    map.register_var("testY", test_y.clone(), real_ty.clone());

    let ay_x_plus_y = terms.mk_add(vec![ay_x, ay_y]);
    let le_4_xy = terms.mk_le(ay_four, ay_x_plus_y);
    let le_x_1_a = terms.mk_le(ay_x, ay_one);
    let le_x_1_b = terms.mk_le(ay_x, ay_one);
    let le_y_2_a = terms.mk_le(ay_y, ay_two);
    let le_y_2_b = terms.mk_le(ay_y, ay_two);
    let not_le_4_xy = terms.mk_not(le_4_xy);
    let not_le_x_1_a = terms.mk_not(le_x_1_a);
    let not_le_x_1_b = terms.mk_not(le_x_1_b);
    let not_le_y_2_a = terms.mk_not(le_y_2_a);
    let not_le_y_2_b = terms.mk_not(le_y_2_b);

    let le_4_xy_prop = mk_le_real(&four_real, &mk_real_add_expr(&test_x, &test_y));
    let le_x_1_prop = mk_le_real(&test_x, &one_real);
    let le_y_2_prop = mk_le_real(&test_y, &two_real);

    let h1_id = FVarId::new(10);
    let h2_id = FVarId::new(11);
    let h3_id = FVarId::new(12);
    let h4_id = FVarId::new(13);
    let h5_id = FVarId::new(14);
    map.register_hypothesis("h_4_le_xy", h1_id, Expr::fvar(h1_id), le_4_xy_prop.clone());
    map.register_hypothesis("h_x_le_1_a", h2_id, Expr::fvar(h2_id), le_x_1_prop.clone());
    map.register_hypothesis("h_x_le_1_b", h3_id, Expr::fvar(h3_id), le_x_1_prop.clone());
    map.register_hypothesis("h_y_le_2_a", h4_id, Expr::fvar(h4_id), le_y_2_prop.clone());
    map.register_hypothesis("h_y_le_2_b", h5_id, Expr::fvar(h5_id), le_y_2_prop.clone());

    let mut proof = Proof::new();
    let farkas = FarkasAnnotation::from_ints(&[2, 1, 1, 1, 1]);
    let s0 = proof.add_theory_lemma_with_farkas(
        "LRA",
        vec![
            not_le_4_xy,
            not_le_x_1_a,
            not_le_x_1_b,
            not_le_y_2_a,
            not_le_y_2_b,
        ],
        farkas,
    );
    let s1 = proof.add_assume(le_4_xy, None);
    let s2 = proof.add_resolution(
        vec![not_le_x_1_a, not_le_x_1_b, not_le_y_2_a, not_le_y_2_b],
        not_le_4_xy,
        s0,
        s1,
    );
    let s3 = proof.add_assume(le_x_1_a, None);
    let s4 = proof.add_resolution(
        vec![not_le_x_1_b, not_le_y_2_a, not_le_y_2_b],
        not_le_x_1_a,
        s2,
        s3,
    );
    let s5 = proof.add_assume(le_x_1_b, None);
    let s6 = proof.add_resolution(vec![not_le_y_2_a, not_le_y_2_b], not_le_x_1_b, s4, s5);
    let s7 = proof.add_assume(le_y_2_a, None);
    let s8 = proof.add_resolution(vec![not_le_y_2_b], not_le_y_2_a, s6, s7);
    let s9 = proof.add_assume(le_y_2_b, None);
    proof.add_resolution(vec![], not_le_y_2_b, s8, s9);

    let hyps = vec![
        (h1_id, "h_4_le_xy", le_4_xy_prop),
        (h2_id, "h_x_le_1_a", le_x_1_prop.clone()),
        (h3_id, "h_x_le_1_b", le_x_1_prop),
        (h4_id, "h_y_le_2_a", le_y_2_prop.clone()),
        (h5_id, "h_y_le_2_b", le_y_2_prop),
    ];
    (terms, map, proof, hyps)
}

#[test]
fn test_e2e_weighted_symbolic_real_lra_constructor_form_constants_type_check() {
    let (terms, map, proof, _hyps) = mk_constructor_weighted_symbolic_real_lra_ay_proof();
    let neg_goal = negated_false_goal();
    let result = attempt_reconstruction(&proof, &terms, &map, &neg_goal);
    assert_eq!(
        result.stats.trust_boundary_steps, 1,
        "theory lemma should hit trust boundary: {:?}",
        result.stats
    );
    assert!(
        result.trust_subterm_count > 0,
        "proof should carry trust debt from the synthesized trust sub-term"
    );
}
