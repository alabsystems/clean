// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{
    build_close_shape, combine_ops, combine_scaled_bounds, expr_contains_const, mk_int_add,
    mk_int_ofnat_expr, mk_var_expr, try_close_int_additive_nf, CmpOp, IntAddNf, Sort, SortCmpAcc,
};

#[test]
fn test_symbolic_int_additive_closeout_motivating_accumulator_reconstructs() {
    let x = mk_var_expr("x");
    let y = mk_var_expr("y");
    let h1 = mk_var_expr("h_4_le_xy");
    let h2 = mk_var_expr("h_x_le_1");
    let h3 = mk_var_expr("h_y_le_2");

    let mut accs = [
        SortCmpAcc {
            lhs: mk_int_ofnat_expr(4),
            rhs: mk_int_add(&x, &y),
            op: CmpOp::Le,
            proof: h1,
        },
        SortCmpAcc {
            lhs: x.clone(),
            rhs: mk_int_ofnat_expr(1),
            op: CmpOp::Le,
            proof: h2,
        },
        SortCmpAcc {
            lhs: y.clone(),
            rhs: mk_int_ofnat_expr(2),
            op: CmpOp::Le,
            proof: h3,
        },
    ];

    let combined = combine_scaled_bounds(&Sort::Int, &mut accs)
        .expect("motivating Int bounds should produce an additive accumulator");
    let lhs_nf = IntAddNf::from_expr(&combined.lhs);
    let rhs_nf = IntAddNf::from_expr(&combined.rhs);
    let shape = build_close_shape(&lhs_nf, &rhs_nf);

    assert_eq!(
        shape.shared.len(),
        2,
        "x and y should be cancellable suffix atoms"
    );
    assert!(
        shape.residual_is_concrete_contradiction(CmpOp::Le),
        "the residual 4 <= 3 contradiction should already be visible after cancellation"
    );
    let false_proof =
        try_close_int_additive_nf(combined.op, &combined.lhs, &combined.rhs, &combined.proof)
            .expect("symbolic closeout should reconstruct once proof transport lands");
    assert!(expr_contains_const(
        &false_proof,
        "Int.le_of_add_le_add_right"
    ));
    assert!(expr_contains_const(&false_proof, "Int.NonNeg.casesOn"));
}

#[test]
fn test_combine_ops_le_le_is_le() {
    assert_eq!(combine_ops(CmpOp::Le, CmpOp::Le), CmpOp::Le);
}

#[test]
fn test_combine_ops_le_lt_is_lt() {
    assert_eq!(combine_ops(CmpOp::Le, CmpOp::Lt), CmpOp::Lt);
}

#[test]
fn test_combine_ops_lt_le_is_lt() {
    assert_eq!(combine_ops(CmpOp::Lt, CmpOp::Le), CmpOp::Lt);
}

#[test]
fn test_combine_ops_lt_lt_is_lt() {
    assert_eq!(combine_ops(CmpOp::Lt, CmpOp::Lt), CmpOp::Lt);
}

#[test]
fn test_combine_scaled_bounds_rejects_single_accumulator() {
    let mut accs = [SortCmpAcc {
        lhs: mk_int_ofnat_expr(1),
        rhs: mk_int_ofnat_expr(2),
        op: CmpOp::Le,
        proof: mk_var_expr("h"),
    }];
    assert!(
        combine_scaled_bounds(&Sort::Int, &mut accs).is_none(),
        "a single accumulator violates the len >= 2 precondition"
    );
}

#[test]
fn test_combine_scaled_bounds_rejects_empty_slice() {
    let mut accs: [SortCmpAcc; 0] = [];
    assert!(
        combine_scaled_bounds(&Sort::Int, &mut accs).is_none(),
        "an empty slice violates the len >= 2 precondition"
    );
}

#[test]
fn test_combine_scaled_bounds_two_le_produces_additive_le() {
    let four = mk_int_ofnat_expr(4);
    let two = mk_int_ofnat_expr(2);
    let x = mk_var_expr("x");
    let y = mk_var_expr("y");

    let mut accs = [
        SortCmpAcc {
            lhs: four.clone(),
            rhs: x.clone(),
            op: CmpOp::Le,
            proof: mk_var_expr("h0"),
        },
        SortCmpAcc {
            lhs: y.clone(),
            rhs: two.clone(),
            op: CmpOp::Le,
            proof: mk_var_expr("h1"),
        },
    ];

    let combined =
        combine_scaled_bounds(&Sort::Int, &mut accs).expect("two Le accumulators must combine");

    assert_eq!(combined.lhs, mk_int_add(&y, &four));
    assert_eq!(combined.rhs, mk_int_add(&two, &x));
    assert_eq!(combined.op, CmpOp::Le, "Le + Le must produce Le");
    assert!(
        expr_contains_const(&combined.proof, "Int.le_trans")
            || expr_contains_const(&combined.proof, "Int.add_le_add_left")
            || expr_contains_const(&combined.proof, "Int.add_le_add_right"),
        "combined proof must contain additive transitivity lemmas"
    );
}

#[test]
fn test_combine_scaled_bounds_three_accs_extends_iteration() {
    let a0 = mk_var_expr("a0");
    let b0_ = mk_var_expr("b0");
    let a1 = mk_var_expr("a1");
    let b1_ = mk_var_expr("b1");
    let a2 = mk_var_expr("a2");
    let b2_ = mk_var_expr("b2");

    let mut accs = [
        SortCmpAcc {
            lhs: a0.clone(),
            rhs: b0_.clone(),
            op: CmpOp::Le,
            proof: mk_var_expr("h0"),
        },
        SortCmpAcc {
            lhs: a1.clone(),
            rhs: b1_.clone(),
            op: CmpOp::Le,
            proof: mk_var_expr("h1"),
        },
        SortCmpAcc {
            lhs: a2.clone(),
            rhs: b2_.clone(),
            op: CmpOp::Le,
            proof: mk_var_expr("h2"),
        },
    ];

    let combined =
        combine_scaled_bounds(&Sort::Int, &mut accs).expect("three Le accumulators must combine");

    let base_lhs = mk_int_add(&a1, &a0);
    assert_eq!(combined.lhs, mk_int_add(&base_lhs, &a2));
    let base_rhs = mk_int_add(&b1_, &b0_);
    assert_eq!(combined.rhs, mk_int_add(&base_rhs, &b2_));
    assert_eq!(combined.op, CmpOp::Le);
}

#[test]
fn test_combine_scaled_bounds_mixed_le_lt_produces_lt() {
    let mut accs = [
        SortCmpAcc {
            lhs: mk_int_ofnat_expr(1),
            rhs: mk_int_ofnat_expr(2),
            op: CmpOp::Le,
            proof: mk_var_expr("h_le"),
        },
        SortCmpAcc {
            lhs: mk_int_ofnat_expr(3),
            rhs: mk_int_ofnat_expr(4),
            op: CmpOp::Lt,
            proof: mk_var_expr("h_lt"),
        },
    ];

    let combined =
        combine_scaled_bounds(&Sort::Int, &mut accs).expect("Le + Lt accumulators must combine");

    assert_eq!(combined.op, CmpOp::Lt, "Le + Lt must produce Lt");
}

#[test]
fn test_combine_scaled_bounds_lt_lt_produces_lt() {
    let mut accs = [
        SortCmpAcc {
            lhs: mk_int_ofnat_expr(5),
            rhs: mk_int_ofnat_expr(3),
            op: CmpOp::Lt,
            proof: mk_var_expr("h_lt_0"),
        },
        SortCmpAcc {
            lhs: mk_int_ofnat_expr(7),
            rhs: mk_int_ofnat_expr(1),
            op: CmpOp::Lt,
            proof: mk_var_expr("h_lt_1"),
        },
    ];

    let combined =
        combine_scaled_bounds(&Sort::Int, &mut accs).expect("Lt + Lt accumulators must combine");

    assert_eq!(combined.op, CmpOp::Lt, "Lt + Lt must produce Lt");
}

#[test]
fn test_combine_scaled_bounds_unsupported_sort_returns_none() {
    let mut accs = [
        SortCmpAcc {
            lhs: mk_var_expr("p"),
            rhs: mk_var_expr("q"),
            op: CmpOp::Le,
            proof: mk_var_expr("hp"),
        },
        SortCmpAcc {
            lhs: mk_var_expr("r"),
            rhs: mk_var_expr("s"),
            op: CmpOp::Le,
            proof: mk_var_expr("hr"),
        },
    ];

    assert!(
        combine_scaled_bounds(&Sort::Bool, &mut accs).is_none(),
        "Bool sort should fail closed (no additive combination defined)"
    );
}
