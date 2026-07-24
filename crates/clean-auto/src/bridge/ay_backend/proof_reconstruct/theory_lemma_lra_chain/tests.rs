// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::bridge::ay_backend::proof_reconstruct::VariableMapping;
use ay::Sort;
use ay_core::TermStore;
use clean_kernel::name::Name;
use clean_kernel::ExprKind;

use super::*;

fn mk_expr(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn mk_bound(lhs_term: u32, rhs_term: u32, label: &str) -> BoundInfo {
    BoundInfo {
        sort: Sort::Int,
        op: CmpOp::Le,
        lhs_term: TermId(lhs_term),
        rhs_term: TermId(rhs_term),
        lhs_expr: mk_expr(&format!("lhs_{label}")),
        rhs_expr: mk_expr(&format!("rhs_{label}")),
    }
}

fn mk_active_bounds<'a>(bounds: &'a [BoundInfo]) -> Vec<ActiveBound<'a>> {
    bounds
        .iter()
        .enumerate()
        .map(|(clause_idx, bound)| ActiveBound { clause_idx, bound })
        .collect()
}

fn expr_contains_const(expr: &Expr, target: &str) -> bool {
    match expr.strip_mdata().kind() {
        ExprKind::Const(name, _) => name.to_string() == target,
        ExprKind::App(fun, arg) => {
            expr_contains_const(fun, target) || expr_contains_const(arg, target)
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            expr_contains_const(ty, target) || expr_contains_const(body, target)
        }
        _ => false,
    }
}

#[test]
fn test_find_chain_order_supports_open_trail_that_revisits_start_term() {
    let terms = TermStore::new();
    let map = VariableMapping::new();
    let ctx = ReconstructionContext::new(&terms, &map, 0);

    let bounds = vec![
        mk_bound(5, 10, "five_to_x"),
        mk_bound(10, 5, "x_to_five"),
        mk_bound(5, 3, "five_to_three"),
    ];
    let active_bounds = mk_active_bounds(&bounds);

    let (chain, is_cycle) = ctx
        .find_chain_order(&active_bounds)
        .expect("open trail that revisits the start term should still chain");

    assert_eq!(chain, vec![0, 1, 2]);
    assert!(
        !is_cycle,
        "revisiting the start term is still an open trail"
    );
}

#[test]
fn test_find_chain_order_backtracks_across_branching_start() {
    let terms = TermStore::new();
    let map = VariableMapping::new();
    let ctx = ReconstructionContext::new(&terms, &map, 0);

    let bounds = vec![
        mk_bound(1, 3, "a_to_c"),
        mk_bound(1, 2, "a_to_b"),
        mk_bound(2, 1, "b_to_a"),
    ];
    let active_bounds = mk_active_bounds(&bounds);

    let (chain, is_cycle) = ctx
        .find_chain_order(&active_bounds)
        .expect("valid Euler trail should not fail because the first edge dead-ends");

    assert_eq!(chain, vec![1, 2, 0]);
    assert!(
        !is_cycle,
        "branching open trail should not be misclassified as a cycle"
    );
}

#[test]
fn test_try_two_bound_chain_reports_invariant_for_non_arithmetic_sort() {
    let terms = TermStore::new();
    let map = VariableMapping::new();
    let ctx = ReconstructionContext::new(&terms, &map, 0);

    let bounds = vec![
        BoundInfo {
            sort: Sort::Bool,
            op: CmpOp::Le,
            lhs_term: TermId(1),
            rhs_term: TermId(2),
            lhs_expr: mk_expr("bool_a"),
            rhs_expr: mk_expr("bool_b"),
        },
        BoundInfo {
            sort: Sort::Bool,
            op: CmpOp::Le,
            lhs_term: TermId(2),
            rhs_term: TermId(3),
            lhs_expr: mk_expr("bool_b"),
            rhs_expr: mk_expr("bool_c"),
        },
    ];
    let active_bounds = mk_active_bounds(&bounds);

    let err = ctx
        .try_two_bound_chain(&active_bounds, 2, 9)
        .expect_err("non-arithmetic chain sorts should fail closed at the invariant boundary");

    assert!(
        matches!(
            &err,
            ReconstructionError::TrustBoundary {
                step_index: 9,
                subsystem: "LRA",
                description
            } if description == "unexpected non-arithmetic sort Bool in LRA chain"
        ),
        "unexpected non-arithmetic chain sort should report the invariant boundary, got {err:?}"
    );
}

#[test]
fn test_try_two_bound_chain_reports_closeout_boundary_for_symbolic_int_chain() {
    let terms = TermStore::new();
    let map = VariableMapping::new();
    let ctx = ReconstructionContext::new(&terms, &map, 0);

    let bounds = vec![
        BoundInfo {
            sort: Sort::Int,
            op: CmpOp::Le,
            lhs_term: TermId(1),
            rhs_term: TermId(2),
            lhs_expr: mk_expr("int_x"),
            rhs_expr: mk_expr("int_b"),
        },
        BoundInfo {
            sort: Sort::Int,
            op: CmpOp::Le,
            lhs_term: TermId(2),
            rhs_term: TermId(3),
            lhs_expr: mk_expr("int_b"),
            rhs_expr: mk_expr("int_y"),
        },
    ];
    let active_bounds = mk_active_bounds(&bounds);

    let err = ctx
        .try_two_bound_chain(&active_bounds, 2, 11)
        .expect_err("symbolic Int chains should reach closeout trust-boundary");

    assert!(
        matches!(
            &err,
            ReconstructionError::TrustBoundary {
                step_index: 11,
                subsystem: "LRA",
                description
            } if description.contains("non-cyclic Le chain over Int has no kernel closing proof")
                && !description.contains("missing transitivity lemma")
        ),
        "symbolic Int chain should report closeout boundary rather than missing transitivity, got {err:?}"
    );
}

#[test]
fn test_build_chain_proof_reports_closeout_boundary_for_open_symbolic_chain() {
    let terms = TermStore::new();
    let map = VariableMapping::new();
    let ctx = ReconstructionContext::new(&terms, &map, 0);

    let int_x = mk_expr("int_x");
    let int_y = mk_expr("int_y");
    let int_z = mk_expr("int_z");
    let int_w = mk_expr("int_w");
    let bounds = vec![
        BoundInfo {
            sort: Sort::Int,
            op: CmpOp::Le,
            lhs_term: TermId(1),
            rhs_term: TermId(2),
            lhs_expr: int_x.clone(),
            rhs_expr: int_y.clone(),
        },
        BoundInfo {
            sort: Sort::Int,
            op: CmpOp::Le,
            lhs_term: TermId(2),
            rhs_term: TermId(3),
            lhs_expr: int_y.clone(),
            rhs_expr: int_z.clone(),
        },
        BoundInfo {
            sort: Sort::Int,
            op: CmpOp::Le,
            lhs_term: TermId(3),
            rhs_term: TermId(4),
            lhs_expr: int_z.clone(),
            rhs_expr: int_w.clone(),
        },
    ];
    let active_bounds = mk_active_bounds(&bounds);

    let err = ctx
        .build_chain_proof(&active_bounds, &Sort::Int, 3, &[0, 1, 2], false, 17)
        .expect_err("open symbolic Int chains should fail closed at closeout");

    assert!(
        matches!(
            &err,
            ReconstructionError::TrustBoundary {
                step_index: 17,
                subsystem: "LRA",
                description
            } if description.contains("non-cyclic Le chain over Int has no kernel closing proof")
        ),
        "open symbolic chain should report the stable closeout boundary, got {err:?}"
    );
}

#[test]
fn test_build_chain_proof_closes_strict_cycle_with_lt_irrefl() {
    let terms = TermStore::new();
    let map = VariableMapping::new();
    let ctx = ReconstructionContext::new(&terms, &map, 0);

    let int_x = mk_expr("int_x");
    let int_y = mk_expr("int_y");
    let int_z = mk_expr("int_z");
    let bounds = vec![
        BoundInfo {
            sort: Sort::Int,
            op: CmpOp::Le,
            lhs_term: TermId(1),
            rhs_term: TermId(2),
            lhs_expr: int_x.clone(),
            rhs_expr: int_y.clone(),
        },
        BoundInfo {
            sort: Sort::Int,
            op: CmpOp::Le,
            lhs_term: TermId(2),
            rhs_term: TermId(3),
            lhs_expr: int_y.clone(),
            rhs_expr: int_z.clone(),
        },
        BoundInfo {
            sort: Sort::Int,
            op: CmpOp::Lt,
            lhs_term: TermId(3),
            rhs_term: TermId(1),
            lhs_expr: int_z,
            rhs_expr: int_x,
        },
    ];
    let active_bounds = mk_active_bounds(&bounds);

    let false_proof = ctx
        .build_chain_proof(&active_bounds, &Sort::Int, 3, &[0, 1, 2], true, 19)
        .expect("strict Int cycles should reconstruct")
        .expect("strict Int cycles should close to False");

    assert!(
        expr_contains_const(&false_proof, "Int.lt_irrefl"),
        "strict cyclic chain should close via Int.lt_irrefl"
    );
}
